---
title: "Extraction: 代码抽取与编译执行"
---

```lean
import SFLean4.LF.Maps
import SFLean4.LF.Imp
import SFLean4.LF.ImpParser
import SFLean4.LF.ImpCEvalFun

set_option linter.defProp false
set_option linter.ambiguousOpen false
set_option linter.unusedVariables false
```

# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)

## 第十五章：代码抽取与 AOT 编译 (Extraction: Extracting Code in Coq vs. Native Compilation in Lean 4)

在形式化验证的世界中，我们花费大量心血证明了软件的数学性质（例如解释器的正确性、编译器的语义保持性）。
然而，形式化规约与证明最终需要转化为**可在物理硬件上高效执行的高性能二进制程序**。

在传统的 Coq 工作流中：
- Coq 本身只是一个逻辑系统，其核心（Kernel）并不直接生成机器码；
- 用户必须通过 **代码抽取（Extraction）** 机制，将 Gallina 形式化定义翻译为目标语言（主要是 OCaml，部分支持 Haskell / Scheme）；
- 抽取过程中擦除所有的证明凭据（`Prop` 项），并可配置将 Coq 的皮亚诺自然数 `nat` 映射到 OCaml 的原生机器字长整数 `int`；
- 随后调用 OCaml 编译器（`ocamlc` / `ocamlopt`）将生成的 `.ml` 文件连同手工编写的驱动程序编译为可执行文件。

而在现代 **Lean 4** 体系中，设计理念发生了一场革命性的飞跃：
- **定理证明器即全功能系统编程语言**：Lean 4 不再依赖外部抽取机制！
- **自举编译器与直接 AOT 编译**：通过 Lean 编译器流水线（Elaborator → Kernel 检查 → LCNF 规范形式 → C 语言生成 → Clang/GCC 编译），Lean 4 直接生成极高运行性能的本机可执行文件；
- **自动证明擦除 (Proof Erasure)**：所有宇宙属于 `Prop` 的类型与证明项在代码生成阶段被静态安全擦除，计算运行时具有完全零开销；
- **确定性引用计数优化 (RC & Borrowing)**：依靠强大的 Reset/Reuse 内存优化，支持就地可变更新（In-place mutation），兼具纯函数式语义与命令式执行效率。

在本章中，我们将系统对照 Coq 的代码抽取技术与 Lean 4 的本机编译机制，并基于前两章实现的词法/语法解析器与步数索引求值器，完整构建 Imp 语言的端到端可执行解释器驱动。

## 基础代码抽取与编译器流水线

```lean
namespace Extraction

open Maps
open Imp
open ImpParser
open ImpCEvalFun
```

### 1. 抽取机制对比：从 Coq 到 Lean 4

在 Coq 中，抽取一个函数的语法如下：
```coq
From Coq Require Extraction.
Extraction Language OCaml.
From LF Require Import ImpCEvalFun.
Extraction "imp1.ml" ceval_step.
```
Coq 会生成一个 `imp1.ml` 文件，其中包含 `ceval_step` 及其递归依赖的定义。

在 Lean 4 中，每一个计算性定义（以 `def` 声明且类型不在 `Prop` 中）天然就是 Lean 运行时的一等执行单元。
无需任何外部抽取命令，`ceval_step` 即可通过 `#eval` 在 VM 中直接解释执行，
或通过 Lake 编译为独立的 C 目标文件与本地机器代码。

## 目标类型映射与 FFI (Foreign Function Interface)

### 2. 原生数据类型映射与证明擦除

在 Coq 中，皮亚诺归纳自然数 `nat` 在运行时具有较重的开销。
Coq 允许使用 `Extract Inductive` 和 `Extract Constant` 建立与宿主语言数据类型的信任桥梁：
```coq
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".
Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
```
这种外部映射要求程序员自己保证语义的一致性。

而在 Lean 4 中：
- 标准库的自然数 `Nat` 在底层使用了 GMP 大数库优化：小整数直接编码为未装箱（Unboxed）的字长标量（Tagged Pointers），极大降低了运算开销；
- 原生定长整数（`UInt8`, `UInt32`, `UInt64`, `USize`）直接编译为 CPU 原生整数指令；
- 支持安全的 `@[extern "c_function"]` C-FFI 接口，能够双向无缝桥接 C/C++ 生态。

## 完整端到端 Imp 解释器驱动 (Imp Driver)

### 3. 可执行驱动程序实现

我们实现对应原版 `impdriver.ml` 的解释器运行驱动：
1. 接收 Imp 源代码字符串；
2. 调用 `ImpParser.parse` 转换为命令抽象语法树 `com`；
3. 设定计算步数预算 `fuel = 1000`，调用 `ImpCEvalFun.ceval_step` 进行步数索引求值；
4. 打印最终内存中常用变量（`w`, `x`, `y`, `z`）的状态。

```lean
/-- Imp 解释器通用运行入口函数 -/
def run_imp (s : String) : IO Unit := do
  IO.println s!"\nProgram: {s}"
  match parse s with
  | optionE.NoneE err =>
      IO.println s!"Syntax error: {err}"
  | optionE.SomeE c =>
      let fuel := 1000
      match ceval_step empty_st c fuel with
      | none =>
          IO.println s!"Still running after {fuel} steps"
      | some res =>
          IO.println s!"Result: [w={res "w"} x={res "x"} y={res "y"} z={res "z"}]"
```

### 4. 示例程序的实际执行验证

## 总结与展望 (Discussion & Going Further)

```lean
/- 测试用例 1：简单顺序赋值 -/
#eval run_imp "x:=1 ; y:=2"

/- 测试用例 2：语法错误检测（非合法命令） -/
#eval run_imp "true"

/- 测试用例 3：空操作 `skip` -/
#eval run_imp "skip"

/- 测试用例 4：空操作序列 -/
#eval run_imp "skip;skip"

/- 测试用例 5：死循环（在 1000 步预算耗尽后安全中止，不导致系统崩溃） -/
#eval run_imp "while true do skip end"

/- 测试用例 6：单一变量赋值 -/
#eval run_imp "x:=3"

/- 测试用例 7：条件死循环 -/
#eval run_imp "x:=3; while 0<=x do skip end"

/- 测试用例 8：阶乘或倒计数累加程序 -/
#eval run_imp "x:=3; while 1<=x do y:=y+1; x:=x-1 end"
```

### 5. 已验证软件工程的闭环

回顾我们从 [Imp](file:///Users/ghostface/LuoJin/SF-lean4/SFLean4/LF/Imp.lean)、[ImpParser](file:///Users/ghostface/LuoJin/SF-lean4/SFLean4/LF/ImpParser.lean) 到 [ImpCEvalFun](file:///Users/ghostface/LuoJin/SF-lean4/SFLean4/LF/ImpCEvalFun.lean) 的完整探索：
1. 我们定义了抽象语法 `aexp`, `bexp`, `com`；
2. 我们定义了大步操作语义关系 `ceval`，并在逻辑上严格证明了它的性质（确定性）；
3. 我们编写了高效的步数索引求值函数 `ceval_step`，并形式化证明了它与大步语义的完全等价；
4. 我们编写了纯函数式的递归下降解析器 `parse`，并实现了交互式执行环境。

这一连串形式化工作使我们得到了一个**经由数学严格验证的已认证解释器（Certified Interpreter）**。
在后续的《程序语言基础》(PLF) 与《函数式算法验证》(VFA) 中，我们将进一步探讨经过形式化验证的优化编译器与高级类型系统的构建！

```lean
end Extraction
```
