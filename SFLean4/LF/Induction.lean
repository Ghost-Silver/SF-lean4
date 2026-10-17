import SFLean4.LF.Basics

/-!
# 软件基础（第 1 卷）：逻辑基础
# Software Foundations Volume 1: Logical Foundations

## 第二章：归纳证明法 (Induction: Proof by Induction)

数学归纳法（Proof by Induction）是计算机科学与离散数学中最基础、最强大的推理工具之一。
在前一章《基础》（Basics）中，我们学习了如何通过简单的等式化简（`rfl`）以及有限情况讨论（`cases`）
来验证关于特定数据结构的性质。然而，当我们需要确立关于**无限集合**（例如全体自然数、任意长度的列表或语法树）
的通用性质时，有限的分情况讨论就会显得无能为力。

在本章中，我们将系统探讨：
1. **独立编译与模块化系统**：Lean 4 如何组织跨文件依赖与构建制品；
2. **皮亚诺自然数上的结构化数学归纳法**：在 Lean 4 中熟练运用 `induction` 策略；
3. **证明中的证明（Proofs Within Proofs）**：如何利用 `have` 策略在证明局部提出并确立辅助引理；
4. **形式化证明与非形式化证明的哲学**：人机互信、算法直觉与形式验证的鸿沟；
5. **代数性质的大规模归纳验证**：自然数加法与乘法的交换律、结合律与分配律；
6. **二进制与皮亚诺自然数的高级同态验证**：自增交换图与二进制规范化（Normalization）理论。

---
-/

/- ================================================================== -/
/-! ## 1. 独立编译与模块系统 (Separate Compilation) -/
/- ================================================================== -/

/-!
在正式展开本章的学习之前，我们需要导入上一章《基础》（`Basics`）中定义的所有核心类型与函数：
```lean
import SFLean4.LF.Basics
```

### 模块编译原理：Coq vs. Lean 4

在 Coq 原书中：
- `From LF Require Export Basics.` 指令要求系统必须能够在当前工作目录或逻辑库搜索路径中找到前一章编译好的二进制目标文件 `Basics.vo`。
  该 `.vo` 文件由源文件 `Basics.v` 经过 Coq 编译器 `coqc` 编译生成，完全类似于 C 语言源码经编译生成的 `.o` 目标文件，或 Java 编译生成的 `.class` 字节码。
- 为此，Coq 项目通常需要配置 `_CoqProject` 项目配置文件，其中声明如下映射行：
  ```
  -Q . LF
  ```
  这行配置指示编译器与 IDE（如 Proof General、CoqIDE 或 VSCoq）将当前目录 `.`（包含 `Basics.v` 与 `Induction.v`）映射到逻辑命名空间前缀 `LF`。
- 在构建方式上，Coq 提供了多种途径：
  - **IDE 构建**：Proof General 通过配置 `coq-compile-before-require` 为 `t` 实现自动预编译；CoqIDE 通过菜单栏“Compile Buffer”编译；VS Code 则通过终端调用构建脚本。
  - **命令行构建**：通过实用工具 `coq_makefile -f _CoqProject *.v -o Makefile` 自动生成 `Makefile`，随后使用 `make Basics.vo` 或直接 `make` 进行全量拓扑排序编译；亦可直接手动调用底层编译器 `coqc -Q . LF Basics.v`。

而在现代 **Lean 4** 中，这套流程被整合得更加流畅而现代：
- Lean 4 拥有一套一体化的现代化工程包管理器与构建系统——**Lake（Lean Make）**。
- 我们的项目根目录下包含项目清单文件 `lakefile.toml`：
  ```toml
  name = "SF-lean4"
  version = "0.1.0"
  defaultTargets = ["SFLean4"]

  [[lean_lib]]
  name = "SFLean4"
  ```
  它自动将 `SFLean4/` 目录组织为统一的顶层命名空间库，替代了 Coq 繁复的手动 `_CoqProject` 与 `Makefile` 生成流程。
- 当我们在终端执行：
  ```bash
  lake build
  ```
  Lake 会智能解析源码文件顶部的 `import` 语句，自动计算模块依赖图（DAG），并仅当被依赖的源文件发生变更时执行增量编译。
- Lake 编译生成的二进制制品存放在 `.lake/build/lib/` 目录下：
  - **`.olean` 文件（Object Lean）**：对应于 Coq 的 `.vo` 文件，包含经完全展开、形式化类型检验与去糖化处理后的抽象语法树与符号环境元数据；
  - **`.ilean` 文件（Interactive Lean）**：包含供语言服务器（LSP）使用的交互式索引，为编辑器提供丝滑的代码悬停、定理跳转、符号重构与实时 Infoview 目标渲染。

接下来，为了使我们在上一章中定义的皮亚诺减法 `minus` 以及二进制数据类型 `Bin` 的构造子能够在全局作用域中直接使用，
我们在此打开相应的命名空间：
-/

-- 打开上一章定义的皮亚诺截断减法
open NatPlayground2 (minus)

-- 打开二进制自然数类型及其构造子 Z, B0, B1
open Bin

/-!
### 常见故障排查指引（Troubleshooting Guide）

正如 Coq 原书中对初学者可能遇到的加载路径与版本冲突所作的详尽预警，
在 Lean 4 学习过程中，如果遇到符号找不到或加载异常，可依循如下对应策略排查：

1. **未找到编译器可执行程序（Command Not Found）**：
   - Coq 提示需确保 `coqc` 位于系统环境变量 `$PATH` 中；
   - 在 Lean 4 中，官方推荐使用版本管理工具 **`elan`**（类似于 Rust 的 `rustup`）。执行 `elan which lean` 或 `elan which lake` 即可确认当前生效的编译器路径。
2. **符号缺失与加载路径未对齐（Missing Identifiers / LoadPath）**：
   - Coq 用户常借助 `Print LoadPath.` 命令检查逻辑映射是否生效；
   - 在 Lean 4 中，如果在 Neovim 或 VS Code 中遇到 `unknown package 'SFLean4'` 或 `cannot find import 'SFLean4.LF.Basics'`，通常是因为尚未执行全局构建。只需在项目根目录运行 `lake build`，生成对应 `.olean` 缓存即可。
3. **前置模块修改导致的跨文件假设不一致（Inconsistent Assumptions）**：
   - 在 Coq 中，如果修改了 `Basics.v` 并重新编译，但未重新编译依赖它的 `Induction.v`，会看到报错：
     `Compiled library Induction makes inconsistent assumptions over library Basics`
     原书建议运行 `make clean && make` 彻底重构。
   - 在 Lean 4 中，Lake 会依据文件内容哈希自动跟踪变化。但如果编辑器后台的 LSP 语言服务未能即时感知底层制品变更，只需在项目根目录执行：
     ```bash
     lake clean && lake build
     ```
     并在 Neovim 中运行 `:LspRestart`（或在 VS Code 中执行 `Lean 4: Restart Server`），即可彻底恢复一致性！
4. **多版本冲突（Multiple Versions Installed）**：
   - 原书提醒若终端的 `coqc` 与编辑器内置的 Coq 版本不一致会导致奇怪的定位错误；
   - 在 Lean 4 中，项目根目录下的 `lean-toolchain` 文件精确锁定了项目所需的 Lean 4 版本（例如 `leanprover/lean4:v4.35.0`），`elan` 会在进入项目目录时自动无缝切换，彻底杜绝了版本分裂的隐患。
-/


/- ================================================================== -/
/-! ## 2. 通过数学归纳法进行证明 (Proof by Induction) -/
/- ================================================================== -/

/-!
在前一章中，我们证明了对任意自然数 $n$，$0 + n = n$ 恒成立。
在 Coq 中，自然数加法 `plus` 是对第一个参数进行结构化匹配的：
```coq
Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
```
因此，当第一个参数为 $0$ 时，无需对第二个参数做任何预设，直接化简（`simpl` 或 `reflexivity`）即可闭合目标。

但是，如果我们想要证明 $0$ 也是加法的**右中性元**（即对任意自然数 $n$，$n + 0 = n$），情况会如何呢？
-/

/-- 尝试一：我们能仅凭直接化简证明加法中性元吗？ -/
theorem add_0_r_firsttry (n : Nat) : n + 0 = n := by
  -- 在 Lean 4 原生标准库中，Nat.add 恰好是对第二个参数进行递归定义的：
  --   Nat.add n 0     = n
  --   Nat.add n (m+1) = (Nat.add n m) + 1
  -- 因此在 Lean 4 原生定义下，n + 0 = n 恰好直接被内核展开为恒等式！
  rfl

/-!
> [!NOTE] 核心洞察：Coq 与 Lean 4 原生加法的对偶镜像（Duality）
>
> 这是一个极为有趣的理论对照：
> 1. **Coq 的原生加法**：按**第一个参数**递归。
>    - $0 + n = n$ 是定义等价（Definitional Equality），一步 `reflexivity` 即可；
>    - $n + 0 = n$ **无法**通过直接化简解决，因为未知的符号变量 $n$ 挡在了匹配的最外层！
> 2. **Lean 4 的原生加法**：按**第二个参数**递归。
>    - $n + 0 = n$ 是定义等价，一步 `rfl` 即可；
>    - $0 + n = n$ **无法**通过直接化简解决，因为未知的符号变量 $n$ 同样挡在了递归分支上！

为了完全体会到原书在 Coq 中遇到的这种“化简无能为力”的困境，
让我们考察 Lean 4 中关于加法左零元的证明尝试：
-/

/-- 对偶困境演示：在 Lean 4 中，直接化简无法证明 0 + n = n！ -/
theorem add_0_l_firsttry (n : Nat) : 0 + n = n := by
  -- 尝试直接 rfl：
  -- rfl -- 报错：The left-hand side 0 + n is not definitionally equal to the right-hand side n
  sorry

/-!
既然直接化简行不通，那么利用上一章学到的 `cases` 策略对变量 $n$ 进行有限状态分类讨论，能解决问题吗？
在 Coq 原书中，作者首先展示了对加法右中性元进行分类讨论的尝试：
-/

/-- 尝试二：利用分类讨论策略 cases 考察右中性元 n + 0 = n。
    在 Lean 4 原生环境中，因为加法对第 2 个参数递归，所以两个分支均可直接闭合；
    而在 Coq 中，原作者在 n = S n' 分支卡在 S n' + 0 = S n' 处无法化简： -/
theorem add_0_r_secondtry (n : Nat) : n + 0 = n := by
  cases n with
  | zero =>
    -- n = 0 的情况：0 + 0 = 0，顺利通过！
    rfl
  | succ n' =>
    -- n = n' + 1 的情况：(n' + 1) + 0 = n' + 1
    rfl

/-- 对偶困境演示：在 Lean 4 中，尝试使用 cases 分类讨论证明左中性元 0 + n = n -/
theorem add_0_l_secondtry (n : Nat) : 0 + n = n := by
  cases n with
  | zero =>
    -- n = 0 的情况：0 + 0 = 0，顺利通过！
    rfl
  | succ n' =>
    -- n = n' + 1 的情况：目标变为 0 + (n' + 1) = n' + 1
    -- 展开 Nat.add 的第二参数递归定义，左侧化简为 (0 + n') + 1 = n' + 1
    -- 我们陷入了与 Coq 中完全一致的僵局：除非我们预先知道 0 + n' 的值，否则无法继续化简！
    sorry

/-!
显然，即使我们对 $n'$ 继续使用 `cases`，我们也只是把问题推向了更高阶的后继项（$n'' + 2$）。
因为自然数集合是无限的，沿有限分支逐一分类的策略永远无法跨越所有自然数。

### 皮亚诺自然数数学归纳原理 (The Principle of Mathematical Induction)

为了证明关于自然数、列表以及其它一切归纳定义的无限数据结构的普适性质，
我们需要借助更本质的推理原则：**数学归纳法（Mathematical Induction）**。

回顾初等数学中的自然数第一归纳原理：
假设 $P(n)$ 是一个关于自然数 $n$ 的命题，如果我们希望确立 $\forall n, P(n)$ 普遍成立，我们只需完成两件事：
1. **基础步骤（Base Case）**：证明 $P(0)$ 成立；
2. **归纳步骤（Inductive Step）**：对于任意的自然数 $n'$，**假设** $P(n')$ 已经成立（这一假设称为**归纳假设，Induction Hypothesis**），
   在此基础之上证明 $P(n' + 1)$ 亦必然成立；
3. **结论**：结合这两步，由良序性与皮亚诺公理可判定：对全体自然数 $n$，$P(n)$ 必定全部成立。

在形式化证明助手中，**`induction` 策略**正是这一数学思想的精确代码映射！
当我们在 Lean 4 中对某个自然数变量 $n$ 调用 `induction n with | zero => ... | succ n' ih => ...` 时，
目标会被自动分解为两个相互独立的子目标：
- 分支 `| zero =>`：目标中的 $n$ 被实例化替换为 $0$；
- 分支 `| succ n' ih =>`：目标中的 $n$ 被替换为后继 $n' + 1$，并且在当前的假设上下文（Hypothesis Context）中，
  系统会自动为我们注入名为 `ih` 的归纳假设：`ih : P n'`！

下面，让我们先完整确立 Lean 4 原生加法的左中性元定理（对偶于原书中的 `add_0_r`）：
-/

/-- 自然数加法左中性元定理：对任意自然数 n，0 + n = n 恒成立。
    （这是 Lean 4 原生加法中需要借助数学归纳法确立的基础中性元定理） -/
theorem add_0_l (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    -- 基步：0 + 0 = 0
    rfl
  | succ n' ih =>
    -- 归纳步：已知归纳假设 ih : 0 + n' = n'
    -- 当前证明目标：0 + (n' + 1) = n' + 1
    -- 根据 Nat.add 的第二参数递归定义，左侧可等价展开为 (0 + n') + 1
    show (0 + n') + 1 = n' + 1
    -- 利用归纳假设 ih 进行子项重写替换：
    rw [ih]

/-- 自然数加法右中性元定理：对任意自然数 n，n + 0 = n 恒成立。
    （在 Lean 4 原生加法中，这是第二参数的基步定义，可直接 rfl；
      同时亦可通过 induction 完整复刻原书证明结构） -/
theorem add_0_r (n : Nat) : n + 0 = n := by
  induction n with
  | zero =>
    -- 基步：0 + 0 = 0
    rfl
  | succ n' ih =>
    -- 归纳步：(n' + 1) + 0 = n' + 1
    rfl

/-!
### 归纳策略工作流剖析

让我们观察上面的 `induction` 语法结构：
1. 关键字 `induction n with` 指示对变量 `n` 进行结构归纳；
2. 竖线 `| zero =>` 捕获基础情形，无需引入新变量，因为 $0$ 是常数构造子；
3. 竖线 `| succ n' ih =>` 捕获后继归纳情形：
   - `n'` 代表脱去一层外壳后的前驱变量；
   - `ih` 是赋予归纳假设的显式名称（Inductive Hypothesis for `n'`）。
   如果不显式指定名称，Lean 也会自动生成内部变量名，但显式命名能极大地提升代码的可读性与重构安全性。

接下来，我们考察另一个必须使用数学归纳法才能证明的经典定理：
“任何自然数减去其自身结果恒等于零（`minus n n = 0`）”。
注意：这里使用的是我们在上一章中手动定义的截断减法 `NatPlayground2.minus`：
-/

/-- 自然数截断自减定理（课堂演练 / Worked in Class）：对任意自然数 n，minus n n = 0 恒成立。 -/
theorem minus_n_n (n : Nat) : minus n n = 0 := by
  induction n with
  | zero =>
    -- 基步：minus 0 0 = 0，命中 minus 的第 1 个匹配分支
    rfl
  | succ n' ih =>
    -- 归纳步：证明 minus (n' + 1) (n' + 1) = 0
    -- 展开 minus 的模式匹配：
    --   match (n' + 1), (m' + 1) with => minus n' m'
    -- 因此目标在定义层面上完全等价于 minus n' n' = 0！
    show minus n' n' = 0
    -- 直接应用归纳假设 ih 闭合证明：
    exact ih


/-!
> [!TIP] 策略小技巧：量词变量的自动引入
>
> 细心的读者可能会注意到：在 `theorem minus_n_n (n : Nat)` 中，
> 变量 `n` 作为参数已经在定理头部的括号中被声明并直接绑定到证明局部上下文中。
> 如果定理声明使用的是全称量词（如 `∀ n : Nat, ...`），
> `induction` 策略同样会自动将量词变量从目标中拉入上下文，无需在调用前繁琐地手动执行 `intro n`。
-/


/- ================================================================== -/
/-! ## 3. 基础归纳练习题 (Basic Induction Exercises) -/
/- ================================================================== -/

/-!
#### ⭐️⭐️ 练习题：basic_induction (2 星，标准，特别有用)

请使用数学归纳法完成下列自然数算术性质的证明。
在后续定理与更高级的章节中，这几个引理将作为最核心的重写规则被反复调用！

在证明加法交换律之前，我们先提示一个关于后继运算与加法交互的关键性质：
在 Coq 中加法对第 1 个参数递归，所以 `(n + 1) + m = (n + m) + 1` 是直接化简，而 `n + (m + 1) = (n + m) + 1`（即 `plus_n_Sm`）需要归纳；
在 Lean 4 中由于加法对第 2 个参数递归，`n + (m + 1) = (n + m) + 1`（`plus_n_Sm`）是直接恒等的，
而 `(n + 1) + m = (n + m) + 1`（即 `plus_Sn_m`）则需要对 $m$ 进行归纳！
为了兼顾原书定理名并确保后续证明的顺畅，我们在此完整提供这两组引理供大家证明和使用：
-/

/-- 自然数乘法右零元引理：对任意自然数 n，n * 0 = 0。 -/
theorem mul_0_r (n : Nat) : n * 0 = 0 := by
  sorry

/-- 自然数乘法左零元引理：对任意自然数 n，0 * n = 0。
    （在 Lean 4 原生环境中，此性质需要对 n 进行归纳证明） -/
theorem mul_0_l (n : Nat) : 0 * n = 0 := by
  sorry

/-- 加法右后继引理（plus_n_Sm）：(n + m) + 1 = n + (m + 1)。
    提示：在 Lean 4 原生加法定义下，等式两边在定义上完全一致，亦可通过归纳进行深入探究。 -/
theorem plus_n_Sm (n m : Nat) : (n + m) + 1 = n + (m + 1) := by
  sorry

/-- 加法左后继引理（plus_Sn_m）：(n + 1) + m = (n + m) + 1。
    提示：在 Lean 4 原生加法定义下，对参数 m 进行数学归纳法。 -/
theorem plus_Sn_m (n m : Nat) : (n + 1) + m = (n + m) + 1 := by
  sorry

/-- 自然数加法交换律（add_comm）：对任意自然数 n 与 m，n + m = m + n。
    提示：尝试对 n 进行归纳，基步可借助 add_0_l，归纳步可结合 plus_Sn_m 与归纳假设！ -/
theorem add_comm (n m : Nat) : n + m = m + n := by
  sorry

/-- 自然数加法结合律（add_assoc）：对任意自然数 n, m 与 p，n + (m + p) = (n + m) + p。
    提示：尝试对 p 进行归纳！观察 Lean 4 原生加法在右侧展开时的化简行为。 -/
theorem add_assoc (n m p : Nat) : n + (m + p) = (n + m) + p := by
  sorry

/-!
#### ⭐️⭐️ 练习题：double_plus (2 星，标准)

考察如下对自然数进行翻倍计算的递归函数 `double`：
-/

/-- 自然数翻倍函数：
    - double 0 = 0；
    - double (n' + 1) = double n' + 2。 -/
def double (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | n' + 1 => (double n') + 2

/-!
请使用数学归纳法证明关于 `double` 的简单性质：一个数翻倍等于自身与自身相加。
-/

theorem double_plus (n : Nat) : double n = n + n := by
  sorry

/-!
#### ⭐️⭐️ 练习题：eqb_refl (2 星，标准)

以下定理确立了作用在自然数上的**可计算布尔等式测试运算（`=?`）**与
命题逻辑宇宙中的**形式化命题等式（`=`）**之间的基础桥梁：
对任意自然数 $n$，$n =? n$ 的计算结果恒为布尔值 `true`。
-/

theorem eqb_refl (n : Nat) : (n =? n) = true := by
  sorry

/-!
#### ⭐️⭐️ 练习题：even_S (2 星，标准，选做)

在我们上一章对偶数判断函数 `even n` 的定义中，一个带来些许证明不便的特征是它在 `n' + 2` 处进行递归跳跃。
这使得通过常规的对 $n$ 单步归纳来证明 `even n` 的性质变得略微复杂。
以下引理给出了关于后继数奇偶性的等价刻画：后继数 `n + 1` 的偶数性恰好等于 `even n` 的逻辑否定。

为了方便处理布尔运算，我们在此声明布尔逻辑非、与、或运算及其基本对合引理：
-/

def negb (b : Bool) : Bool := !b
def andb (b1 b2 : Bool) : Bool := b1 && b2
def orb (b1 b2 : Bool) : Bool := b1 || b2

/-- 布尔非对合引理：对任意布尔值 b，两次取非等于其自身。 -/
theorem negb_involutive (b : Bool) : negb (negb b) = b := by
  cases b <;> rfl

/-- 后继奇偶性交替引理：even (n + 1) = negb (even n)。
    提示：对 n 进行数学归纳法。在归纳步中展开 even，结合归纳假设以及 negb_involutive！ -/
theorem even_S (n : Nat) : even (n + 1) = negb (even n) := by
  sorry


/- ================================================================== -/
/-! ## 4. 证明中的证明：局部引理与 have 策略 (Proofs Within Proofs) -/
/- ================================================================== -/

/-!
在 Coq 与 Lean 4 中，如同在传统非形式化数学中一样，大型复杂证明往往会被拆解为一系列定理序列，
后继证明通过定理名直接引用之前已经确立的结论。
然而，在实际证明过程中，我们经常会遇到一些极其琐碎、专业度极高且不具备全局复用价值的局部事实。
为每一个这样的小事实都命名并声明一个顶层全局定理不仅繁琐，而且会严重污染代码库的符号命名空间。

在 Coq 中，我们可以使用 `assert` 策略在证明执行到中途时，当场声明并证明一个局部子定理；
而在 **Lean 4** 中，对应的核心策略是 **`have` 策略**！

语法形式如下：
```lean
have h : <命题> := by
  <子证明步骤>
```
一旦闭合了 `have` 块，在随后的证明上下文中就会立即新增一条名为 `h` 的有效前提假设！

让我们通过一个具体的例子来观察其运作机制：
我们需要证明 $((n + 0 + 0) \times m) = n \times m$。
显而易见，只要先证明局部子事实 $n + 0 + 0 = n$，随后的证明即可一马平川：
-/

/-- 演示：使用 have 策略在证明内部提出并使用局部子定理 -/
theorem mult_0_plus' (n m : Nat) : (n + 0 + 0) * m = n * m := by
  -- 提出局部断言：声明 n + 0 + 0 = n，并赋予假设名 h
  have h : n + 0 + 0 = n := by
    -- 在这个缩进的代码块中，我们的证明目标是暂存的局部等式
    rw [add_0_r]
  -- 回到主证明目标，此时上下文已具备假设 h : n + 0 + 0 = n
  rw [h]

/-!
### 精准定位子项重写：解决 rewrite 的全局贪婪问题

`have` 策略的另一个不可替代的重大用途，是**精确控制重写的位置**。
当等式两端存在多个结构相同的子表达式时，朴素的 `rw` 策略往往不具备足够的上下文语义推断能力，
它通常只会自顶向下地匹配找到的**第一个（最外层）**匹配项。

例如，假设我们希望证明：
$$(n + m) + (p + q) = (m + n) + (p + q)$$
两边的唯一差异仅仅在于第一组加法操作数被交换了位置（由 $n + m$ 变为 $m + n$）。
直觉上，调用加法交换律 `add_comm` 似乎理应生效，然而直接调用 `rw [add_comm]` 会发生什么呢？
-/

/-- 尝试失败演示：未经限定的重写会盲目作用在错误的最外层操作符上 -/
theorem plus_rearrange_firsttry (n m p q : Nat) :
  (n + m) + (p + q) = (m + n) + (p + q) := by
  -- 尝试直接重写 add_comm：
  -- rw [add_comm]
  -- 此时 Lean 4 会把整个最外层的加法视为 A + B，从而将整个目标颠倒重写为：
  -- (p + q) + (n + m) = (m + n) + (p + q)
  -- 彻底偏离了我们的预期！
  sorry

/-!
为了让重写准确作用在我们希望它发生的地方，我们可以借助 `have` 针对该特定的子项提出一个精确的局部引理，
然后再用这个带有具体变量绑定的局部事实执行单点定向重写：
-/

/-- 成功演示：通过 have 策略精确定向重写复合子表达式 -/
theorem plus_rearrange (n m p q : Nat) :
  (n + m) + (p + q) = (m + n) + (p + q) := by
  -- 针对具体变量 n 与 m 提出局部交换断言：
  have h : n + m = m + n := by
    rw [add_comm]
  -- 此时由于 h 的类型严格锁定了两端操作数，rw [h] 仅会匹配 (n + m)！
  rw [h]


/- ================================================================== -/
/-! ## 5. 形式化证明 vs. 非形式化证明 (Formal vs. Informal Proof) -/
/- ================================================================== -/

/-!
> “**非形式化证明是算法，形式化证明是代码。**”
> （*Informal proofs are algorithms; formal proofs are code.*）

什么样的文本才称得上一篇成功的数学证明？
这一问题困扰了哲学家数千年。一个直观且实用的工程定义是：
**某个数学命题 $P$ 的证明，是一段书面（或口头）表述，它能够使读者在心智中无可辩驳地确信 $P$ 必然为真。**
换言之，**证明本质上是一种沟通行为（Act of Communication）。**

沟通行为必然取决于它的“读者”是谁：
1. **机器读者（如 Lean 4 / Coq）**：
   读者是一套严格遵循一阶逻辑与构造性类型论规则的计算机类型检查程序。
   此时形式化证明是一组精确指导编译器逐步进行环境变换与项构造的“代码脚本”。
   机器读者绝对严密、绝不容忍跳步、完全避免人类逻辑错觉，但形式化脚本本身对人类读者的心智认知并不友好。
2. **人类读者**：
   读者是同行数学家或计算机科学家，证明通常以自然语言（汉语或英语）撰写。
   由于不存在单一通用的全知读者，一个好的非形式化证明必须在高层思想直觉与具体技术推演之间维持微妙的平衡：
   - 过于冗长琐碎的证明会淹没核心思想脉络，让读者迷失在细节泥潭中；
   - 过度省略关键步骤的证明则可能隐藏逻辑漏洞，沦为虚妄的空想。

### 对比示例：自然数加法结合律的形式化与非形式化呈现

让我们来看同一段关于加法结合律证明的两种形式化书写方式，以及数学家对应的非形式化数学写作方式：
-/

-- 紧凑压缩写法：机器乐于接受，但对人类如同天书
theorem add_assoc' (n m p : Nat) : n + (m + p) = (n + m) + p := by
  induction p with | zero => rfl | succ p' ih => show (n + (m + p')) + 1 = ((n + m) + p') + 1; rw [ih]

-- 结构化注释写法：清晰标识子目标状态
theorem add_assoc'' (n m p : Nat) : n + (m + p) = (n + m) + p := by
  induction p with
  | zero =>
    -- p = 0 的基步情形
    rfl
  | succ p' ih =>
    -- p = p' + 1 的归纳步情形
    -- 根据 Nat.add 定义，两端最外层皆为 (+ 1)
    show (n + (m + p')) + 1 = ((n + m) + p') + 1
    rw [ih]

/-!
现在，让我们阅读一位严谨的数学家在教科书中所撰写的对应**非形式化证明**：

---
**定理**：对任意自然数 $n, m, p$，等式 $n + (m + p) = (n + m) + p$ 恒成立。

**证明**：对变量 $p$ 施加数学归纳法。
- **基步**：设 $p = 0$。根据自然数加法的右中性元定义，等式左侧为：
  $$n + (m + 0) = n + m$$
  右侧为：
  $$(n + m) + 0 = n + m$$
  两端完全相等，基步得证。
- **归纳步**：设 $p = p' + 1$，且归纳假设成立，即：
  $$n + (m + p') = (n + m) + p'$$
  我们现在需要证明：
  $$n + (m + (p' + 1)) = (n + m) + (p' + 1)$$
  根据自然数加法后继定义与引理 `plus_n_Sm`，左侧可展开重写为：
  $$n + ((m + p') + 1) = (n + (m + p')) + 1$$
  而右侧同样展开为：
  $$((n + m) + p') + 1$$
  此时将归纳假设代入左侧核心项，两边形式完全一致，归纳步得证。
综上所述，结合自然数归纳原理，该定理对全体 $n, m, p$ 恒成立。$\quad\blacksquare$
---

对比两者我们可以清晰发现：
形式化证明与非形式化证明在骨架上是高度对应的，但各有千秋：
形式化证明通过机器策略确保每一步绝对无误，而非形式化证明则在关键分岔点时刻向人类读者重申当前的局部状态与核心直觉。
在接下来的两道练习题中，请尝试扮演数学家的角色，将形式化策略转化为优美流畅的自然语言数学证明！
-/

/-!
#### ⭐️⭐️ 练习题：add_comm_informal (2 星，进阶，特别有用)

请将你此前完成的加法交换律 `add_comm` 的证明，改写为一段清晰、严谨的自然语言非形式化证明。
请直接在下方注释块中书写你的证明文本：
-/

/-
定理：加法满足交换律，即对任意自然数 n 与 m，n + m = m + n 恒成立。

证明：
  [请在此处用中文详细撰写你的归纳证明过程：
   明确指出对哪个变量进行归纳、基步的状态如何闭合、
   归纳步的假设是什么、如何借助辅助引理使两端达成一致]
-/

def manual_grade_for_add_comm_informal : Option (Nat × String) := none

/-!
#### ⭐️⭐️ 练习题：eqb_refl_informal (2 星，标准，选做)

请参考上文加法结合律的范例，为定理 `eqb_refl`（即 $\forall n : \text{Nat}, (n =? n) = \text{true}$）
撰写一段规范的自然语言数学证明。切记：不要只是把 Lean 策略直译成英文或代码指令，
而要以面向数学读者的视角阐述数据结构的归纳拆解与计算展开过程！
-/

/-
定理：对任意自然数 n，(n =? n) = true 恒成立。

证明：
  [请在此处撰写你的自然语言证明]
-/

def manual_grade_for_eqb_refl_informal : Option (Nat × String) := none


/- ================================================================== -/
/-! ## 6. 更多练习题 (More Exercises) -/
/- ================================================================== -/

/-!
#### ⭐️⭐️⭐️ 练习题：mul_comm (3 星，标准，特别有用)

首先，使用 `have` 策略（或直接传递重写参数）证明辅助定理 `add_shuffle3`。
注意：本题不需要使用归纳法，只需组合利用已有的加法结合律与交换律即可！
-/

theorem add_shuffle3 (n m p : Nat) : n + (m + p) = m + (n + p) := by
  sorry

/-!
现在，请证明自然数乘法的交换律：
$$\forall n, m : \text{Nat}, n \times m = m \times n$$
提示：
在进行归纳证明时，你可能需要用到类似于 $n \times (m + 1) = n + n \times m$ 的后继乘法展开引理。
观察目标，思考对哪个参数进行归纳更加自然，并在卡住时适时抽取并确立局部引理！
-/

theorem mul_comm (n m : Nat) : n * m = m * n := by
  sorry

/-!
#### ⭐️⭐️ 练习题：plus_leb_compat_l (2 星，标准，选做)

在逻辑推理中，如果有一个形如 `h : P → a = b` 的条件假设，那么对其应用重写不仅会完成替换，
还会将前置条件 `P` 作为新的待证分支引入。
请在以下练习中对 $p$ 实施数学归纳法，确立小于等于关系关于加法的左单调性：
$$n \le m \implies (p + n) \le (p + m)$$
-/

#check leb

theorem plus_leb_compat_l (n m p : Nat) (h : (n <=? m) = true) :
  ((p + n) <=? (p + m)) = true := by
  sorry


/-!
#### ⭐️⭐️⭐️ 练习题：more_exercises (3 星，标准，选做)

拿起一张草稿纸。对于下列每一个定理，首先在动笔编写代码之前深入思考并预测：
- (a) 它是否仅凭定义化简与子项重写（`rfl`, `rw`）即可直接获证？
- (b) 它是否需要进行有限情况分类（`cases`）？
- (c) 它是否必须引入结构化数学归纳法（`induction`）？

在脑海中完成推演后，再在 Lean 4 中完成证明：
-/

/-- 自然数小于等于关系的自反性 -/
theorem leb_refl (n : Nat) : (n <=? n) = true := by
  sorry

/-- 零与后继数判等为假 -/
theorem zero_neqb_S (n : Nat) : (0 =? (n + 1)) = false := by
  sorry

/-- 布尔逻辑与的右假零元 -/
theorem andb_false_r (b : Bool) : andb b false = false := by
  sorry

/-- 后继数与零判等为假 -/
theorem S_neqb_0 (n : Nat) : ((n + 1) =? 0) = false := by
  sorry

/-- 自然数乘法左一元恒等 -/
theorem mult_1_l (n : Nat) : 1 * n = n := by
  sorry

/-- 三布尔变量特定逻辑或永真规范 -/
theorem all3_spec (b c : Bool) :
  orb (andb b c) (orb (negb b) (negb c)) = true := by
  sorry

/-- 自然数乘法对加法的右分配律：(n + m) * p = (n * p) + (m * p) -/
theorem mult_plus_distr_r (n m p : Nat) :
  (n + m) * p = (n * p) + (m * p) := by
  sorry

/-- 自然数乘法结合律：n * (m * p) = (n * m) * p -/
theorem mult_assoc (n m p : Nat) :
  n * (m * p) = (n * m) * p := by
  sorry

/-!
#### ⭐️⭐️ 练习题：add_shuffle3' (2 星，标准，选做)

在 Coq 中，原书介绍了 `replace (t) with (u)` 策略，用于直接在目标中将子项表达式 `t` 强制替换为 `u`，
并衍生出一个附加子目标 `t = u` 供用户证明。

而在 **Lean 4** 中，我们拥有多种更自然、更精准的手段来实现同样的目的：
1. **显式传参重写**：在 Lean 4 中，定理可以像函数一样显式接受参数。例如 `rw [add_comm n m]` 会精准且仅替换表达式 `n + m`，而绝不会误触其它加法项！
2. **定向转换模式（`conv` 模式）**：通过 `conv => lhs; arg 1; ...` 直接“步入”复杂 AST 表达式的特定子树内部执行微操；
3. **局部定义替换**：利用 `have` 配合定向匹配。

请重新证明 `add_shuffle3'`，体验 Lean 4 中精准定向重写的威力：
-/

theorem add_shuffle3' (n m p : Nat) :
  n + (m + p) = m + (n + p) := by
  sorry


/- ================================================================== -/
/-! ## 7. 自然数与二进制之间的相互转换 (Nat to Bin and Back to Nat) -/
/- ================================================================== -/

/-!
回顾我们在上一章《基础》（`Basics`）末尾定义的二进制自然数表示类型 `Bin`：
```lean
inductive Bin where
  | Z
  | B0 (n : Bin)
  | B1 (n : Bin)
```
以及自增函数 `incr` 与十进制求值函数 `bin_to_nat`：
- `Z` 代表数值 $0$；
- `B0 n` 代表将二进制数左移一位，即数值 $2 \times n$；
- `B1 n` 代表将二进制数左移一位并置最低位为 1，即数值 $2 \times n + 1$。

在上一章中，我们通过若干单元测试验证了这两个函数的计算结果，
但单元测试只能检验有限个孤立的测试用例。现在，我们将使用归纳证明法确立其普遍的数学正确性！
-/

/-!
#### ⭐️⭐️⭐️ 练习题：binary_commute (3 星，标准，特别有用)

请证明如下交换图（Commutative Diagram）是严格成立的：

```
                        incr
          Bin ------------------------> Bin
           |                             |
bin_to_nat |                             | bin_to_nat
           |                             |
           v                             v
          Nat ------------------------> Nat
                      (· + 1)
```

换言之：**对一个二进制数先进行自增运算再转换为自然数，
其结果严格等于先将其转换为自然数再在皮亚诺自然数上加一！**
-/

theorem bin_to_nat_pres_incr (b : Bin) :
  bin_to_nat (incr b) = 1 + bin_to_nat b := by
  sorry

/-!
#### ⭐️⭐️⭐️ 练习题：nat_bin_nat (3 星，标准)

现在，请编写一个将皮亚诺自然数编码转换为二进制表示的函数 `nat_to_bin`：
- $0$ 对应 `Bin.Z`；
- $n' + 1$ 对应对前驱转换结果的自增 `incr`。
-/

/-- 将皮亚诺十进制自然数转换为二进制数 -/
def nat_to_bin (n : Nat) : Bin :=
  match n with
  | 0      => Z
  | n' + 1 => incr (nat_to_bin n')

/-!
请证明：如果我们从任意自然数 $n$ 出发，将其转换为二进制数 `nat_to_bin n`，
再将结果转回自然数 `bin_to_nat`，我们必定能分毫不差地取回最初的自然数 $n$！

提示：充分借助上一题刚刚得证的 `bin_to_nat_pres_incr` 作为辅助引理，
整个归纳证明过程将极为顺畅！
-/

theorem nat_bin_nat (n : Nat) : bin_to_nat (nat_to_bin n) = n := by
  sorry


/- ================================================================== -/
/-! ## 8. 进阶讨论：二进制到自然数再转回二进制 (Bin to Nat and Back to Bin - Advanced) -/
/- ================================================================== -/

/-!
既然自然数到二进制再转回自然数（$\text{Nat} \to \text{Bin} \to \text{Nat}$）是恒等映射，
那么反向的转换——从二进制出发，转为自然数后再转回二进制（$\text{Bin} \to \text{Nat} \to \text{Bin}$）——也是恒等的吗？

答案是：**该逆向命题在一般情况下并不成立！**
在 Coq 原书中，作者首先陈述了该猜想，并在发现其不成立后主动放弃证明（`Abort`）：
```coq
Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.
```
在 Lean 4 中，我们可以直接通过构造一个具体的反例（例如带有高位前导零的 `B0 Z`），
形式化确立该普遍命题的严格逻辑否定：
-/

/-- 逆向恒等定理的否定（对应 Coq 中因无法成立而 Abort 的 bin_nat_bin_fails 定理）：
    并非所有二进制数在经历转换后再转回都能取回其原始形态！ -/
theorem bin_nat_bin_fails : ¬ (∀ b : Bin, nat_to_bin (bin_to_nat b) = b) := by
  intro h
  have h_counter := h (B0 Z)
  -- bin_to_nat (B0 Z) 求值为 0
  -- nat_to_bin 0 求值为 Z
  -- 假设 h 意味着 Z = B0 Z，这在归纳类型的构造子互异性（NoConfusion）下是不可能的！
  nomatch h_counter

/-- 逆向恒等失败的具体数值反例 -/
theorem bin_nat_bin_fails_example : nat_to_bin (bin_to_nat (B0 Z)) ≠ B0 Z := by
  intro h
  nomatch h

/-!
### 为什么逆向转换会失效？（思考题）

该定理之所以无法成立，是因为存在某些二进制数，经过转换后我们无法恢复其“最初”的形式，
而是得到了一个“等价”的二进制数（原书在此特意未给出等价的精确定义，留给读者深思）。

请在下方的注释块中，解释为什么该逆向转换定理无法成立。
你的解释虽然不会被自动评分，但深入理解这一点对后续内容的展开至关重要。
如果你感到困惑，不妨思考一下：如果 `double_bin` 的实现未能满足 `double_bin_zero`（例如返回了 `B0 Z`），
但在其它方面看似正确，会带来怎样的后果？
-/

/- 请在此处写下你的思考与解释（例如关于前导零与同态代表元的讨论）：
   [在此处输入你的解释]
-/

/-!
为了解决这一问题，我们需要引入**规范化（Normalization）**的概念：
在所有等价的二进制表示中，选出那个不包含任何冗余高位零的最简形式。
随后我们即可证明：$\text{Bin} \to \text{Nat} \to \text{Bin}$ 的结果恰好等于原始二进制数的**规范化结果**！

为了循序渐进地构建这一宏伟定理，我们先确立若干关键辅助函数与性质：
-/

/-!
#### ⭐️⭐️ 练习题：double_bin (2 星，进阶)

首先证明关于自然数 `double` 函数关于后继的一个简单步进性质：
-/

theorem double_incr (n : Nat) : double (n + 1) = (double n) + 2 := by
  sorry

/-!
现在，为二进制数 `Bin` 定义对应的翻倍函数 `double_bin`：
- 对 $0$ 翻倍依然是 $0$（注意：必须返回最简形式 `Z`，绝不能返回带有冗余前导零的 `B0 Z`！）；
- 对非零二进制数 $n$ 翻倍，只需在末尾追加一个零位 `B0 n`。
-/

/-- 二进制翻倍函数：将二进制数左移一位，保持零的最简规范性 -/
def double_bin (b : Bin) : Bin :=
  match b with
  | Z => Z
  | n => B0 n

/-- 检验你的函数对零进行翻倍时确实保持规范化 -/
theorem double_bin_zero : double_bin Bin.Z = Bin.Z := by
  rfl

/-!
接下来，请证明对应于 `double_incr` 的二进制自增交换性质：
对自增后的二进制数翻倍，等于对翻倍后的二进制数连续自增两次！
-/

theorem double_incr_bin (b : Bin) :
  double_bin (incr b) = incr (incr (double_bin b)) := by
  sorry

/-!
#### ⭐️⭐️⭐️⭐️ 练习题：bin_nat_bin (4 星，进阶)

现在，请定义规范化函数 `normalize`。
要求：保持结构尽可能极简，遍历二进制结构的每一位，利用 `double_bin` 来消除多余的前导零，
而不要尝试“超前偷看（Look Ahead）”未来的高位比特：
-/

/-- 二进制规范化函数：去除高位无意义的前导零，收敛至唯一的规范代表元 -/
def normalize (b : Bin) : Bin :=
  match b with
  | Z     => Z
  | B0 b' => double_bin (normalize b')
  | B1 b' => incr (double_bin (normalize b'))

-- 单元测试集：验证不同阶数的前导零全部被正确消除为唯一的规范元 Z
theorem test_normalize0_1 : normalize Z = Z := by rfl
theorem test_normalize0_2 : normalize (B0 Z) = Z := by rfl
theorem test_normalize0_3 : normalize (B0 (B0 Z)) = Z := by rfl
theorem test_normalize0_4 : normalize (B0 (B0 (B0 Z))) = Z := by rfl

-- 单元测试集：验证非零数值在规范化后数值语义保持完全守恒
theorem test_normalize1 : bin_to_nat (normalize (B1 Z)) = 1 := by rfl
theorem test_normalize2 : bin_to_nat (normalize (B0 (B1 Z))) = 2 := by rfl
theorem test_normalize3 : bin_to_nat (normalize (B1 (B1 Z))) = 3 := by rfl
theorem test_normalize4 : bin_to_nat (normalize (B0 (B0 (B1 Z)))) = 4 := by rfl

/-!
在攻克最终的主定理之前，我们需要先确立一座连接自然数翻倍与二进制翻倍的桥梁引理：
对翻倍后的自然数转换为二进制，等于将自然数先转为二进制再应用 `double_bin`！

提示：尝试对主结论展开归纳证明，观察在哪个归纳分支会卡住；
思考是否可以抽取出一条前置引理（可能自身亦需归纳证明）来驱动主证明向前推进。
原书中针对 `B0` 情形设计了一条结合 `double_incr_bin` 的引理，针对 `B1` 分支亦有对应对称结构。
-/

theorem nat_to_bin_double (n : Nat) :
  nat_to_bin (double n) = double_bin (nat_to_bin n) := by
  sorry

/-!
终于，我们来到了本章最具深度的巅峰主定理：
**对任意二进制数 $b$，将其转为自然数后再编码回二进制数，
其结果必然严格等于该二进制数的规范化表示 `normalize b`！**

提示：对 $b$ 进行结构归纳讨论（`Z`, `B0`, `B1`）。
在归纳步中分别借助 `double_plus`, `nat_to_bin_double` 以及归纳假设！
-/

theorem bin_nat_bin (b : Bin) :
  nat_to_bin (bin_to_nat b) = normalize b := by
  sorry



/- ================================================================== -/
/-! ## 9. 章节总结与测试指引 (Chapter Summary & Testing Guide) -/
/- ================================================================== -/

/-!
恭喜你！至此，我们已经完整建立了《软件基础》第二章《归纳证明法》（Induction）的全部理论与形式化框架！

### 本章核心知识回顾：
1. **模块系统与独立编译**：
   - 理解了 Lake 的依赖驱动构建模型，掌握了 `.olean` 与 `.ilean` 的编译原理；
   - 掌握了如何在多文件之间通过 `import` 与命名空间复用类型与引理。
2. **结构化数学归纳法（`induction` 策略）**：
   - 深刻理解了有限分类 `cases` 与无限结构推演 `induction` 的本质区别；
   - 领会了 Coq 与 Lean 4 原生加法递归方向的对偶镜像关系；
   - 掌握了在 Lean 4 中为归纳假设精准命名的规范书写模式。
3. **证明中的证明（`have` 策略）**：
   - 掌握了在证明执行中途当场提出并证明局部引理的模式；
   - 解决了朴素 `rw` 盲目作用在最外层操作符上的定位难题。
4. **形式化 vs. 非形式化证明的哲学**：
   - 领悟了代码级别机器严格检验与面向人类心智交流的高层算法直觉的互补统一。
5. **数制表示的代数同态与规范化**：
   - 严格形式化检验了二进制与皮亚诺自然数之间的交换图；
   - 探究了冗余表示、前导零、同态映射与规范化（Normalization）理论。

---

### 自动化构建与检验：

在终端中执行：
```bash
lake build
```
若提示构建成功（伴随预期的 `declaration uses 'sorry'` 警告），
说明整章的所有类型签名、引理表述与单元测试均已完美对接。
现在，请在 Neovim 中打开此文件，逐一攻克所有的 `sorry` 练习题吧！
-/
