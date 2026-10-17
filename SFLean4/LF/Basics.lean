/-
  ======================================================================
  《软件基础》(Software Foundations) 卷一：逻辑基础 (Logical Foundations)
  第一章：基础 (Basics: Functional Programming in Lean 4)
  ======================================================================

  原著：Benjamin C. Pierce et al.
  形式化迁移与中文精译：针对 Lean 4 现代依赖类型论体系严格重构
-/

/-!
# 导言 (Introduction)

函数式编程（Functional Programming）的风格根植于简单而自然的日常数学直觉：
如果一个过程或方法**没有任何副作用（Side Effects）**，那么在不考虑计算效率的前提下，
我们理解它所需要的一切，就只是弄清楚它是如何将输入映射为输出的——换言之，
我们可以将其单纯地视为一种**计算纯数学函数**的具体实现。
这便是“函数式编程”一词中“函数”的第一层含义。程序与纯粹数学对象之间的这种直接联系，
既为形式化的**程序正确性证明**提供了基石，也为严谨推演程序的运行时行为赋予了坚实的理论支撑。

函数式编程中“函数”的第二层含义在于：它强调将函数视作**一等公民（First-class Values）**——
即函数本身就是数据，可以作为参数传递给其他函数、作为计算结果返回、或者直接存放在复合数据结构之中。
将函数等同于数据的这一思想，孕育了大量极其通用且表达力强大的编程范式与设计模式。

此外，函数式语言的其他常见特性还包括：
- **代数数据类型（Algebraic Data Types, ADT）** 与 **模式匹配（Pattern Matching）**：
  使构造与操纵复杂丰富的数据结构变得轻而易举；
- **多态类型系统（Polymorphic Type Systems）**：为高度抽象与代码复用提供类型安全的保障。

原版《软件基础》使用 Coq 证明助手的核心函数式语言 Gallina；
而在本项目中，我们使用现代依赖类型论的先锋语言——**Lean 4**。
Lean 4 既是一个顶尖的交互式定理证明器，同时也是一门现代、强类型、自带高效垃圾回收与无开销抽象的系统级通用编程语言。

本章的前半部分将系统介绍 Lean 4 原生核心函数式编程语言的基本要素；
后半部分将引入用于形式化证明程序数学性质的基础策略（Tactics）。
-/

/-!
# 工程与作业提交指引 (Homework Submission Guidelines)

如果你在高校课程或自学体系中使用《软件基础》，请注意以下工程与验证规范：

- **不要修改练习题的名称**：否则自动化测试脚本和批改工具将无法定位你的解答。
- **不要删除练习题**：如果你跳过某道习题（例如选做题，或者暂时未能解出），可以在定义或证明体中保留占位关键字 `sorry`（这在 Lean 4 中等价于 Coq 的 `Admitted`，代表承认该步骤尚未完成，允许下游代码继续编译）。
- **允许引入辅助定义**：在你的解答中，完全可以根据需要定义额外的辅助函数或引理（Lemma），请将它们放置在待解决的目标定理之前。
- **构建与测试验证**：在终端进入项目根目录，运行 `lake build` 即可编译并校验全部证明；在 Neovim / VS Code 中打开本文件时，可随时通过右侧的 Infoview 即时检查待证目标（Goal）与假设上下文。
-/

/- ================================================================== -/
/-! ## 1. 数据与函数 (Data and Functions) -/
/- ================================================================== -/

/-!
### 1.1 枚举类型 (Enumerated Types)

Lean 4 与 Coq 一样，其最底层的内建原子特性集是**极其微小精简**的。
例如，系统内核并没有内置布尔型、整型、字符串等传统原子类型，而是提供了一套高度统一且强力的底层机制——
**从零开始定义全新的数据类型**，并让上述所有我们熟悉的常用类型作为其具体实例。

自然地，Lean 4 官方分发包中自带了完备的标准库，提供了布尔值、数值以及列表、哈希表等众多经典数据结构的定义。
但这些库定义并无任何魔法或编译器特权。为了直观展现这一点，在本书中，我们将**从最原始的定义开始亲手重建（几乎）所有核心概念**，而不是直接向标准库索取。
-/

/-!
### 1.2 一周的日子 (Days of the Week)

为了阐述这种类型定义机制是如何工作的，让我们从一个极简的例子启程。
下面的声明向 Lean 4 表明：我们正在定义一个全新的数据值集合——即一个**类型（Type）**：
-/

/-- 定义表示星期几的枚举类型 `Day`。
    原版 Coq 中写作 `Inductive day : Type := monday | ...`。
    在 Lean 4 中，通过 `deriving Repr, DecidableEq` 可自动派生文本打印与等式可判定性。 -/
inductive Day where
  | monday    : Day
  | tuesday   : Day
  | wednesday : Day
  | thursday  : Day
  | friday    : Day
  | saturday  : Day
  | sunday    : Day
  deriving Repr, DecidableEq

/-!
这个新类型被命名为 `Day`，它的成员（成员也称为**构造子 Constructors**）分别是
`.monday`、`.tuesday` 等。

有了 `Day` 类型之后，我们就可以编写操作日期的函数了：
-/

/-- 计算下一个工作日：周一至周四顺延一天；周五、周六、周日之后都是周一。 -/
def next_working_day (d : Day) : Day :=
  match d with
  | .monday    => .tuesday
  | .tuesday   => .wednesday
  | .wednesday => .thursday
  | .thursday  => .friday
  | .friday    => .monday
  | .saturday  => .monday
  | .sunday    => .monday

/-!
请注意：在上面的函数定义中，参数类型 `(d : Day)` 和返回类型 `: Day` 均显式声明了出来。
与大多数高级函数式编程语言一样，当未显式给出时，Lean 4 通常能够借助**类型推导（Type Inference）**自动推断出它们；
但在教学与形式化规范中，显式注明类型能够显著提升代码的可读性与自解释性。
-/

/-!
### 1.3 示例与计算求值 (Evaluating Expressions)

定义好函数之后，我们需要验证它在一系列具体示例上的表现是否符合预期。
在证明助手中，检验一个函数通常有以下三种层次的方法：

**第一种方法**：使用交互式计算命令求值。
在 Coq 中使用 `Compute` 命令；在 Lean 4 中，我们使用 **`#eval`** 命令直接在编译期或编辑器中执行求值并输出结果：
-/

#eval next_working_day .friday
-- 期望输出: Day.monday

#eval next_working_day (next_working_day .saturday)
-- 期望输出: Day.tuesday

/-!
**第二种方法**：通过编写形式化命题，将我们**所期望的结果**记录为一个机器检验的断言（Assertion / Example）：
-/

/-- 形式化断言：周六之后的第二个工作日必为周二。
    在 Coq 中写作：
    ```coq
    Example test_next_working_day:
      (next_working_day (next_working_day saturday)) = tuesday.
    Proof. simpl. reflexivity. Qed.
    ```
    在 Lean 4 中，使用 `by rfl`（自反性策略 Reflexivity）即可！ -/
example : next_working_day (next_working_day .saturday) = .tuesday := by
  rfl

/-!
上述声明达成了两件事：
1. 它给出了一个精确的形式化数学断言（周六之后的第二个工作日是周二）；
2. 它通过交互式策略脚本（Tactic Script）让 Lean 4 内核对其进行严格证明。

此时具体细节尚不需要深究，但直观而言，`by rfl` 的含义是：
“该断言可以通过直接观察到**等式左右两端在化简展开后计算为完全相同的项（Definitional Equality）**而宣告得证。”

**第三种方法**：从形式化规范中**提取（Extract）或编译**为常规高效代码。
在 Coq 中，用户通常通过抽取机制将证明逻辑转换为 OCaml、Haskell 或 Scheme 代码；
而在现代 Lean 4 中，这一步更加纯粹原生——Lean 4 本身就是一门编译型语言，
它通过自身的编译器流水线，将经过形式化验证的纯函数无缝降维编译为无开销的 **原生 C 语言代码** 与可执行二进制，
从而构成了“算法数学证明严谨”到“工业级机器代码高效执行”的坚实桥梁。
-/

/- ================================================================== -/
/-! ## 2. 布尔类型 (Booleans) -/
/- ================================================================== -/

/-!
依循上述定义一周日期的相同模式，我们可以在一个独立的沙箱命名空间中，从无到有地定义标准的布尔类型 `bool`。
它包含两个最基础的构造子：`true` 和 `false`。
-/

namespace PlayGround

/-- 自定义布尔类型 `bool`。
    为了避免与 Lean 4 标准库内置的 `Bool` 发生歧义冲突，我们将其置于独立的命名空间 `PlayGround` 中。 -/
inductive bool where
  | true
  | false
  deriving Repr, DecidableEq

/-!
作用在布尔值上的基本逻辑函数可以通过完全相同的模式匹配方式进行定义：
-/

/-- 逻辑非（negb）：真变假，假变真。 -/
def negb (b : bool) : bool :=
  match b with
  | .true  => .false
  | .false => .true

/-- 逻辑与（andb）：当且仅当两个操作数皆为真时返回真。 -/
def andb (b1 b2 : bool) : bool :=
  match b1 with
  | .true  => b2
  | .false => .false

/-- 逻辑或（orb）：只要有一个操作数为真即返回真。 -/
def orb (b1 b2 : bool) : bool :=
  match b1 with
  | .true  => .true
  | .false => b2

/-!
上面的 `andb` 与 `orb` 展现了多参数函数的定义方式。
下面的四个单元测试断言，完整覆盖了二元布尔运算的真值表（Truth Table），
构成了关于 `orb` 函数行为的完备形式化规范：
-/

theorem test_orb1 : orb .true  .false = .true  := by rfl
theorem test_orb2 : orb .false .false = .false := by rfl
theorem test_orb3 : orb .false .true  = .true  := by rfl
theorem test_orb4 : orb .true  .true  = .true  := by rfl

/-!
### 2.1 中缀符号表示 (Infix Notation)

对于常用的布尔运算，我们希望能像传统数学那样使用中缀操作符（如 `&&` 与 `||`）。
在 Coq 中使用 `Notation` 命令；而在 Lean 4 中，我们使用 **`infixl`**（左结合中缀定义）声明自定义语法糖：
-/

infixl:65 " &&* " => andb
infixl:60 " ||* " => orb

/-- 验证多层中缀符号计算与结合性 -/
theorem test_orb5 : (.false ||* .false ||* .true) = .true := by rfl

/-!
### 2.2 条件表达式 (Conditional Expressions)

布尔运算也为我们引入编程语言中极为基础的特性提供了契机：**条件表达式（Conditional Expressions）**。
在 Lean 4 中，我们可以针对我们自定义的 `bool` 使用 `match` 或形式统一的条件判断：
-/

def negb' (b : bool) : bool :=
  match b with
  | .true  => .false
  | .false => .true

def andb' (b1 b2 : bool) : bool :=
  match b1 with
  | .true  => b2
  | .false => .false

def orb' (b1 b2 : bool) : bool :=
  match b1 with
  | .true  => .true
  | .false => b2

/-!
在依赖类型论中，条件分支并非什么神秘结构，它本质上就是对恰好拥有**两个构造子**的归纳类型的一种语法展开。
例如，我们可以定义一个黑白二值类型 `bw`（黑 `bw_black` 与白 `bw_white`），并为其编写反转函数：
-/

inductive bw where
  | bw_black
  | bw_white
  deriving Repr, DecidableEq

def invert (x : bw) : bw :=
  match x with
  | .bw_black => .bw_white
  | .bw_white => .bw_black

#eval invert .bw_black
-- 输出: PlayGround.bw.bw_white

#eval invert .bw_white
-- 输出: PlayGround.bw.bw_black

/-!
### 2.3 核心练习题

在教材中，习题通过星级（⭐️ 表示难度）与标准测试断言组织。
练习题使用 `sorry` 占位，读者需要在 Neovim 中把 `sorry` 替换为正确的实现与证明。
-/

/-!
#### ⭐️ 练习题：nandb (1 星，标准)

“与非门”（NAND）运算：当且仅当输入的两个参数不全为 `.true` 时返回 `.true`。
请补全函数定义，并完成随后的四个单测定理证明（将 `sorry` 替换为有效证明 `by rfl`）。
-/

def nandb (b1 b2 : bool) : bool :=
  negb (b1 &&* b2)

theorem test_nandb1 : nandb .true .false = .true := by
  sorry

theorem test_nandb2 : nandb .false .false = .true := by
  sorry

theorem test_nandb3 : nandb .false .true = .true := by
  sorry

theorem test_nandb4 : nandb .true .true = .false := by
  sorry

/-!
#### ⭐️ 练习题：andb3 (1 星，标准)

三元逻辑与运算：仅当三个输入参数全部为 `.true` 时返回 `.true`，否则返回 `.false`。
-/

def andb3 (b1 b2 b3 : bool) : bool :=
  b1 &&* (b2 &&* b3)

theorem test_andb31 : andb3 .true .true .true = .true := by
  sorry

theorem test_andb32 : andb3 .false .true .true = .false := by
  sorry

theorem test_andb33 : andb3 .true .false .true = .false := by
  sorry

theorem test_andb34 : andb3 .true .true .false = .false := by
  sorry

end PlayGround

/- ================================================================== -/
/-! ## 3. 类型与函数类型 (Types and Function Types) -/
/- ================================================================== -/

/-!
在 Lean 4 中，**每一个合法表达式都拥有一个类型**，用以描述它计算出的是何种事物。
**`#check`** 命令指示 Lean 4 打印出一个表达式的具体类型：
-/

#check true
-- 输出: true : Bool

#check PlayGround.bool.true
-- 输出: PlayGround.bool.true : PlayGround.bool

#check (PlayGround.negb .true)
-- 输出: PlayGround.negb PlayGround.bool.true : PlayGround.bool

/-!
在函数式编程中，像 `negb` 这样的函数本身就是**一等数据值**，其地位与普通的 `true` 或 `false` 完全平等。
函数的类型被称为**函数类型（Function Types）**，由箭头（`->` 或 `→`）连接：
-/

#check PlayGround.negb
-- 输出: PlayGround.negb : PlayGround.bool → PlayGround.bool

/-!
类型 `PlayGround.bool → PlayGround.bool` 读作“`bool` 到 `bool`”，它的含义是：
“给定一个类型为 `bool` 的输入参数，该函数必定产生一个类型为 `bool` 的输出结果。”

类似地，多参数函数的类型如 `andb : bool → bool → bool`。
在类型理论中，箭头是**右结合（Right-associative）**的，即它等价于 `bool → (bool → bool)`。
这揭示了柯里化（Currying）的本质：一个接收两个参数的函数，在本质上就是一个“接收第一个参数、返回一个新函数”的单参数函数。
-/

/-!
### 3.1 从旧类型构建新类型 (New Types from Old)

到目前为止我们看到的类型都是“枚举类型”：它们的定义明确穷举了一个有限的离散构造子集合。
下面展示一个更具表现力的数据类型定义，其中某个构造子自身可以携带参数：
-/

inductive rgb where
  | red
  | green
  | blue
  deriving Repr, DecidableEq

inductive color where
  | black
  | white
  | primary (p : rgb)
  deriving Repr, DecidableEq

/-!
让我们仔细考察这个定义：
一个归纳类型的声明达成了两件事：
1. 它定义了一组新的**构造子**。例如 `red`、`primary`、`black`、`white` 都是构造子；
2. 它将这些构造子打包规约到一个全新的命名类型之下（如 `rgb` 或 `color`）。

**构造子表达式（Constructor Expressions）** 是通过将构造子应用于符合类型数量约束的其他表达式所构成的合法项。
例如：`.red`、`.primary .red`、`.white` 是合法的构造子表达式；
而 `.primary (.primary .red)` 则不合法，因为 `primary` 要求其参数类型必须是 `rgb`，而不能是 `color`。
-/

/-- 判断一种颜色是否属于单色灰度（黑或白） -/
def monochrome (c : color) : PlayGround.bool :=
  match c with
  | .black     => .true
  | .white     => .true
  | .primary _ => .false

/-- 判断一种颜色是否恰好是纯三原色中的红（primary red） -/
def isred (c : color) : PlayGround.bool :=
  match c with
  | .black        => .false
  | .white        => .false
  | .primary .red => .true
  | .primary _    => .false

/-!
在上述模式匹配中，下划线通配符 `_` 的作用是通配任意其他可能的分支，
避免引入不必要的无用变量名。
-/

/-!
### 3.2 模块与命名空间 (Modules and Namespaces)

大型工程需要模块系统来组织代码并避免命名污染。
在 Coq 中使用 `Module X ... End X`；而在 Lean 4 中，我们使用 **`namespace X ... end X`**。
在命名空间内部定义的符号，在空间外部需要通过带前缀的全限定名（如 `ModulePlayground.foo`）来引用：
-/

namespace ModulePlayground
  def foo : rgb := .blue
end ModulePlayground

def foo : PlayGround.bool := .true

#check ModulePlayground.foo
-- 输出: ModulePlayground.foo : rgb

#check foo
-- 输出: foo : PlayGround.bool

/-!
### 3.3 元组与多字段构造子 (Tuples)

单个携带多个参数的构造子可以用来创建复合元组类型。
作为一个直观示例，考虑用四位（Nybble，半个字节）表示二进制片段。
我们首先定义一位数据 `bit`（包含 `B0` 和 `B1` 两个状态），然后定义 `nybble`，它在本质上就是四个 `bit` 的元组打包：
-/

namespace TuplePlayground

inductive bit where
  | B1
  | B0
  deriving Repr, DecidableEq

inductive nybble where
  | bits (b0 b1 b2 b3 : bit)
  deriving Repr, DecidableEq

#check nybble.bits .B1 .B0 .B1 .B0
-- 输出: nybble.bits bit.B1 bit.B0 bit.B1 bit.B0 : nybble

/-- 检查一个 nybble 是否四位全为零 (B0) -/
def all_zero (nb : nybble) : PlayGround.bool :=
  match nb with
  | .bits .B0 .B0 .B0 .B0 => .true
  | .bits _ _ _ _         => .false

#eval all_zero (.bits .B1 .B0 .B1 .B0)
-- 输出: PlayGround.bool.false

#eval all_zero (.bits .B0 .B0 .B0 .B0)
-- 输出: PlayGround.bool.true

end TuplePlayground

/- ================================================================== -/
/-! ## 4. 自然数与皮亚诺算术 (Numbers) -/
/- ================================================================== -/

/-!
迄今为止我们定义的所有类型——不论是一周的七天、布尔值还是半字节元组——全都是**有限集（Finite Sets）**。
然而，自然数是一个**无穷无尽的无限集合（Infinite Set）**。
为了严密形式化表达无限概念，我们需要使用一种更丰富、具备自指自构能力的类型声明形态——**递归归纳定义**。

在人类数学史上，存在着许多数值表示方案：
- 最常见的是十进制（Base 10），使用字符 `0` 到 `9` 拼合数值；
- 计算机底层钟爱二进制（Base 2），因为只需要两种电平即可稳定实现硬件逻辑；
- 而在定理证明与逻辑学领域，最理想的是一种能够让**形式化数学归纳证明最为简练清晰**的表示方案。

这便是**一进制（Unary，Base 1）——皮亚诺公理体系**。
在皮亚诺表示法中，仅需要两个纯粹的构造子：
1. 字符 `O` 表示零；
2. 构造子 `S` 施加在某个自然数 $n$ 之上，表示其后继（Successor，即 $n + 1$）。
-/

namespace NatPlayground

/-- 皮亚诺自然数系统的归纳构造定义。
    - `O` 代表零；
    - `S n` 代表 `n + 1`。 -/
inductive nat where
  | O
  | S (n : nat)
  deriving Repr, DecidableEq

/-!
有了这个定义：
- $0$ 表示为 `O`；
- $1$ 表示为 `S O`；
- $2$ 表示为 `S (S O)`；
- $3$ 表示为 `S (S (S O))`，以此类推。

**至关重要的一点认知**：我们目前所做的仅仅是定义了一种数值的**“书写表示记号”**。
名称 `O` 与 `S` 本身并没有任何内嵌的数学魔法，它们只是符号记号。
如果我们愿意，完全可以写出结构完全同构的另一种记号表达：
-/

inductive otherNat where
  | stop
  | tick (foo : otherNat)
  deriving Repr, DecidableEq

/-!
这些机械符号之所以能被赋予真正的“数学含义”，完全来自于我们**如何利用模式匹配来编写对它们进行求值的计算规则**。
例如，自然数的前驱函数 `pred`（即减一运算，零的前驱规定仍为零）：
-/

def pred (n : nat) : nat :=
  match n with
  | .O    => .O
  | .S n' => n'

end NatPlayground

/-!
自然数是计算机科学与形式化逻辑中最常用的基础结构。
现代 Lean 4 标准库直接提供了高精度的原生 `Nat`，其底层逻辑正是皮亚诺构造（`Nat.zero` 与 `Nat.succ`），
同时编译器提供了语法糖，允许我们直接使用阿拉伯数字（如 `0`、`1`、`4`）直观书写。
接下来，我们将使用这一标准的自然数体系进一步深入展开。
-/

/-- 前驱两次（minustwo）：对一个自然数连续递减两次。
    若小于等于 1 则结果为 0。 -/
def minustwo (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | 1      => 0
  | n' + 2 => n'

#eval minustwo 4
-- 输出: 2

/-!
### 4.1 递归函数 (Recursion)

对于多数涉及自然数的非平凡运算，单纯的单层模式匹配是不足够的，我们必须借助**结构化递归（Structural Recursion）**。
在 Coq 中引入递归函数使用关键字 `Fixpoint`；
而在 Lean 4 中，直接使用统一的 **`def`** 声明即可——Lean 4 的方程编译器会自动对结构化减小（Structural Decrease）进行停机检查（Termination Checking），确保函数必定终止。
-/

/-- 判断一个自然数是否为偶数（even）：
    - 0 是偶数；
    - 1 不是偶数；
    - 对于 (n' + 2)，其奇偶性与 n' 严格一致。 -/
def even (n : Nat) : Bool :=
  match n with
  | 0      => true
  | 1      => false
  | n' + 2 => even n'

/-- 判断一个自然数是否为奇数（odd）：直接等于“偶数判断”的反面。 -/
def odd (n : Nat) : Bool :=
  !even n

theorem test_odd1 : odd 1 = true  := by rfl
theorem test_odd2 : odd 4 = false := by rfl

/-!
### 4.2 多参数自然数算术运算

借助结构化递归，我们可以从无到有地推导出加法、乘法与减法：
-/

namespace NatPlayground2

/-- 自然数加法：对第一个参数进行结构化递归。
    - 0 + m = m；
    - (S n') + m = S (n' + m)。 -/
def plus (n m : Nat) : Nat :=
  match n with
  | 0      => m
  | n' + 1 => (plus n' m) + 1

#eval plus 3 2
-- 输出: 5

/-!
Lean 4 内核对 `plus 3 2` 的规约化简步骤清晰可视：
```
  plus 3 2
= plus (2 + 1) 2
= (plus 2 2) + 1
= ((plus 1 2) + 1) + 1
= (((plus 0 2) + 1) + 1) + 1
= (((2) + 1) + 1) + 1
= 5
```
-/

/-- 自然数乘法：将乘法转化为连加。
    - 0 * m = 0；
    - (n' + 1) * m = m + (n' * m)。 -/
def mult (n m : Nat) : Nat :=
  match n with
  | 0      => 0
  | n' + 1 => m + (mult n' m)

theorem test_mult1 : mult 3 3 = 9 := by rfl

/-- 自然数减法：截断减法（Saturating Subtraction）。
    由于自然数不存在负数，当减数大于被减数时结果截断为 0。 -/
def minus (n m : Nat) : Nat :=
  match n, m with
  | 0,      _      => 0
  | _,      0      => n
  | n' + 1, m' + 1 => minus n' m'

end NatPlayground2

/-- 自然数乘方运算：base 的 power 次幂。
    - base ^ 0 = 1；
    - base ^ (p + 1) = base * (base ^ p)。 -/
def exp (base power : Nat) : Nat :=
  match power with
  | 0     => 1
  | p + 1 => base * (exp base p)

/-!
#### ⭐️ 练习题：factorial (1 星，标准)

回忆经典数学中的阶乘函数：
$$factorial(0) = 1$$
$$factorial(n) = n \times factorial(n - 1) \quad (n > 0)$$

请在 Lean 4 中完成该函数的定义，并使随后的两个形式化验证断言顺利得证：
-/

def factorial (n : Nat) : Nat :=
  match n with
  | 0     => 1
  | n' + 1 => (n' + 1) * factorial n'

theorem test_factorial1 : factorial 3 = 6 := by
  sorry

theorem test_factorial2 : factorial 5 = 10 * 12 := by
  sorry

/-!
### 4.3 自然数的可判定比较运算

在逻辑学中，**判断两个对象是否相等**本身也是一种可定义的运算。
在这里我们需要严格区分两个核心概念：
1. **逻辑命题等式（Propositional Equality，写作 `=`）**：
   这是一个数学**断言**（例如 $n = m$），它属于逻辑宇宙 `Prop`，本身不是可以直接运行的布尔代码，而是需要提供严格的形式化数学证明（Proof）；
2. **布尔可判定比较（Boolean Equality Test，我们写作 `=?`）**：
   这是一个具体的**可执行计算程序**，它接收两个数值，直接在有限步内计算返回 `.true` 或 `.false`。
-/

/-- 检验两个自然数是否数值相等，返回布尔值 `Bool` -/
def eqb (n m : Nat) : Bool :=
  match n, m with
  | 0,      0      => true
  | 0,      _ + 1  => false
  | _ + 1,  0      => false
  | n' + 1, m' + 1 => eqb n' m'

/-- 检验第一个自然数是否小于等于第二个自然数 (Less-than-or-Equal-Boolean) -/
def leb (n m : Nat) : Bool :=
  match n, m with
  | 0,      _      => true
  | _ + 1,  0      => false
  | n' + 1, m' + 1 => leb n' m'

theorem test_leb1 : leb 2 2 = true  := by rfl
theorem test_leb2 : leb 2 4 = true  := by rfl
theorem test_leb3 : leb 4 2 = false := by rfl

/-- 为等式与不等式判断引入直观的中缀符号表示 -/
infix:70 " =? "  => eqb
infix:70 " <=? " => leb

theorem test_leb3' : (4 <=? 2) = false := by rfl

/-!
#### ⭐️ 练习题：ltb (1 星，标准)

自然数严格小于比较函数（`ltb`）：当且仅当第一个参数严格小于第二个参数时返回 `true`。
提示：不需要重新编写带双重模式匹配的递归函数，请直接尝试用已经定义好的 `eqb` 和 `leb` 来组合实现它！
-/

def ltb (n m : Nat) : Bool :=
  (leb n m) && !(eqb n m)

infix:70 " <? " => ltb

theorem test_ltb1 : (ltb 2 2) = false := by
  sorry

theorem test_ltb2 : (ltb 2 4) = true := by
  sorry

theorem test_ltb3 : (ltb 4 2) = false := by
  sorry


/- ================================================================== -/
/-! ## 5. 通过化简进行证明 (Proof by Simplification) -/
/- ================================================================== -/

/-!
既然我们已经探索了若干核心数据类型与操纵它们的函数，
现在让我们转向形式化验证的核心主题：**陈述并机器检验关于这些程序行为的数学性质**。

实际上，我们在之前的章节中已经在不经意间开始了这项工作：
前文中的每一个 `example`，本质上都是关于某个函数在特定输入下的运行时行为做出的精确**断言（Claim）**。
那些断言的形式化证明模式是完全统一的：
在 Coq 中，使用策略 `simpl` 化简等式两端，然后用 `reflexivity` 检查化简后两端是否完全字面一致；
而在 Lean 4 中，策略 **`rfl`（自反性 Reflexivity）** 会自动展开可规约的定义并进行化简求值，直接闭合证明目标！

这种“通过化简进行证明”的机制，同样可以用来确立更具通用性、更有数学趣味的普遍定理。
例如，“$0$ 是自然数加法的左中性元（$0 + n = n$）”这一性质，
可以通过观察 $0 + n$ 无论对于什么具体的 $n$ 都会自然归约为 $n$ 得到证实。
-/

/-- 自然数加法左中性元引理：对任意自然数 n，0 + n = n。
    注意：在我们之前定义的 `NatPlayground2` 命名空间中，加法 `plus` 是对第一个参数进行结构化模式匹配的，
    因此当第一个参数为 0 时，无需对 n 的取值做任何预设，Lean 4 的内核展开定义即可立即判定两边恒等！ -/
theorem plus_O_n (n : Nat) : NatPlayground2.plus 0 n = n := by
  rfl

/-- 原版 Coq 中的变体定理名称别名 -/
theorem plus_O_n_playground (n : Nat) : NatPlayground2.plus 0 n = n := by
  rfl

/-- 显式使用全称量词与 intro 策略的版本 -/
theorem plus_O_n' : ∀ n : Nat, NatPlayground2.plus 0 n = n := by
  intro n
  rfl

/-- 更加紧凑的无参数化化简版本 -/
theorem plus_O_n'' : ∀ n : Nat, NatPlayground2.plus 0 n = n := by
  intros
  rfl

/-- 左加一引理（在自定义 NatPlayground2 递归加法下）：1 + n = n + 1。 -/
theorem plus_1_l (n : Nat) : NatPlayground2.plus 1 n = n + 1 := by
  rfl

theorem plus_1_l_playground (n : Nat) : NatPlayground2.plus 1 n = n + 1 := by
  rfl

/-- 左零乘引理（在自定义 NatPlayground2 递归乘法下）：0 * n = 0。 -/
theorem mult_0_l (n : Nat) : NatPlayground2.mult 0 n = 0 := by
  rfl

/-!
💡 **深度解析：Coq 与 Lean 4 标准库的加法定义差异**

- 在 Coq 的标准库中，加法 `plus` 是对**第一个参数**进行结构化递归的（`0 + n ==> n`），
  因此在 Coq 中 `0 + n = n` 可以直接通过 `reflexivity` 证明，而 `n + 0 = n` 则无法单靠化简解决（必须借助归纳法）。
- 在现代 Lean 4 的官方标准库 `Nat` 中，加法 `+` 则是对**第二个参数**进行结构化递归的（`n + 0 ==> n`）。
  因此在 Lean 4 原生环境中，`n + 0 = n` 可以直接 `by rfl` 判定，而 `0 + n = n` 则是标准库中的已证定理 `Nat.zero_add n`。
- 不过，这两种设计在数学逻辑上是完全对偶的。下面我们展示 Lean 4 原生加法中右中性元的直接化简：
-/

/-- 原生自然数加法右中性元：对任意自然数 n，n + 0 = n 恒成立。 -/
theorem plus_n_O (n : Nat) : n + 0 = n := by
  rfl

/-- 原生自然数乘法右零元：对任意自然数 n，n * 0 = 0 恒成立。 -/
theorem mult_n_O (n : Nat) : n * 0 = 0 := by
  rfl

/-!
让我们仔细考察一下上述定理的声明语法与之前 `example` 的不同之处：

1. **关键字 `theorem`**：
   在 Lean 4 中，可以使用 `theorem`、`lemma`、`example` 或 `fact`。
   `example` 是一次性的匿名断言，不会将证明结果注册到全局符号表中；
   而 `theorem` 和 `lemma` 会为证明赋予一个永久的名字，使随后的其他证明能够引用它。
2. **全称量词与上下文引入**：
   上面的定理表述了对**所有**自然数 `n` 普遍成立的结论。
   在命题中，我们可以写成 `(n : Nat)` 作为参数，也可以显式使用全称量词符号 `∀ (n : Nat), ...`。
   在证明体中，我们可以使用 **`intro` 策略**将量词绑定的变量引入证明上下文（Context）中：
-/

theorem plus_n_O' : ∀ n : Nat, n + 0 = n := by
  intro n  -- 将量词 ∀ n 引入局部假设上下文
  rfl      -- 通过内核自反性完成化简校验

/-!
`intro` 与 `rfl` 是我们接触到的第一批**证明策略（Tactics）**。
策略是写在 `by` 代码块中的交互式指令，用于指导证明助手逐步化简目标（Goal）、操纵假设，直至最终构建出合法的证明项。
-/

/-- 在 Lean 4 原生标准库下：n + 1 与 Nat.succ n 具有相同的定义构造。 -/
theorem plus_1_r (n : Nat) : n + 1 = Nat.succ n := by
  rfl


/- ================================================================== -/
/-! ## 6. 通过重写进行证明 (Proof by Rewriting) -/
/- ================================================================== -/

/-!
并非所有定理都能单凭简单的展开计算直接解决。
来看下面这个比先前更耐人寻味的定理：
-/

theorem plus_id_example (n m : Nat) (h : n = m) : n + n = m + m := by
  -- 此时两端含有未知的符号变量 n 和 m，无法直接通过 rfl 化简。
  -- 但在上下文中有已知前提假设 h : n = m。
  -- 策略 `rw [h]` 会将目标中所有出现的 n 统一替换为 m：
  rw [h]

/-!
上面这个定理并未声称对任意互不相关的 `n` 和 `m` 都有 `n + n = m + m`；
它是一个**条件命题**：仅当已知前提 $n = m$ 成立时，结论才成立。
在 Lean 4 中，前提条件可以直接写为定理的命名参数（如 `(h : n = m)`），
也可以用蕴涵箭头 `n = m → n + n = m + m` 书写。

策略 **`rw [h]`**（重写 Rewriting）告诉 Lean 4：
利用等式假设 `h`，将目标中与 `h` 左侧相同的子项全部替换为其右侧的内容。
如果我们希望从右向左逆向替换，只需在等式名前加上左箭头：`rw [← h]`（在 Neovim 中输入 `\l` 即可补全为 `←`）。
-/

/-!
#### ⭐️ 练习题：plus_id_exercise (1 星，标准)

请证明以下定理：已知前提 `h1 : n = m` 与 `h2 : m = o`，证明 `n + m = m + o`。
提示：连续使用两次 `rw` 重写策略，把结论化简为显然等价的形式。
-/

theorem plus_id_exercise (n m o : Nat) (h1 : n = m) (h2 : m = o) : n + m = m + o := by
  sorry

/-!
### 6.1 复用已证明的引理

`rw` 策略不仅能使用当前上下文中的局部假设 `h`，
更可以直接使用**之前已经证明过的全局定理或标准库引理**。
当被引用的定理中包含全称量词变量时，Lean 4 会自动通过模式匹配（Pattern Matching）去推导相应的实例化参数：
-/

/-- 利用标准库乘法性质定理证明两个乘积之和为 0。
    Lean 4 标准库提供了 `Nat.mul_zero (n : Nat) : n * 0 = 0`。 -/
theorem mult_n_0_m_0 (p q : Nat) : (p * 0) + (q * 0) = 0 := by
  rw [Nat.mul_zero p]  -- 将 (p * 0) 重写为 0
  rw [Nat.mul_zero q]  -- 将 (q * 0) 重写为 0

/-!
#### ⭐️ 练习题：mult_n_1 (1 星，标准)

在 Lean 4 标准库中，自然数乘法满足以下恒等式：
- `Nat.mul_one (p : Nat) : p * 1 = p`
请完成以下定理的形式化验证：
-/

theorem mult_n_1 (p : Nat) : p * 1 = p := by
  sorry

/- ================================================================== -/
/-! ## 7. 通过分类讨论进行证明 (Proof by Case Analysis) -/
/- ================================================================== -/

/-!
并非所有数学性质都能单靠化简与等式重写得证。
一般而言，当目标中包含**未知、抽象的假设变量**（例如任意的布尔值、任意的自然数或列表）时，
直接计算往往会被“卡住”。

例如，考虑下面这个看似极其显而易见的断言：对任意自然数 `n`，$(n + 1) =? 0$ 必定为 `false`。
如果我们尝试直接写下 `by rfl`，编译器会立即报错：
因为我们之前定义的判定函数 `=?`（`eqb`）的第一步操作就是对传入的数值进行模式匹配；
然而此时我们面对的是一个未知的、通用的代数符号 `n`，编译器无法判定它到底匹配哪一个分支，化简由此中断！

为了打破僵局，我们必须对未知变量的所有可能形态进行**分类讨论（Case Analysis）**：
- 如果 $n$ 是基底 $0$，那么 $(0 + 1) =? 0$ 变成了 $1 =? 0$，可以直接计算求值为 `false`；
- 如果 $n$ 是某个后继 $n' + 1$，那么 $((n' + 1) + 1) =? 0$ 的外层构造子必定是后继，同样可以直接计算求值为 `false`。

在 Coq 中，执行分类讨论的策略被称为 `destruct`；
而在 Lean 4 中，最核心、最严谨的策略是 **`cases`**：
-/

/-- 首次尝试：直接使用自反性或化简无法证明该命题，因为 `(n + 1) =? 0` 依赖于未知的 `n`。
    在原版 Coq 中，使用 `Abort` 中途放弃；在 Lean 4 中我们使用 `sorry` 占位说明其卡住的状态。 -/
theorem plus_1_neq_0_firsttry (n : Nat) : ((n + 1) =? 0) = false := by
  -- simpl 或 rfl 在此无法继续展开，因为我们不知道 n 是 0 还是后继 S n'
  sorry

theorem plus_1_neq_0 (n : Nat) : ((n + 1) =? 0) = false := by
  -- 对自然数 n 的两种可能归纳构造分别进行讨论：
  cases n with
  | zero =>
    -- 子目标 1：n = 0 的情形
    rfl
  | succ n' =>
    -- 子目标 2：n = n' + 1 的情形
    rfl

/-!
在 Lean 4 的 `cases` 语法中：
- `cases n with | zero => ... | succ n' => ...` 结构极其严谨优美；
- 每一个分支以竖线 `|` 和对应的构造子名称引导；
- Lean 4 会强制保证**穷尽性（Exhaustiveness）**：你必须处理该类型的所有可能构造子，漏掉任何一种都会导致编译错误。
-/

/-!
### 7.1 布尔代数性质证明

`cases` 策略同样适用于我们在 `PlayGround` 命名空间中从零构建的布尔类型 `bool`。
由于布尔类型只有 `.true` 和 `.false` 两个构造子，而且它们都不携带任何参数，
因此对其进行分类讨论最为简单直观：
-/

namespace PlayGround

/-- 双重否定律：对任意布尔值 b，对其连续取反两次后仍然等于它自身。
    原版 Coq 中需要：`intros b. destruct b. - reflexivity. - reflexivity.`
    在 Lean 4 中，通过结构化的 `cases` 展开，一目了然： -/
theorem negb_involutive (b : bool) : negb (negb b) = b := by
  cases b with
  | true  => rfl
  | false => rfl

/-- 逻辑与交换律：b &&* c = c &&* b。
    当命题涉及多个变量时，我们可以通过嵌套 `cases` 进行多维分类讨论： -/
theorem andb_commutative (b c : bool) : andb b c = andb c b := by
  cases b with
  | true  =>
    cases c with
    | true  => rfl
    | false => rfl
  | false =>
    cases c with
    | true  => rfl
    | false => rfl

/-- 逻辑与交换律的另一种书写风格：
    在 Coq 原作中使用花括号 `{ ... }` 组织多层子目标；
    在 Lean 4 中，我们可以使用点号 `.` 或直接展示 `<;>` 战术连接符，
    将策略一次性应用到由前序策略产生的所有子分支： -/
theorem andb_commutative' (b c : bool) : andb b c = andb c b := by
  cases b <;> cases c <;> rfl

/-- 三元逻辑与结合律与交换律组合示例：
    借助 Lean 4 的策略连接符 `<;>`（将后续策略同时应用到由前序策略生成的所有子目标上），
    我们可以将极其冗长的多分支枚举证明极度浓缩为单行代码！ -/
theorem andb3_exchange (b c d : bool) :
    andb (andb b c) d = andb (andb b d) c := by
  cases b <;> cases c <;> cases d <;> rfl

/-!
#### ⭐️⭐️ 练习题：andb_true_elim2 (2 星，标准)

请证明：如果已知 `andb b c = .true`，那么必有 `c = .true`。
提示：
1. 对 `b` 和 `c` 进行分类讨论；
2. 当在假设前提中推导出不可能成立的矛盾时（例如 `.false = .true`），
   可以使用 Lean 4 的 **`contradiction`** 策略自动利用矛盾闭合当前目标！
-/

theorem andb_true_elim2 (b c : bool) (h : andb b c = .true) : c = .true := by
  sorry

/-!
### 7.2 方程编译器证明（Lean 4 独占特色）

在 Lean 4 中，定理证明与函数式编程遵循深度的“命题即类型、证明即程序（Curry-Howard 同构）”哲学。
因此，许多原本需要调用 `cases` 策略的分支证明，
可以直接使用 Lean 4 的**方程编译器（Equation Compiler）**以模式匹配的方式直接写就，连 `by` 关键字都不需要！
-/

/-- 使用方程编译器模式匹配直接证明逻辑与交换律：优雅、直观、地道！ -/
theorem andb_commutative'' : ∀ (b c : bool), andb b c = andb c b
  | .true,  .true  => rfl
  | .true,  .false => rfl
  | .false, .true  => rfl
  | .false, .false => rfl

end PlayGround

/-- 使用方程编译器（模式匹配）简写的加一非零定理：
    在原版 Coq 中可以使用模式化引入 `intros [|n]`；
    在 Lean 4 中，直接使用方程编译器可以在无需调用 `by cases` 的情况下直接展开分支： -/
theorem plus_1_neq_0' : ∀ n : Nat, ((n + 1) =? 0) = false
  | 0     => rfl
  | _ + 1 => rfl

/-!
#### ⭐️ 练习题：zero_nbeq_plus_1 (1 星，标准)

请证明：对任意自然数 `n`，判断式 `0 =? (n + 1)` 的计算结果必定为 `false`。
-/

theorem zero_nbeq_plus_1 (n : Nat) : (0 =? (n + 1)) = false := by
  sorry


/- ================================================================== -/
/-! ## 8. 进阶：记号机制与结构化递归 (More on Notation & Structural Recursion) -/
/- ================================================================== -/

/-!
### 8.1 语法记号与优先级 (More on Notation)

在之前的定义中，我们已经见识过了中缀运算符记号（如 `&&*`、`+*`、`=?` 等）。
在形式化证明助手中，为常用函数引入符合人类数学直觉的操作符，对于代码的可读性有着决定性的影响。

在原版 Coq 中，定义记号使用 `Notation`，并指定 `at level n`（优先级范围为 0 到 100）与结合性（`left associativity`）。
而在 Lean 4 中，中缀记号体系更为规范强大，直接通过内置的宏指令声明：
- `infixl:65 " + " => Nat.add`（左结合，优先级 65）
- `infixr:80 " ^ " => Nat.pow`（右结合，优先级 80）
- `prefix:90 " - " => Neg.neg`（前缀运算符）

Lean 4 的优先级采用更宽广的数值区间（0 至 1024），其中乘法默认优先级高于加法。
这使得形如 `1 + 2 * 3 * 4` 的复合表达式能够毫无歧义地被解析为 `1 + ((2 * 3) * 4)`。
-/

/-!
### 8.2 停机检查与结构化递归 (Fixpoints and Structural Recursion)

当我们编写一个递归函数时（例如之前的加法 `plus`）：
Lean 4 为什么能允许我们写递归？
这是因为 Lean 4 的类型论内核要求：**所有函数必须是良基且必定终止的（Well-founded and terminating）**。

在 Coq 中，递归函数必须通过关键字 `Fixpoint` 声明，并且必须有某个参数在每一次递归调用中都在**严格减小（Decreasing）**——即所谓的**结构化递归（Structural Recursion）**。
如果无法在语法层面上证明存在某个递减的归纳参数，Coq 就会直接拒绝该函数。
例如下面重新写出的加法定义：
-/

/-- 结构化递归加法 `plus'`：严格在第一个参数 `n` 上进行结构递减递归。 -/
def plus' (n : Nat) (m : Nat) : Nat :=
  match n with
  | 0      => m
  | n' + 1 => (plus' n' m) + 1

/-!
在 Lean 4 中，我们无需区分 `def` 与 `Fixpoint`，统一使用 `def`。
Lean 4 的方程编译器在后台拥有更加先进的自动化停机检查器（Termination Checker）：
1. 默认情况下，Lean 4 会自动尝试寻找结构化减小（Structural Decrease）的参数；
2. 如果函数不是朴素的结构递减（例如斐波那契数列、二分查找、或通过欧几里得算法求最大公约数），
   Lean 4 允许我们显式提供停机依据：使用 `termination_by` 指定测度（Measure），
   并结合 `decreasing_by` 给出该测度严格下降的数学证明。
-/

/-!
#### ⭐️⭐️ 练习题：decreasing (2 星，标准，可选)

为了切实感受这一机制，请思考并尝试设计一个逻辑上对所有输入必定终止，
但无法直接通过最基础的语法结构递减分析的递归函数。

例如在原版 Coq 中讨论的典型例子：
```lean
-- def trouble_mult (n : Nat) : Nat := mult (NatPlayground2.plus 1 (trouble_mult n)) 0
```
虽然由于外层乘以 0，该函数数学上对任意输入实际上都会终止并求值为 0，
但由于内部递归调用 `trouble_mult n` 的参数并没有在语法上严格变小，
原始的形式化停机检查器会直接拒绝此类定义。
（如果你在自己的作业中探索此题，请将其注释掉，以免阻塞全局编译！）
-/

/- ================================================================== -/
/-! ## 9. 基础热身练习 (Warmup Exercises) -/
/- ================================================================== -/

/-!
在进入大规模实战案例之前，让我们先用几道精炼的习题检验并巩固我们迄今为止学到的策略：
`intro`、`rw`、`cases` 与 `rfl`。
-/

/-!
#### ⭐️ 练习题：identity_fn_applied_twice (1 星，标准)

恒等函数应用两次：设 `f : Bool → Bool` 是一个布尔函数。
如果已知前提 `h : ∀ (x : Bool), f x = x`（即 `f` 是恒等函数），
请证明：对任意布尔值 `b`，都有 `f (f b) = b`。
提示：使用两次 `rw [h]` 策略。
-/

theorem identity_fn_applied_twice (f : Bool → Bool) (h : ∀ (x : Bool), f x = x) (b : Bool) :
    f (f b) = b := by
  sorry

/-!
#### ⭐️ 练习题：negation_fn_applied_twice (1 星，标准)

取反函数应用两次：设 `f : Bool → Bool` 是一个布尔函数。
如果已知前提 `h : ∀ (x : Bool), f x = !x`（即 `f` 具有逻辑非的性质），
请证明：对任意布尔值 `b`，都有 `f (f b) = b`。
提示：先使用 `rw` 代入 `h`，然后对 `b` 进行分类讨论（`cases b`）。
-/

theorem negation_fn_applied_twice (f : Bool → Bool) (h : ∀ (x : Bool), f x = !x) (b : Bool) :
    f (f b) = b := by
  sorry

/-- 自动评分系统使用的辅助占位定义 (保持与原版 autograder 接口兼容) -/
def manual_grade_for_negation_fn_applied_twice : Option (Nat × String) := none

/-!
#### ⭐️⭐️⭐️ 练习题：andb_eq_orb (3 星，标准，可选)

请证明：对任意我们自定义的布尔值 `b` 和 `c`，
如果 `(b &&* c) = (b ||* c)`，那么必有 `b = c`。
提示：对 `b` 进行分类讨论；在每一个分支中化简等式两端，你会发现结论自然浮现。
-/

theorem andb_eq_orb (b c : PlayGround.bool)
    (h : PlayGround.andb b c = PlayGround.orb b c) : b = c := by
  sorry

/- ================================================================== -/
/-! ## 10. 形式化实战案例：课程作业迟交评分政策 (Course Late Policies, Formalized) -/
/- ================================================================== -/

/-!
形式化验证并不仅仅局限于抽象的数学命题，
它同样能够极其精准地形式化现实生活与软件系统中的业务规则，发现潜藏在文字描述中的漏洞与边界缺陷。

假设某大学课程制定了一套基于迟交天数（Late Days）的作业扣分政策：
如果学生迟交次数过多，期末的成绩等级将会被降级。
在接下来的系列任务中，我们将使用迄今学到的全部语言特性对这套规则进行严格的形式化建模，
并证明关于该评分政策的定理。
-/

namespace LateDays

/-!
### 10.1 等级与修饰符数据结构建模
-/

/-- 成绩的字母部分：A、B、C、D、F -/
inductive Letter where
  | A
  | B
  | C
  | D
  | F
  deriving Repr, DecidableEq

/-- 等级修饰符：加号（Plus，如 A+）、普通无修饰（Natural，如 A）、减号（Minus，如 A-） -/
inductive Modifier where
  | Plus
  | Natural
  | Minus
  deriving Repr, DecidableEq

/-- 完整的成绩等级：由一个字母和一个修饰符复合而成。
    例如 `Grade.grade .A .Minus` 表示 A-，`Grade.grade .C .Natural` 表示 C。 -/
inductive Grade where
  | grade (l : Letter) (m : Modifier) : Grade
  deriving Repr, DecidableEq

/-- 用于表示三元比较结果的枚举类型：相等 (Eq)、严格小于 (Lt)、严格大于 (Gt) -/
inductive Comparison where
  | Eq
  | Lt
  | Gt
  deriving Repr, DecidableEq

open Letter Modifier Grade Comparison

/-!
### 10.2 比较运算定义
-/

/-- 比较两个字母等级的高低：A > B > C > D > F -/
def letter_comparison (l1 l2 : Letter) : Comparison :=
  match l1, l2 with
  | .A, .A => .Eq
  | .A, _  => .Gt
  | .B, .A => .Lt
  | .B, .B => .Eq
  | .B, _  => .Gt
  | .C, .A | .C, .B => .Lt
  | .C, .C => .Eq
  | .C, _  => .Gt
  | .D, .A | .D, .B | .D, .C => .Lt
  | .D, .D => .Eq
  | .D, _  => .Gt
  | .F, .F => .Eq
  | .F, _  => .Lt

#eval letter_comparison .B .A
-- 输出: Comparison.Lt

#eval letter_comparison .D .D
-- 输出: Comparison.Eq

#eval letter_comparison .B .F
-- 输出: Comparison.Gt

/-!
#### ⭐️ 练习题：letter_comparison (1 星，标准)

健全性自检：证明任何字母等级与自身比较必然为 `.Eq`。
-/

theorem letter_comparison_Eq (l : Letter) : letter_comparison l l = .Eq := by
  sorry

/-- 比较两个修饰符的高低：Plus > Natural > Minus -/
def modifier_comparison (m1 m2 : Modifier) : Comparison :=
  match m1, m2 with
  | .Plus, .Plus => .Eq
  | .Plus, _     => .Gt
  | .Natural, .Plus => .Lt
  | .Natural, .Natural => .Eq
  | .Natural, _  => .Gt
  | .Minus, .Plus | .Minus, .Natural => .Lt
  | .Minus, .Minus => .Eq

/-!
#### ⭐️⭐️ 练习题：grade_comparison (2 星，标准)

请补全两个完整成绩之间的比较运算（字典序比较）：
首先比较字母等级；如果字母相同，再进一步比较修饰符。
-/

def grade_comparison (g1 g2 : Grade) : Comparison :=
  match g1, g2 with
  | .grade l1 m1, .grade l2 m2 =>
    match letter_comparison l1 l2 with
    | .Eq => modifier_comparison m1 m2
    | .Gt => .Gt
    | .Lt => .Lt

-- 单元测试断言
theorem test_grade_comparison1 : grade_comparison (.grade .A .Minus) (.grade .B .Plus) = .Gt := by rfl
theorem test_grade_comparison2 : grade_comparison (.grade .A .Minus) (.grade .A .Plus) = .Lt := by rfl
theorem test_grade_comparison3 : grade_comparison (.grade .F .Plus) (.grade .F .Plus) = .Eq := by rfl
theorem test_grade_comparison4 : grade_comparison (.grade .B .Minus) (.grade .C .Plus) = .Gt := by rfl

/-!
### 10.3 降级逻辑与边界反例分析
-/

/-- 将字母等级降低一档（A 降为 B，B 降为 C 等；F 已经是最低，保持为 F） -/
def lower_letter (l : Letter) : Letter :=
  match l with
  | .A => .B
  | .B => .C
  | .C => .D
  | .D => .F
  | .F => .F

/-- 边界事实：F 无法再降低，降低 F 仍得到 F -/
theorem lower_letter_F_is_F : lower_letter .F = .F := by
  rfl

/-- 首次尝试：直觉上会认为降低字母等级必然使等级变低。
    然而该命题在数学上并不成立（反例是 l = F 时，lower_letter F = F，比较结果为 Eq 而非 Lt）！
    原版 Coq 在验证到最后一个分支时卡住并使用 `Abort` 放弃；在 Lean 4 中我们使用 `sorry` 演示该卡住尝试。 -/
theorem lower_letter_lowers_firsttry (l : Letter) :
    letter_comparison (lower_letter l) l = .Lt := by
  sorry

/-!
#### ⭐️⭐️ 练习题：lower_letter_lowers (2 星，标准)

我们直觉上会认为“降低一个字母等级后必然比原来低”，即：
`∀ l, letter_comparison (lower_letter l) l = .Lt`。
但在形式化世界中，这个命题是不成立的——反例恰恰是 `l = .F`！
只要我们加上前置条件排除 `F`（即 `h : letter_comparison .F l = .Lt`），该命题即可顺利成立。
请完成证明：
-/

theorem lower_letter_lowers (l : Letter) (h : letter_comparison .F l = .Lt) :
    letter_comparison (lower_letter l) l = .Lt := by
  sorry

/-!
#### ⭐️⭐️ 练习题：lower_grade (2 星，标准)

请实现完整成绩降低一档的函数：
- A+ 降为 A；A 降为 A-；A- 降为 B+；
- 最低成绩为 F-，降低 F- 依然为 F-。
-/

def lower_grade (g : Grade) : Grade :=
  match g with
  | .grade l m =>
    match m with
    | .Plus    => .grade l .Natural
    | .Natural => .grade l .Minus
    | .Minus   =>
      match l with
      | .F => .grade .F .Minus
      | _  => .grade (lower_letter l) .Plus

-- 单元测试示例
theorem lower_grade_A_Plus : lower_grade (.grade .A .Plus) = .grade .A .Natural := by rfl
theorem lower_grade_A_Natural : lower_grade (.grade .A .Natural) = .grade .A .Minus := by rfl
theorem lower_grade_A_Minus : lower_grade (.grade .A .Minus) = .grade .B .Plus := by rfl
theorem lower_grade_B_Plus : lower_grade (.grade .B .Plus) = .grade .B .Natural := by rfl
theorem lower_grade_F_Natural : lower_grade (.grade .F .Natural) = .grade .F .Minus := by rfl
theorem lower_grade_twice : lower_grade (lower_grade (.grade .B .Minus)) = .grade .C .Natural := by rfl
theorem lower_grade_thrice : lower_grade (lower_grade (lower_grade (.grade .B .Minus))) = .grade .C .Minus := by rfl

theorem lower_grade_F_Minus : lower_grade (.grade .F .Minus) = .grade .F .Minus := by
  rfl

/-!
#### ⭐️⭐️⭐️ 练习题：lower_grade_lowers (3 星，标准)

证明：只要成绩初始高于 F-，执行 `lower_grade` 后成绩必然严格变低。
提示：对 `g` 和 `m` 分别进行 `cases` 展开，并结合之前证明过的引理 `letter_comparison_Eq`。
-/

theorem lower_grade_lowers (g : Grade)
    (h : grade_comparison (.grade .F .Minus) g = .Lt) :
    grade_comparison (lower_grade g) g = .Lt := by
  sorry

/-!
### 10.4 迟交政策形式化与性质证明

具体的迟交惩罚规则如下：
- 迟交 0 到 8 天：无惩罚；
- 迟交 9 到 16 天：降低 1 档（如 A+ => A, A- => B+）；
- 迟交 17 到 20 天：降低 2 档；
- 迟交 21 天及以上：降低 3 档（整整一个字母级别）。
-/

def apply_late_policy (late_days : Nat) (g : Grade) : Grade :=
  if (late_days <? 9) then g
  else if (late_days <? 17) then lower_grade g
  else if (late_days <? 21) then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g))

theorem apply_late_policy_unfold (late_days : Nat) (g : Grade) :
    apply_late_policy late_days g =
      (if (late_days <? 9) then g
      else if (late_days <? 17) then lower_grade g
      else if (late_days <? 21) then lower_grade (lower_grade g)
      else lower_grade (lower_grade (lower_grade g))) := by
  rfl

/-!
#### ⭐️⭐️ 练习题：no_penalty_for_mostly_on_time (2 星，标准)

证明：如果迟交天数不超过 8 天（即 `late_days <? 9 = true`），学生的成绩不受任何影响。
-/

theorem no_penalty_for_mostly_on_time (late_days : Nat) (g : Grade)
    (h : (late_days <? 9) = true) :
    apply_late_policy late_days g = g := by
  sorry

/-!
#### ⭐️⭐️ 练习题：graded_lowered_once / grade_lowered_once (2 星，标准)

证明：如果迟交天数在 9 到 16 天之间，成绩恰好被扣降一档。
-/

theorem grade_lowered_once (late_days : Nat) (g : Grade)
    (h1 : (late_days <? 9) = false)
    (h2 : (late_days <? 17) = true) :
    apply_late_policy late_days g = lower_grade g := by
  sorry

end LateDays

/- ================================================================== -/
/-! ## 11. 形式化挑战：二进制计数系统 (Binary Numerals) -/
/- ================================================================== -/

/-!
#### ⭐️⭐️⭐️ 练习题：binary (3 星，标准)

此前我们定义的皮亚诺自然数是一进制（Unary）的：数值 $n$ 由 $n$ 个嵌套的 `S` 构造子构成。
这种表示法在理论证明上极简优美，但在空间与时间复杂度上效率较低。

我们可以通过定义一个归纳数据类型 `Bin` 将自然数推广为更加高效的**二进制（Binary）计数体系**：
- `Z` 代表零；
- `B0 n` 代表将二进制数 `n` 左移一位并补零，对应数学数值 $2 \times n$；
- `B1 n` 代表将二进制数 `n` 左移一位并补一，对应数学数值 $2 \times n + 1$。

在这个表示中，**低位（低有效位 Least Significant Bit）在左，高位在右**。
例如：
- 十进制 `0` 对应 `Z`
- 十进制 `1` 对应 `B1 Z`
- 十进制 `2` 对应 `B0 (B1 Z)`
- 十进制 `3` 对应 `B1 (B1 Z)`
- 十进制 `4` 对应 `B0 (B0 (B1 Z))`

请补全下列二进制“加一运算” `incr` 与“二进制转十进制” `bin_to_nat` 的函数定义，
并确保随后的单元测试全部顺利得证：
-/

inductive Bin where
  | Z
  | B0 (n : Bin)
  | B1 (n : Bin)
  deriving Repr, DecidableEq

open Bin

/-- 二进制自增函数（加一运算） -/
def incr (m : Bin) : Bin :=
  match m with
  | Z    => B1 Z
  | B0 n => B1 n
  | B1 n => B0 (incr n)

/-- 将二进制数转换为十进制原生自然数 -/
def bin_to_nat (m : Bin) : Nat :=
  match m with
  | Z    => 0
  | B0 n => (bin_to_nat n) + (bin_to_nat n)
  | B1 n => (bin_to_nat n + 1) + (bin_to_nat n)

-- 单元测试套件：自增运算验证
theorem test_bin_incr1 : incr (B1 Z) = B0 (B1 Z) := by
  sorry

theorem test_bin_incr2 : incr (B0 (B1 Z)) = B1 (B1 Z) := by
  sorry

theorem test_bin_incr3 : incr (B1 (B1 Z)) = B0 (B0 (B1 Z)) := by
  sorry

-- 单元测试套件：数制转换验证
theorem test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2 := by
  sorry

theorem test_bin_incr5 : bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z) := by
  sorry

theorem test_bin_incr6 : bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z) := by
  sorry

/- ================================================================== -/
/-! ## 12. 章节总结与测试指引 (Testing Your Solutions) -/
/- ================================================================== -/

/-!
至此，我们已经完整走完了《软件基础》第一章《基础》（Basics）的全部理论与实践内容！

### 核心收获总结：
1. **函数式编程基石**：
   - 掌握了在 Lean 4 中通过归纳数据类型（`inductive`）从零构造枚举、布尔、元组与皮亚诺自然数；
   - 掌握了通过模式匹配（`match`）与结构化递归编写纯函数。
2. **基础证明策略工具箱**：
   - `rfl`：利用计算化简与定义等价性判定显然等式；
   - `intro`：将全称量词变量与命题假设引入局部上下文；
   - `rw`：利用已知等式假设或全局定理进行双向重写与子项代换；
   - `cases`：对有限状态与代数数据结构进行完备的分类讨论；
   - 方程编译器（Equation Compiler）：在 Lean 4 中直接用模式匹配写定理证明。

### 自动化构建与检验：
在终端执行：
```bash
lake build
```
若屏幕显示 `Build completed successfully`，且所有预留的习题均正常提示 `declaration uses 'sorry'`，
即代表你已经拥有了一份完全准备就绪的形式化作业！
现在，在 Neovim 中逐一寻找 `sorry`，踏上你的定理证明解谜之旅吧！
-/
