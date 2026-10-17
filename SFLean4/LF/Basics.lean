/-
  ======================================================================
  《软件基础》第一卷：逻辑基础 (Logical Foundations)
  第一章：基础 (Basics: Functional Programming in Lean 4)
  ======================================================================
-/

/-!
# 导言 (Introduction)

函数式编程的基石建立在简单直观的数学模型之上：
如果一个过程或方法**没有任何副作用**，那么除了效率考量之外，
我们只需理解它是如何将输入映射到输出的——即，它可以被看作是计算纯数学函数的具体方法。
这也是“函数式编程”中“函数”的第一层含义。程序与简单数学对象之间的直接联系，
既支持形式化的正确性证明，也支持对程序行为做出清晰严密的推理。

函数式编程的第二层含义是：它强调将函数作为**一等公民（First-class citizens）**——
即函数可以像普通数据一样作为参数传递给其他函数、作为返回值返回、或者存储在数据结构中。

在原版《软件基础》中，原书使用 Coq 及其核心语言 Gallina；而在本项目中，
我们将使用现代依赖类型论的先锋语言——**Lean 4**。
Lean 4 既是一个世界级的交互式定理证明器，同时也是一门现代、高性能、带垃圾回收与无开销抽象的通用编程语言。

本章的第一部分将介绍 Lean 4 核心函数式编程语言的基本要素；
第二部分将介绍用于证明程序性质的基础证明策略（Tactics）。
-/

/- ================================================================== -/
/-! ## 1. 数据与函数 (Data and Functions) -/
/- ================================================================== -/

/-!
### 1.1 枚举类型 (Enumerated Types)

Lean 4 与 Coq 一样，其最核心的内建类型系统非常小巧精炼。
与传统编程语言内置大量固定的原子类型（如布尔型、整型等）不同，
Lean 4 提供了一套极其通用的机制来**从零开始定义新的数据类型**——这便是**归纳类型（Inductive Types）**。
-/

/-- 定义星期几的枚举类型 `Day`。
    `deriving Repr, DecidableEq` 为其自动生成可打印字符串与可判定相等性支持。 -/
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
有了 `Day` 类型后，我们可以定义操作它的函数。
在 Lean 4 中，可以通过模式匹配（`match ... with`）或方程编译器（Equation Compiler）来定义函数。
注意：通过在构造子前加点（例如 `.monday`），Lean 4 会根据上下文期望的类型自动推导归属。
-/

/-- 计算下一个工作日的函数：周一到周四顺延，周五、周六、周日之后都是周一。 -/
def next_weekday (d : Day) : Day :=
  match d with
  | .monday    => .tuesday
  | .tuesday   => .wednesday
  | .wednesday => .thursday
  | .thursday  => .friday
  | .friday    => .monday
  | .saturday  => .monday
  | .sunday    => .monday

/-!
我们可以用 `#eval` 命令在编译期或交互环境中直接求值（类似于 Coq 中的 `Compute`）：
-/

#eval next_weekday .friday
-- 结果: Day.monday

#eval next_weekday (next_weekday .saturday)
-- 结果: Day.tuesday

/-!
### 1.2 通过计算进行证明 (Proof by Simplification / Reflexivity)

除了用 `#eval` 观察输出外，我们更希望能写下**形式化的断言**，并让编译器进行数学上的机器检验。
在 Lean 4 中，断言使用 `example`、`theorem` 或 `lemma` 来声明：
-/

/-- 断言：周六之后的第二个工作日是周二。
    在 Coq 中对应的证明为：`Proof. simpl. reflexivity. Qed.`
    在 Lean 4 中，直接使用 `rfl`（自反性 Reflexivity）策略即可化简并判定等式两侧完全一致！ -/
example : next_weekday (next_weekday .saturday) = .tuesday := by
  rfl

/- ================================================================== -/
/-! ## 2. 布尔类型 (Booleans) -/
/- ================================================================== -/

/-!
为了展示如何从零构建一切，我们在一个独立的命名空间中定义我们自己的布尔类型 `MyBool`。
Lean 4 自身拥有内置的 `Bool`，为了避免命名遮蔽（Shadowing）与歧义，
我们使用带前导点的构造子写法 `.true` 和 `.false`。
-/

namespace PlayGround

/-- 自定义布尔类型，包含两个构造子：`true` 和 `false`。 -/
inductive MyBool where
  | true  : MyBool
  | false : MyBool
  deriving Repr, DecidableEq

/-- 逻辑非（negb） -/
def negb (b : MyBool) : MyBool :=
  match b with
  | .true  => .false
  | .false => .true

/-- 逻辑与（andb） -/
def andb (b1 b2 : MyBool) : MyBool :=
  match b1 with
  | .true  => b2
  | .false => .false

/-- 逻辑或（orb） -/
def orb (b1 b2 : MyBool) : MyBool :=
  match b1 with
  | .true  => .true
  | .false => b2

/-- 为我们自定义的布尔运算引入直观的中缀符号表示 -/
infixl:35 " &&* " => andb
infixl:30 " ||* " => orb

-- 单元测试示例（Truth Table 验证）
example : (.true &&* .false) = .false := by rfl
example : (.false ||* .true) = .true  := by rfl

/-!
#### ⭐️ 练习题：nandb (1 星，标准)

“与非门”（NAND）运算：当且仅当输入的两个参数不全为 `true` 时返回 `true`。
请补全下列函数定义，并完成随后的定理证明（把 `sorry` 替换为真实的证明）。
-/

def nandb (b1 b2 : MyBool) : MyBool :=
  negb (b1 &&* b2)

-- 测试用例：在 Neovim 中打开，光标停在 sorry 处，右侧 Infoview 会显示待证目标！
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

三元逻辑与函数：仅当三个输入参数全部为 `true` 时返回 `true`，否则返回 `false`。
-/

def andb3 (b1 b2 b3 : MyBool) : MyBool :=
  b1 &&* (b2 &&* b3)

theorem test_andb31 : andb3 .true .true .true = .true := by
  sorry

theorem test_andb32 : andb3 .false .true .true = .false := by
  sorry

end PlayGround

/- ================================================================== -/
/-! ## 3. 自然数与皮亚诺算术 (Natural Numbers) -/
/- ================================================================== -/

/-!
自然数是形式化验证与程序语言理论中最基本、也最耐人寻味的结构之一。
我们通过皮亚诺（Peano）公理以归纳方式定义自然数：
- `O` 代表零；
- `S n` 代表 `n` 的后继（即 $n + 1$）。
-/

namespace PeanoPlayGround

inductive MyNat where
  | O : MyNat
  | S (n : MyNat) : MyNat
  deriving Repr, DecidableEq

open MyNat

/-- 前驱函数：0 的前驱仍为 0；(S n) 的前驱为 n -/
def pred (n : MyNat) : MyNat :=
  match n with
  | O   => O
  | S m => m

/-- 自然数加法递归定义 -/
def add (n m : MyNat) : MyNat :=
  match n with
  | O   => m
  | S p => S (add p m)

/-- 自然数乘法递归定义 -/
def mult (n m : MyNat) : MyNat :=
  match n with
  | O   => O
  | S p => add m (mult p m)

infixl:65 " +* " => add
infixl:70 " ** " => mult

example : (S (S O)) +* (S O) = S (S (S O)) := by rfl

end PeanoPlayGround

/- ================================================================== -/
/-! ## 4. 证明策略：重写与分类讨论 (Rewriting and Case Analysis) -/
/- ================================================================== -/

/-!
### 4.1 通过重写证明 (Proof by Rewriting)

并非所有定理都能单靠 `rfl`（计算展开）就直接解决。
当定理中包含前提假设（Hypotheses）时，我们需要：
1. 用 `intro` 策略将前提或全称量词引入到上下文中；
2. 用 `rw [h]` 策略将已知等式假设 `h` 代入替换目标中的对应项。
-/

theorem plus_id_example (n m : Nat) (h : n = m) : n + n = m + m := by
  -- 将假设 h : n = m 应用于目标，将目标中的 n 全部替换为 m
  rw [h]

/-!
### 4.2 通过分类讨论证明 (Proof by Case Analysis)

当一个变量是有限状态的归纳类型（例如布尔型 `MyBool`，只有 `true` 和 `false` 两种可能），
我们无法直接用 `rfl` 证明通用命题，因为此时变量的值是未知的。
此时我们可以使用 `cases` 策略对变量的所有可能构造进行枚举分流讨论：
-/

open PlayGround

/-- 双重否定律：对任意布尔值 b，两次取反后仍为 b。
    在 Coq 中对应的证明是：`intros b. destruct b. - reflexivity. - reflexivity.`
    在 Lean 4 中，`cases b with | true => ... | false => ...` 极度清晰直观！ -/
theorem negb_involutive (b : MyBool) : negb (negb b) = b := by
  cases b with
  | true  => rfl
  | false => rfl

/-- 练习：逻辑与与自身具有幂等性：`b &&* b = b` -/
theorem andb_idempotent (b : MyBool) : (b &&* b) = b := by
  cases b with
  | true  => rfl
  | false => rfl

/-!
#### ⭐️ 练习题：andb_true_r (1 星，标准)

请证明：对任意布尔值 `b`，`b &&* .true = b`。
提示：对 `b` 进行分类讨论（`cases b with | true => ... | false => ...`）。
-/
theorem andb_true_r (b : MyBool) : (b &&* .true) = b := by
  sorry

/-!
#### ⭐️ 练习题：andb_eq_orb (2 星，标准)

请证明：如果 `(b &&* c) = (b ||* c)`，那么必有 `b = c`。
提示：你需要对 `b` 和 `c` 分别进行分类讨论。
-/
theorem andb_eq_orb (b c : MyBool) (h : (b &&* c) = (b ||* c)) : b = c := by
  sorry
