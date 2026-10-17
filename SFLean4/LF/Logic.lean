import SFLean4.LF.Basics
import SFLean4.LF.Induction
import SFLean4.LF.Lists
import SFLean4.LF.Poly
import SFLean4.LF.Tactics

/-!
# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)

## 第六章：逻辑学基础 (Logic: Logic in Coq / Lean 4)

在前几章中，我们已经接触了形式化断言（Propositions，即命题）以及为断言提供严谨证据（Proofs，即证明）的多种基础方式。
特别是，我们深入使用了：
- 等式命题（如 `e1 = e2`）；
- 蕴含命题（如 `P → Q`）；
- 全称量化命题（如 `∀ x, P x`）。

在本章中，我们将系统探讨数学逻辑学中的核心逻辑联结词：
1. **合取 (Conjunction - `∧` / `And`)**；
2. **析取 (Disjunction - `∨` / `Or`)**；
3. **否定 (Negation - `¬` / `Not`) 与假命题 (`False`)**；
4. **真命题 (`True`)**；
5. **逻辑等价 (Logical Equivalence - `↔` / `Iff`)**；
6. **存在量词 (Existential Quantification - `∃` / `Exists`)**。

此外，本章还将揭示依值类型论（Dependent Type Theory）与现代形式化逻辑的两大核心支柱：
- **柯里-霍华德同构 (Curry-Howard Isomorphism)**：命题即类型（Propositions-as-Types），证明即程序（Proofs-as-Programs）。定理可以像普通函数一样施加参数！
- **布尔计算与命题逻辑的对偶 (Booleans vs. Propositions)**：探索可判定性（Decidability）与布尔反射（Boolean Reflection）的巨大威能；
- **经典逻辑 vs. 构造性逻辑 (Classical vs. Constructive Logic)**：深入剖析排中律（Excluded Middle）与函数外延性（Functional Extensionality）在证明助手中的地位。
-/

namespace Logic

open Poly
open Poly.list
open Poly.prod
open Poly.option
open Tactics

/-- 皮亚诺后继记号别名，对齐原版 Coq 的 `S` -/
abbrev S := Nat.succ

/-- 自然数零记号别名，对齐原版 Coq 的 `O` -/
abbrev O := 0

/-- 自然数前驱函数别名，对齐原版 Coq 的 `pred` -/
abbrev pred := Nat.pred

/- ================================================================== -/
/-! ## 1. 命题是一等公民 (Propositions as First-Class Citizens) -/
/- ================================================================== -/

/-!
在 Lean 4 中，每一个良构（Well-formed）的表达式都具备其对应的类型。
逻辑断言亦不例外：任何我们在 Lean 4 中试图陈述或证明的命题，其类型均为 `Prop`（命题宇宙，Sort 0）。

我们可以通过 `#check` 指令直观检验命题的类型：
-/

#check (∀ n m : Nat, n + m = m + n)
-- 输出: ∀ (n m : Nat), n + m = m + n : Prop

#check 2 = 2
-- 输出: 2 = 2 : Prop

#check 3 = 2
-- 输出: 3 = 2 : Prop

#check ∀ n : Nat, n = 2
-- 输出: ∀ (n : Nat), n = 2 : Prop

/-!
请注意：**所有语法良构的断言其类型都是 `Prop`，无论它们在数学上究竟是真还是假！**
身为一个合法的命题是一回事；该命题是否可证（Provable）则是另一回事。

既然命题具有类型 `Prop`，它们就是计算世界中的**一等公民 (First-Class Entities)**，
可以像数字、列表和函数一样被赋值、命名、作为参数传递或作为函数的返回值。

例如，我们不仅可以在 `theorem` 或 `lemma` 中声明命题，还可以使用 `def` 为命题赋予名称：
-/

/-- 直接证明等式命题 -/
theorem plus_2_2_is_4 : 2 + 2 = 4 := by
  rfl

/-- 使用 `def` 将一个命题命名为常量标识符 -/
def plus_claim : Prop := 2 + 2 = 4

#check plus_claim
-- 输出: plus_claim : Prop

/-- 随后在定理陈述中直接使用该命题名称 -/
theorem plus_claim_is_true : plus_claim := by
  rfl

/-!
更进一步，我们可以定义**参数化命题 (Parameterized Propositions)**，即接受某种类型的参数并返回一个命题的函数。
在逻辑学中，这类函数被称为定义了其参数上的**性质 (Property)** 或**谓词 (Predicate)**。
-/

/-- 定义一个性质：断言给定的自然数等于 3 -/
def is_three (n : Nat) : Prop :=
  n = 3

#check is_three
-- 输出: is_three : Nat → Prop

/-- 定义单射函数（Injective Function）的抽象数学性质 -/
def injective {A B : Type} (f : A → B) : Prop :=
  ∀ x y : A, f x = f y → x = y

/-- 皮亚诺后继构造子是单射的 -/
theorem succ_inj : injective S := by
  intro x y h
  injection h

#check @Eq
-- 在 Lean 4 中，等号 `=` 本质上是多态二元归纳谓词 `Eq` 的中缀语法糖：
-- @Eq : {α : Sort u} → α → α → Prop

/- ================================================================== -/
/-! ## 2. 逻辑联结词 (Logical Connectives) -/
/- ================================================================== -/

/-!
### 2.1 合取 (Conjunction - `∧` / `And`)

命题 $A$ 与 $B$ 的**合取（逻辑与）**记作 $A \land B$（在 Lean 4 中为 `A ∧ B`，类型定义为 `And A B`），
表示断言“$A$ 与 $B$ 均成立”。

在证明目标形如 `A ∧ B` 时，我们可以使用 `constructor`（或 `apply And.intro`，或匿名构造子 `⟨..., ...⟩`）
将目标拆分为两个子目标：分别证明 $A$ 和证明 $B$。
-/

/-- 证明一个具体的合取目标 -/
theorem and_example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  constructor
  · rfl
  · rfl

/-- 亦可使用匿名构造子直接打包证据 -/
theorem and_example' : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  apply And.intro
  · rfl
  · rfl

/-!
#### 练习：2 星, standard (plus_is_O)
-/

/-- 两个自然数相加为零，则两者必然同时为零。
    提示：对 $n$ 或 $m$ 进行分类讨论 (`cases`)。 -/
theorem plus_is_O : ∀ n m : Nat, n + m = 0 → n = 0 ∧ m = 0 := by
  sorry

/-!
当假设中包含合取前提 $H : A \land B$ 时，我们使用模式匹配（`rcases H with ⟨HA, HB⟩` 或 `intro ⟨HA, HB⟩`）
来解包获得两个独立的命题假设：$HA : A$ 与 $HB : B$。
-/

/-- 解包合取假设以推导结论 -/
theorem and_example2 (n m : Nat) (h : n = 0 ∧ m = 0) : n + m = 0 := by
  rcases h with ⟨hn, hm⟩
  rw [hn, hm]

/-- 在引入参数的同时直接解构合取假设 -/
theorem and_example2' : ∀ n m : Nat, n = 0 ∧ m = 0 → n + m = 0 := by
  intro n m ⟨hn, hm⟩
  rw [hn, hm]

/-- 将前提作为两个分离的假设（柯里化形式） -/
theorem and_example2'' (n m : Nat) (hn : n = 0) (hm : m = 0) : n + m = 0 := by
  rw [hn, hm]

/-- 在中间证明步骤中生成并使用合取结论 -/
theorem and_example3 (n m : Nat) (h : n + m = 0) : n * m = 0 := by
  have ⟨hn, _⟩ := plus_is_O n m h
  rw [hn]
  rw [Nat.zero_mul]

/-- 合取的左投影律：从 `P ∧ Q` 提取 `P` -/
theorem proj1 (P Q : Prop) (hpq : P ∧ Q) : P := by
  rcases hpq with ⟨hp, _⟩
  exact hp

/-!
#### 练习：1 星, standard, optional (proj2)
-/

/-- 合取的右投影律：从 `P ∧ Q` 提取 `Q` -/
theorem proj2 (P Q : Prop) : P ∧ Q → Q := by
  sorry

/-- 合取交换律：证明合取关于参数对称 -/
theorem and_commut (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro ⟨hp, hq⟩
  exact ⟨hq, hp⟩

/-!
#### 练习：1 星, standard (and_assoc)
-/

/-- 合取结合律：证明三项嵌套合取的结合次序无关紧要。
    提示：注意嵌套模式解包 `⟨hp, ⟨hq, hr⟩⟩`。 -/
theorem and_assoc (P Q R : Prop) : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  sorry

#check And
-- 输出: And : Prop → Prop → Prop

/-!
### 2.2 析取 (Disjunction - `∨` / `Or`)

命题 $A$ 与 $B$ 的**析取（逻辑或）**写作 $A \lor B$（在 Lean 4 中为 `A ∨ B`，类型定义为 `Or A B`）。
当 $A$ 成立或 $B$ 成立（或二者皆成立）时，析取命题成立。

- 要**使用**上下文中的析取假设 $H : A \lor B$，我们进行分支讨论：`rcases H with HA | HB`；
- 要**证明**一个形如 $A \lor B$ 的析取目标，我们只需证明其中任意一侧成立：使用 `left`（即 `apply Or.inl`）或 `right`（即 `apply Or.inr`）。
-/

/-- 析取假设的分类讨论示例 -/
theorem factor_is_O (n m : Nat) (h : n = 0 ∨ m = 0) : n * m = 0 := by
  rcases h with hn | hm
  · rw [hn, Nat.zero_mul]
  · rw [hm, Nat.mul_zero]

/-- 析取的左引入规则 -/
theorem or_intro_l (A B : Prop) (ha : A) : A ∨ B := by
  left
  exact ha

/-- 任意自然数要么是 0，要么是其前驱的后继 -/
theorem zero_or_succ (n : Nat) : n = 0 ∨ n = S (pred n) := by
  cases n with
  | zero =>
    left
    rfl
  | succ n' =>
    right
    rfl

/-!
#### 练习：2 星, standard (mult_is_O)
-/

/-- 两个数相乘为零，则其中至少有一个为零。
    提示：对 $n$ 进行 `cases` 讨论；在 $n = n' + 1$ 分支中再对 $m$ 进行 `cases`。 -/
theorem mult_is_O (n m : Nat) : n * m = 0 → n = 0 ∨ m = 0 := by
  sorry

/-!
#### 练习：1 星, standard (or_commut)
-/

/-- 析取交换律：$P \lor Q \iff Q \lor P$ -/
theorem or_commut (P Q : Prop) : P ∨ Q → Q ∨ P := by
  sorry

/-!
### 2.3 伪命题与否定 (Falsehood and Negation - `¬` / `False`)

在直觉主义与构造性逻辑中，逻辑否定 $
eg P$（非 $P$）被**定义**为：
$$
eg P 	riangleq P 	o 	ext{False}$$
其中 `False` 是 Lean 4 / Coq 标准库中没有任何构造子的空归纳类型（Uninhabited Type）。
这意味着：断言“$P$ 不成立”，实质上就是声称“如果假定 $P$ 成立，就能构造出荒谬的矛盾（`False`）”。
-/

namespace NotPlayground

def not (P : Prop) : Prop := P → False

#check not
-- 输出: not : Prop → Prop

end NotPlayground

/-- 爆炸原理 (Principle of Explosion / Ex Falso Quodlibet)：
    从荒谬的矛盾假命题 `False` 可以推导出任意命题。 -/
theorem ex_falso_quodlibet (P : Prop) : False → P := by
  intro contra
  cases contra

/-!
#### 练习：2 星, standard, optional (not_implies_our_not)
-/

/-- 证明构造性逻辑中的否定蕴含了直观上的爆炸定义：¬P → ∀ Q, P → Q -/
theorem not_implies_our_not (P : Prop) : ¬P → (∀ Q : Prop, P → Q) := by
  sorry

/-!
不等号 `x ≠ y` 在 Lean 4 中正是 `¬(x = y)` 的记号别名：
-/

/-- 证明 0 不等于 1 -/
theorem zero_not_one : (0 : Nat) ≠ 1 := by
  intro contra
  contradiction

/-- 证明矛盾命题 `False` 本身必然是不成立的 -/
theorem not_False : ¬False := by
  intro h
  cases h

/-- 命题与其否定同时成立将导致矛盾，进而推导出任何结论 -/
theorem contradiction_implies_anything (P Q : Prop) : (P ∧ ¬P) → Q := by
  intro ⟨hp, hnp⟩
  contradiction

/-- 命题成立蕴含其双重否定成立（注意：在构造性逻辑中逆命题不无条件成立！） -/
theorem double_neg (P : Prop) : P → ¬¬P := by
  intro hp hnp
  exact hnp hp

/-!
#### 练习：2 星, advanced (double_neg_informal)

请给出定理 `double_neg`（即对于任意命题 `P`，`P → ¬¬P`）的非形式化数学证明。

**证明草稿（中文非形式化证明）**：
假设命题 $P$ 成立。我们要证明 $
eg
eg P$，根据否定的定义，这等价于证明 $(
eg P) 	o 	ext{False}$。
因此，我们进一步假设 $
eg P$ 成立，即假设 $P 	o 	ext{False}$。
将此蕴含假设应用于最开始的已知事实 $P$，即可得出矛盾 $	ext{False}$。
根据否定引入规则，由此证明了 $
eg
eg P$。
证毕。
-/

def manual_grade_for_double_neg_informal : Option (Nat × String) := none

/-!
#### 练习：1 星, standard, especially useful (contrapositive)
-/

/-- 逆否命题法则：原命题成立蕴含其逆否命题成立 -/
theorem contrapositive (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  sorry

/-!
#### 练习：1 星, standard (not_both_true_and_false)
-/

/-- 无矛盾律（矛盾律）：任何命题不能既真又假 -/
theorem not_both_true_and_false (P : Prop) : ¬(P ∧ ¬P) := by
  sorry

/-!
#### 练习：1 星, advanced (not_PNP_informal)

请用自然语言给出命题 `∀ P : Prop, ¬(P ∧ ¬P)`（无矛盾律）的非形式化证明。

**证明草稿（中文非形式化证明）**：
任取命题 $P$。我们要证明 $
eg(P \wedge 
eg P)$，根据否定的定义即证明 $(P \wedge 
eg P) 	o 	ext{False}$。
假设合取式 $P \wedge 
eg P$ 成立。
由合取消去律，我们同时拥有前提 $P$ 以及前提 $
eg P$（即 $P 	o 	ext{False}$）。
将假设 $
eg P$ 应用于假设 $P$，直接得出矛盾 $	ext{False}$。
因此原命题成立。
证毕。
-/

def manual_grade_for_not_PNP_informal : Option (Nat × String) := none

/-!
#### 练习：2 星, standard (de_morgan_not_or)
-/

/-- 德·摩根定律之一：析取的否定等于否定的合取 -/
theorem de_morgan_not_or (P Q : Prop) : ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  sorry

/-!
#### 练习：1 星, standard, optional (not_S_inverse_pred)
-/

/-- 证伪后继与前驱互为逆运算的全称断言（在自然数 0 上失效） -/
theorem not_S_pred_n : ¬(∀ n : Nat, S (pred n) = n) := by
  sorry

/-- 布尔值不等于 true 则必定等于 false -/
theorem not_true_is_false (b : Bool) (h : b ≠ true) : b = false := by
  cases b with
  | false => rfl
  | true => contradiction

/-- 使用 `exfalso` 策略将荒谬目标转化为 `False` -/
theorem not_true_is_false' (b : Bool) (h : b ≠ true) : b = false := by
  cases b with
  | false => rfl
  | true =>
    exfalso
    exact h rfl

/-!
### 2.4 真命题 (Truth - `True`)

与 `False` 相对，标准库定义了平凡恒真的命题 `True`，其唯一的构造子为 `True.intro`（常记作 `trivial`）。
-/

/-- `True` 命题是平凡自证的 -/
theorem True_is_true : True :=
  trivial

/-- 构造子判别谓词：将 0 映射为 True，正数映射为 False -/
def disc_fn (n : Nat) : Prop :=
  match n with
  | 0 => True
  | _ + 1 => False

/-- 无需使用 `contradiction`，纯手工通过 `disc_fn` 证明不同构造子不相等 -/
theorem disc_example (n : Nat) : ¬(0 = S n) := by
  intro contra
  have h : disc_fn 0 := trivial
  have h' : disc_fn (S n) := by
    rw [← contra]
    exact h
  exact h'

/-!
#### 练习：2 星, advanced, optional (nil_is_not_cons)
-/

/-- 列表构造子判别谓词 -/
def list_disc_fn (X : Type) (n : list X) : Prop :=
  match n with
  | nil => True
  | cons _ _ => False

/-- 不使用 `contradiction` / `injection` 策略，模仿 `disc_example` 证明空列表不等于非空列表 -/
theorem nil_is_not_cons (X : Type) (x : X) (xs : list X) : ¬(nil = x :: xs) := by
  sorry

/-!
### 2.5 逻辑等价 (Logical Equivalence - `↔` / `Iff`)

逻辑等价 $P \iff Q$（在 Lean 4 中为 `P ↔ Q`，类型 `Iff P Q`）本质上就是双向蕴含的合取：
$$(P 	o Q) \land (Q 	o P)$$
-/

namespace IffPlayground

def iff (P Q : Prop) : Prop := (P → Q) ∧ (Q → P)

end IffPlayground

/-- 逻辑等价的对称性 -/
theorem iff_sym (P Q : Prop) : (P ↔ Q) → (Q ↔ P) := by
  intro ⟨hab, hba⟩
  exact ⟨hba, hab⟩

/-- 布尔不等与布尔相等的逻辑等价 -/
theorem not_true_iff_false (b : Bool) : b ≠ true ↔ b = false := by
  constructor
  · intro h; exact not_true_is_false b h
  · intro h; rw [h]; intro contra; contradiction

/-- 顺向应用逻辑等价 -/
theorem apply_iff_example1 (P Q R : Prop) (hiff : P ↔ Q) (h : Q → R) : P → R := by
  intro hp
  exact h (hiff.mp hp)

/-- 逆向应用逻辑等价 -/
theorem apply_iff_example2 (P Q R : Prop) (hiff : P ↔ Q) (h : P → R) : Q → R := by
  intro hq
  exact h (hiff.mpr hq)

/-!
#### 练习：1 星, standard, optional (iff_properties)
-/

/-- 逻辑等价的自反性 -/
theorem iff_refl (P : Prop) : P ↔ P := by
  sorry

/-- 逻辑等价的传递性 -/
theorem iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  sorry

/-!
#### 练习：3 星, standard (or_distributes_over_and)
-/

/-- 析取对合取的分配律：$P \lor (Q \land R) \iff (P \lor Q) \land (P \lor R)$ -/
theorem or_distributes_over_and (P Q R : Prop) :
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry

/-!
### 2.6 Setoid 与逻辑等价重写 (Rewriting with `↔`)

在 Coq 中，使用 `↔` 进行目标重写需要专门引入 `Setoid` 库；
而在 Lean 4 中，得益于**命题外延性公理 (Propositional Extensionality - `propext`)**：
$$(P \iff Q) \implies P = Q$$
Lean 4 的 `rw` 策略原生支持直接对 `P ↔ Q` 进行替换重写！
-/

/-- 乘积为零充要条件 -/
theorem mul_eq_0 (n m : Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  · intro h; exact mult_is_O n m h
  · intro h; exact factor_is_O n m h

/-- 析取结合律的等价形式 -/
theorem or_assoc (P Q R : Prop) : P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R := by
  constructor
  · intro h
    rcases h with hp | hq | hr
    · left; left; exact hp
    · left; right; exact hq
    · right; exact hr
  · intro h
    rcases h with (hp | hq) | hr
    · left; exact hp
    · right; left; exact hq
    · right; right; exact hr

/-- 三项乘积为零的充要条件（展示链式 `rw` 逻辑等价式） -/
theorem mul_eq_0_ternary (n m p : Nat) :
    n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0 := by
  rw [mul_eq_0, mul_eq_0, or_assoc]

/-!
### 2.7 存在量词 (Existential Quantification - `∃` / `Exists`)

要断言存在某种元素 $x$ 使得性质 $P\ x$ 成立，我们使用存在量词 $\exists x, P\ x$（在 Lean 4 中写作 `∃ x, P x`）。
- 要**证明**存在量词目标，我们需要给出一个具体的见证者（Witness）$t$，并证明 $P\ t$ 成立（使用 `exists t` 或匿名构造子 `⟨t, ...⟩`）；
- 要**使用**上下文中的存在量词假设，我们通过模式匹配解构出见证者与证据：`rcases H with ⟨x, Hx⟩`。
-/

/-- 偶数的命题化定义：存在某个数使得其翻倍等于自身 -/
def Even (x : Nat) : Prop :=
  ∃ n : Nat, x = double n

#check Even
-- 输出: Even : Nat → Prop

/-- 证明 4 是偶数 -/
theorem four_is_Even : Even 4 := by
  dsimp [Even]
  exists 2

/-- 存在假设的解构与传递示例 -/
theorem exists_example_2 (n : Nat) (h : ∃ m, n = 4 + m) : ∃ o, n = 2 + o := by
  rcases h with ⟨m, hm⟩
  exists 2 + m
  rw [hm]
  omega

/-!
#### 练习：1 星, standard, especially useful (dist_not_exists)
-/

/-- 全称断言蕴含不存在反例：若对所有 x 性质均成立，则不存在反例 -/
theorem dist_not_exists (X : Type) (P : X → Prop) :
    (∀ x, P x) → ¬(∃ x, ¬P x) := by
  sorry

/-!
#### 练习：2 星, standard (dist_exists_or)
-/

/-- 存在量词对析取满足分配律 -/
theorem dist_exists_or (X : Type) (P Q : X → Prop) :
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry

/-!
#### 练习：3 星, standard, optional (leb_plus_exists)
-/

/-- 小于等于的布尔判定蕴含存在加法差值 -/
theorem leb_plus_exists (n m : Nat) (h : (n <=? m) = true) :
    ∃ x, m = n + x := by
  sorry

/-- 存在加法差值蕴含小于等于判定为 true -/
theorem plus_exists_leb (n m : Nat) (h : ∃ x, m = n + x) :
    (n <=? m) = true := by
  sorry

/- ================================================================== -/
/-! ## 3. 用命题进行编程 (Programming with Propositions) -/
/- ================================================================== -/

/-!
既然命题也是一等公民，我们完全可以编写接受普通数据并递归构造复合命题的**命题值递归函数**！
最经典的范例莫过于定义某个元素 $x$ 是否出现在多态列表 $l$ 中的谓词 `In`：
- 若 $l$ 为空列表 `nil`，则没有元素包含其中，结果为 `False`；
- 若 $l$ 为 `x' :: l'`，则当 $x' = x$ 时成立，或者当 $x$ 属于剩余列表 $l'$ 时成立。
-/

/-- 列表隶属度谓词：递归构造嵌套析取命题 -/
def In {A : Type} (x : A) : list A → Prop
  | nil => False
  | x' :: l' => x' = x ∨ In x l'

/-- 具体列表上的 `In` 判定展开为嵌套析取 -/
theorem In_example_1 : In 4 [1; 2; 3; 4; 5] := by
  dsimp [In]
  right; right; right; left; rfl

/-- 利用空分支进行模式匹配排除矛盾分支 -/
theorem In_example_2 (n : Nat) (h : In n [2; 4]) : ∃ n', n = 2 * n' := by
  dsimp [In] at h
  rcases h with h1 | h2 | h3
  · exists 1
    rw [← h1]
  · exists 2
    rw [← h2]
  · cases h3

/-- 映射保持列表隶属度：若 x 在 l 中，则 f x 在 map f l 中 -/
theorem In_map (A B : Type) (f : A → B) (l : list A) (x : A) (h : In x l) :
    In (f x) (map f l) := by
  induction l with
  | nil =>
    cases h
  | cons x' l' ih =>
    dsimp [In, map] at *
    rcases h with h1 | h2
    · left
      rw [h1]
    · right
      exact ih h2

/-!
#### 练习：2 星, standard (In_map_iff)
-/

/-- 映射后列表的元素隶属度充要条件 -/
theorem In_map_iff (A B : Type) (f : A → B) (l : list A) (y : B) :
    In y (map f l) ↔ ∃ x, f x = y ∧ In x l := by
  sorry

/-!
#### 练习：2 星, standard (In_app_iff)
-/

/-- 列表拼接后元素隶属度的充要条件 -/
theorem In_app_iff (A : Type) (l l' : list A) (a : A) :
    In a (l ++ l') ↔ In a l ∨ In a l' := by
  sorry

/-!
#### 练习：3 星, standard, especially useful (All)

类比 `In` 的定义，编写一个递归函数 `All`，判定某个性质 $P$ 是否对列表 $l$ 中的每一个元素均成立。
并证明其与全称量化定义的等价性引理 `All_In`。
-/

/-- 递归判定列表所有元素是否均满足性质 P -/
def All {T : Type} (P : T → Prop) : list T → Prop
  | nil => True
  | x :: l' => P x ∧ All P l'

/-- 证明 All 与全称量化的充要等价性 -/
theorem All_In (T : Type) (P : T → Prop) (l : list T) :
    (∀ x, In x l → P x) ↔ All P l := by
  sorry

/-!
#### 练习：2 星, standard, optional (combine_odd_even)
-/

/-- 奇数与偶数性质组合器：当 n 为奇数时返回 Podd n，否则返回 Peven n -/
def combine_odd_even (Podd Peven : Nat → Prop) : Nat → Prop :=
  fun n => if odd n then Podd n else Peven n

theorem combine_odd_even_intro (Podd Peven : Nat → Prop) (n : Nat)
    (hodd : odd n = true → Podd n)
    (heven : odd n = false → Peven n) :
    combine_odd_even Podd Peven n := by
  sorry

theorem combine_odd_even_elim_odd (Podd Peven : Nat → Prop) (n : Nat)
    (h : combine_odd_even Podd Peven n)
    (hodd : odd n = true) :
    Podd n := by
  sorry

theorem combine_odd_even_elim_even (Podd Peven : Nat → Prop) (n : Nat)
    (h : combine_odd_even Podd Peven n)
    (heven : odd n = false) :
    Peven n := by
  sorry

/- ================================================================== -/
/-! ## 4. 将定理应用于参数 (Applying Theorems to Arguments) -/
/- ================================================================== -/

/-!
在依值类型论中，**定理即类型，证明即程序（Curry-Howard Isomorphism）**。
一个普遍全称量化的定理（如 `∀ n m, n + m = m + n`）实际上就是一个接受参数并返回特定类型证明项的**函数**！

这意味着，我们不仅可以在证明策略中使用定理，甚至可以直接像给函数传参一样，将具体的数值或前提假设传递给定理！
-/

#check add_comm
-- 输出: add_comm (n m : Nat) : n + m = m + n

#check plus_id_example
-- 输出: plus_id_example (n m : Nat) (h : n = m) : n + n = m + m

/-- 尝试使用简单重写证明三项加法结合律（原版 Coq 中因循环重写而 Abort）：
    在 Lean 4 中我们保留此声明并以 `sorry` 演示该受阻尝试。 -/
theorem add_comm3 (x y z : Nat) : x + (y + z) = (z + y) + x := by
  -- rw [Nat.add_comm]
  -- rw [Nat.add_comm] -- 循环往复，回到了原点！
  sorry

/-- 方案二：使用 `have` 显式断言并重写局部结合律 -/
theorem add_comm3_take2 (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [Nat.add_comm x (y + z)]
  have h : y + z = z + y := by rw [Nat.add_comm]
  rw [h]

/-- 方案三：直接为定理提供特定参数进行具现化（函数式应用） -/
theorem add_comm3_take3 (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [Nat.add_comm x (y + z)]
  rw [Nat.add_comm y z]

/-- 方案四：在两侧重写中均完全具现化参数 -/
theorem add_comm3_take4 (x y z : Nat) : x + (y + z) = (z + y) + x := by
  rw [Nat.add_comm x (y + z)]
  rw [Nat.add_comm y z]

/-- 列表非空引理：包含元素的列表必定不等于空列表 -/
theorem in_not_nil (A : Type) (x : A) (l : list A) (h : In x l) : l ≠ nil := by
  intro hl
  rw [hl] at h
  cases h

/-- 尝试直接 apply in_not_nil（原版 Coq 中因无法推断未出现在结论中的 witness x 而 Fail 并 Abort）：
    在 Lean 4 中保留此声明并以 `sorry` 演示。 -/
theorem in_not_nil_42 (l : list Nat) (h : In 42 l) : l ≠ nil := by
  -- apply in_not_nil -- 报错：无法推断实参 x
  sorry

/-- 具现化技巧 1：显式指定被隐式量化的参数命名 -/
theorem in_not_nil_42_take2 (l : list Nat) (h : In 42 l) : l ≠ nil := by
  apply in_not_nil (x := 42)
  exact h

/-- 具现化技巧 2：像函数一样直接传参应用 -/
theorem in_not_nil_42_take3 (l : list Nat) (h : In 42 l) : l ≠ nil := by
  exact in_not_nil Nat 42 l h

/-- 具现化技巧 3：利用 `@` 前缀显式提供所有类型参数与实参 -/
theorem in_not_nil_42_take4 (l : list Nat) (h : In 42 l) : l ≠ nil := by
  apply @in_not_nil Nat 42
  exact h

/-- 具现化技巧 4：将假设直接作为参数传给引理 -/
theorem in_not_nil_42_take5 (l : list Nat) (h : In 42 l) : l ≠ nil := by
  exact in_not_nil _ _ _ h

/-- 综合运用定理函数式应用的大型范例 -/
theorem lemma_application_ex {n : Nat} {ns : list Nat}
    (h : In n (map (fun m => m * 0) ns)) : n = 0 := by
  have h1 := (In_map_iff Nat Nat (fun m => m * 0) ns n).mp h
  rcases h1 with ⟨m, hm, _⟩
  rw [Nat.mul_zero] at hm
  exact hm.symm

/- ================================================================== -/
/-! ## 5. 处理可判定性质与布尔反射 (Working with Decidable Properties) -/
/- ================================================================== -/

/-!
在形式化系统中，我们有两种截然不同的方式表达断言：
1. **布尔计算 (`Bool`)**：只有 `true` 与 `false` 两种可能，算法可判定（Decidable），可在 `if-then-else` 中作为分支条件；
2. **命题逻辑 (`Prop`)**：包罗万象，支持不可判定命题，具有构造性证据，支持使用 `rw` 策略重写。

当一个性质恰好是可判定时，将其同时表述为布尔函数与命题谓词，并在二者之间自由穿梭，
便构成了极为强大的**证明反射 (Proof by Reflection)** 技术！
-/

/-- 布尔形式断言 42 是偶数（通过计算化简） -/
theorem even_42_bool : even 42 = true := by
  rfl

/-- 命题形式断言 42 是偶数（通过见证者 21 构造证据） -/
theorem even_42_prop : Even 42 := by
  dsimp [Even]
  exists 21

/-- 翻倍后的数必定是偶数 -/
theorem even_double (k : Nat) : even (double k) = true := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    dsimp [double]
    exact ih

/-!
#### 练习：3 星, standard (even_double_conv)
-/

/-- 自然数与偶数翻倍的互逆转换引理 -/
theorem even_double_conv (n : Nat) :
    ∃ k, n = if even n then double k else S (double k) := by
  sorry

/-- 核心定理：布尔偶数判定与命题偶数谓词完全等价（反射桥梁） -/
theorem even_bool_prop (n : Nat) : even n = true ↔ Even n := by
  constructor
  · intro h
    rcases even_double_conv n with ⟨k, hk⟩
    rw [hk, h]
    dsimp
    exists k
  · intro ⟨k, hk⟩
    rw [hk]
    apply even_double

/-- 布尔相等与命题相等的等价性 -/
theorem eqb_eq (n1 n2 : Nat) : (n1 =? n2) = true ↔ n1 = n2 := by
  constructor
  · intro h; exact eqb_true n1 n2 h
  · intro h; rw [h]; apply eqb_refl

/-- 借助布尔反射检验素偶数 -/
def is_even_prime (n : Nat) : Bool :=
  if (n =? 2) then true else false

set_option maxRecDepth 20000

/-- 手工给出 500 次递归见证者（在 Lean 4 中需放宽递归深度限制） -/
theorem even_1000 : Even 1000 := by
  exists 500

/-- 通过布尔计算一瞬间自反得证 -/
theorem even_1000' : even 1000 = true := by
  rfl

/-- 借助布尔反射直接证明命题偶数，免去手动枚举 500 的烦恼！ -/
theorem even_1000'' : Even 1000 := by
  apply (even_bool_prop 1000).mp
  rfl

/-- 布尔否定的平凡自反证明 -/
theorem not_even_1001 : even 1001 = false := by
  rfl

/-- 利用反射迅速证明命题否定 -/
theorem not_even_1001' : ¬(Even 1001) := by
  rw [← even_bool_prop]
  intro h
  contradiction

/-- 将布尔相等转化为命题等式以便重写 -/
theorem plus_eqb_example (n m p : Nat) (h : (n =? m) = true) :
    (((n + p) =? (m + p)) = true) := by
  rw [eqb_eq] at h
  rw [h]
  rw [eqb_eq]

/-!
#### 练习：2 星, standard (logical_connectives)
-/

/-- 布尔与与命题合取的反射关联 -/
theorem andb_true_iff (b1 b2 : Bool) :
    (b1 && b2) = true ↔ b1 = true ∧ b2 = true := by
  sorry

/-- 布尔或与命题析取的反射关联 -/
theorem orb_true_iff (b1 b2 : Bool) :
    (b1 || b2) = true ↔ b1 = true ∨ b2 = true := by
  sorry

/-!
#### 练习：1 星, standard (eqb_neq)
-/

/-- 布尔不等与命题否定的反射关联 -/
theorem eqb_neq (x y : Nat) :
    (x =? y) = false ↔ x ≠ y := by
  sorry

/-!
#### 练习：3 星, standard (eqb_list)
-/

/-- 列表结构等价判定函数 -/
def eqb_list {A : Type} (eqb : A → A → Bool) : list A → list A → Bool
  | nil, nil => true
  | nil, cons _ _ => false
  | cons _ _, nil => false
  | cons x1 l1', cons x2 l2' => (eqb x1 x2) && (eqb_list eqb l1' l2')

/-- 证明元素等价可判定性提升至列表等价可判定性 -/
theorem eqb_list_true_iff (A : Type) (eqb : A → A → Bool)
    (heqb : ∀ a1 a2, eqb a1 a2 = true ↔ a1 = a2) (l1 l2 : list A) :
    eqb_list eqb l1 l2 = true ↔ l1 = l2 := by
  sorry

/-!
#### 练习：2 星, standard, especially useful (All_forallb)
-/

/-- 检验列表中所有元素是否均满足布尔测试（自包含定义） -/
def forallb {X : Type} (test : X → Bool) : list X → Bool
  | nil => true
  | x :: l' => (test x) && (forallb test l')

/-- 证明布尔过滤器 forallb 与命题谓词 All 的充要反射关系 -/
theorem forallb_true_iff (X : Type) (test : X → Bool) (l : list X) :
    forallb test l = true ↔ All (fun x => test x = true) l := by
  sorry

/- ================================================================== -/
/-! ## 6. 证明助手的元逻辑 (The Logic of Coq / Lean 4) -/
/- ================================================================== -/

/-!
### 6.1 函数外延性 (Functional Extensionality)

在普通数学中，如果两个函数在每一个输入上都产生相同的输出，则这两个函数就是相等的：
$$(orall x, f\ x = g\ x) \implies f = g$$
这被称为**函数外延性原理 (Functional Extensionality)**。

在某些极简单的情况下，若两个函数能直接化简为相同表达式，则无需公理即可通过 `rfl` 证明相等：
-/

/-- 两个由于定义性计算直接等价的匿名函数 -/
theorem function_equality_ex1 :
    (fun x : Nat => 3 + x) = (fun x => (pred 4) + x) := by
  rfl

/-- 演示定义性等价受阻：(fun x => x + 1) 与 (fun x => 1 + x) 无法通过简单 rfl 得证 -/
theorem function_equality_ex2_failed :
    (fun x : Nat => x + 1) = (fun x => 1 + x) := by
  -- rfl -- 报错：无法直接化简相等
  sorry

/-- 函数外延性公理：在 Lean 4 中内建为核心公理 `funext` -/
theorem functional_extensionality {X Y : Type} {f g : X → Y}
    (h : ∀ x : X, f x = g x) : f = g :=
  funext h

/-- 利用函数外延性公理顺利证明两函数相等 -/
theorem function_equality_ex2 :
    (fun x : Nat => x + 1) = (fun x => 1 + x) := by
  apply functional_extensionality
  intro x
  rw [Nat.add_comm]

/-!
#### 练习：4 星, standard (tr_rev_correct)
-/

/-- 尾递归辅助拼接翻转函数 -/
def rev_append {X : Type} : list X → list X → list X
  | nil, l2 => l2
  | x :: l1', l2 => rev_append l1' (x :: l2)

/-- 基于尾递归的线性时间翻转函数 -/
def tr_rev {X : Type} (l : list X) : list X :=
  rev_append l nil

/-- 尾递归拼接引理 -/
theorem rev_append_nil (X : Type) (l1 l2 : list X) :
    rev_append l1 l2 = rev_append l1 nil ++ l2 := by
  sorry

/-- 证明尾递归翻转与朴素翻转函数在外延意义上等价 -/
theorem tr_rev_correct (X : Type) :
    @tr_rev X = @rev X := by
  sorry

/-!
### 6.2 经典逻辑 vs. 构造性逻辑 (Classical vs. Constructive Logic)

在经典数学（如 ZFC 集合论）中，任何命题要么为真，要么为假，这被称为**排中律 (Law of the Excluded Middle)**：
$$orall P : 	ext{Prop},\ P \lor 
eg P$$

然而，在构造性逻辑（Constructive Logic）中，排中律并非逻辑公理！
因为在构造性哲学中，一个存在量词证明 $\exists x, P\ x$ 必须实质性给出一个具体的构造算法与见证者；
如果允许任意使用排中律，就会导致非构造性证明（即知道存在，却永远无法计算其具体值）。
-/

/-- 排中律断言的抽象形式化定义 -/
def excluded_middle : Prop := ∀ P : Prop, P ∨ ¬P

/-- 对于布尔可判定的命题，排中律是平凡成立的定理 -/
theorem restricted_excluded_middle (P : Prop) (b : Bool) (h : P ↔ b = true) :
    P ∨ ¬P := by
  cases b with
  | true =>
    left
    exact h.mpr rfl
  | false =>
    right
    intro hp
    have hbt : (false = true) := h.mp hp
    contradiction

/-- 自然数等式命题上的受限排中律（因为自然数相等是布尔可判定的） -/
theorem restricted_excluded_middle_eq (n m : Nat) :
    n = m ∨ n ≠ m := by
  apply restricted_excluded_middle (n = m) (n =? m)
  exact (eqb_eq n m).symm

/-!
#### 练习：3 星, standard (excluded_middle_irrefutable)
-/

/-- 排中律不可反驳定理：在纯构造性逻辑中，排中律的双重否定恒成立！ -/
theorem excluded_middle_irrefutable (P : Prop) :
    ¬¬(P ∨ ¬P) := by
  sorry

/-!
#### 练习：3 星, advanced (not_exists_dist)
-/

/-- 在假设排中律的前提下，证明存在量词否定的分配律 -/
theorem not_exists_dist (hem : excluded_middle) (X : Type) (P : X → Prop) :
    ¬(∃ x, ¬P x) → (∀ x, P x) := by
  sorry

/-!
#### 练习：5 星, standard, optional (classical_axioms)

本练习证明以下 5 种经典逻辑表述与排中律 `excluded_middle` 是完全等价的：
1. 皮尔士定律 (Peirce's Law)；
2. 双重否定消除律 (Double Negation Elimination)；
3. 德·摩根否定合取律 (De Morgan: Not-And of Nots)；
4. 蕴含转换为析取 (Implication to Disjunction)；
5. 奇妙推论律 (Consequentia Mirabilis / 归谬原理)。
-/

/-- 皮尔士定律 -/
def peirce : Prop := ∀ P Q : Prop, ((P → Q) → P) → P

/-- 双重否定消除律 -/
def double_negation_elimination : Prop := ∀ P : Prop, ¬¬P → P

/-- 德·摩根否定合取律 -/
def de_morgan_not_and_not : Prop := ∀ P Q : Prop, ¬(¬P ∧ ¬Q) → P ∨ Q

/-- 蕴含转换为析取 -/
def implies_to_or : Prop := ∀ P Q : Prop, (P → Q) → (¬P ∨ Q)

/-- 奇妙推论律 -/
def consequentia_mirabilis : Prop := ∀ P : Prop, (¬P → P) → P

theorem peirce_double_negation_elimination :
    peirce → double_negation_elimination := by
  sorry

theorem double_negation_elimination_de_morgan_not_and_not :
    double_negation_elimination → de_morgan_not_and_not := by
  sorry

theorem de_morgan_not_and_not_implies_to_or :
    de_morgan_not_and_not → implies_to_or := by
  sorry

theorem implies_to_or_excluded_middle :
    implies_to_or → excluded_middle := by
  sorry

theorem excluded_middle_consequentia_mirabilis :
    excluded_middle → consequentia_mirabilis := by
  sorry

theorem consequentia_mirabilis_peirce :
    consequentia_mirabilis → peirce := by
  sorry

end Logic
