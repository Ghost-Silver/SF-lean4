import SFLean4.LF.Basics
import SFLean4.LF.Induction
import SFLean4.LF.Lists
import SFLean4.LF.Poly
import SFLean4.LF.Tactics
import SFLean4.LF.Logic
import SFLean4.LF.IndProp
import SFLean4.LF.Maps

set_option linter.defProp false
set_option linter.ambiguousOpen false

/-!
# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)

## 第九章：证明对象与柯里-霍华德同构 (ProofObjects: The Curry-Howard Correspondence)

> “算法是证明的计算内涵。” —— 罗伯特·哈珀 (Robert Harper)

在前几章的学习中，我们接触了两套看似平行的机制：
1. **函数式编程世界**：用归纳数据类型（如 `Nat`、`list`）与递归函数定义数据结构与算法；
2. **形式化逻辑证明世界**：用归纳命题（如 `ev`、`le`）、蕴含（`→`）与全称量词（`∀`）声明性质，并用策略（Tactics，如 `apply`、`intro`、`cases`）完成证明。

我们习惯性地把这两者区分为“编写程序”与“推导证明”。
然而在基于依赖类型论的证明助手（如 Lean 4 与 Coq）中，这两者本质上是**完全同一的**！
- 关键字 `inductive` 既用于声明数据类型，也用于声明逻辑谓词；
- 箭头 `→` 既表示程序函数的输入输出映射，也表示逻辑推导中的“前件蕴含后件”；
- 冒号 `:` 既读作“具有类型”（`x : Nat`），也读作“是该命题的证明证据”（`h : ev 4`）。

这一在类型与命题、程序与证明之间的深刻对应，就是计算机科学与数理逻辑中最著名的里程碑之一：
**柯里-霍华德同构（Curry-Howard Correspondence，或 Propositions-as-Types / Proofs-as-Programs）**！

---

### 柯里-霍华德字典 (The Curry-Howard Dictionary)

| 逻辑概念 (Logic) | 类型论 / 计算概念 (Type Theory / Computation) | Lean 4 语法表示 |
| :--- | :--- | :--- |
| **命题 (Proposition)** | **类型 (Type / `Prop`)** | `ev 4 : Prop` |
| **证明证据 (Proof / Evidence)** | **程序项 (Term / Value)** | `ev.ev_SS 2 (ev.ev_SS 0 ev.ev_0)` |
| **蕴含证明 ($P → Q$)** | **高阶函数 (Function)** | `fun (hp : P) => ... : Q` |
| **合取 / 并且 ($P ∧ Q$)** | **数对 / 乘积类型 (Pair / Product)** | `⟨hp, hq⟩` (`Prod P Q`) |
| **析取 / 或者 ($P ∨ Q$)** | **和类型 (Sum Type / Either)** | `Or.inl hp` / `Or.inr hq` |
| **全称量词 ($∀ x : A, P x$)** | **依赖函数类型 (Dependent Function / $\Pi$-Type)** | `(x : A) → P x` |
| **存在量词 ($∃ x : A, P x$)** | **依赖数对类型 (Dependent Pair / $\Sigma$-Type)** | `⟨witness, proof⟩` |
| **真命题 (`True`)** | **单元素单位类型 (Unit Type)** | `True.intro` (`trivial`) |
| **假命题 / 荒谬 (`False`)** | **空类型 (Empty Type / Void)** | 无构造子，`nomatch contra` |
| **等式命题 ($x = y$)** | **等式归纳族 (Identity Type)** | `rfl` (`Eq.refl x`) |

---

### 本章核心学习目标：
1. **揭秘策略背后的真相**：理解交互式策略（`apply`, `intro`, `cases`）本质上是在后台逐步合成显式函数项（Proof Objects）；
2. **逻辑联结词的归纳本质**：通过构造子深入剖析 `and`、`or`、`ex`、`True`、`False` 与 `eq` 的归纳定义；
3. **纯函数项证明实战**：脱离策略模式，直接用模式匹配（`match`）与 Lambda 抽象（`fun`）手写纯函数证明项；
4. **元逻辑深化**：掌握莱布尼茨相等性（Leibniz Equality）、命题外延性公理（Propositional Extensionality）及其蕴含的**证明无关性 (Proof Irrelevance)**。
-/

namespace ProofObjects

/- ================================================================== -/
/-! ## 1. 证明项即一等公民值 (Proof Terms as First-Class Values) -/
/- ================================================================== -/

/-- 偶数归纳谓词的微缩复现 -/
inductive ev : Nat → Prop where
  | ev_0 : ev 0
  | ev_SS (n : Nat) (H : ev n) : ev (n + 2)

/-!
### 1.1 构造证据树 (Building the Evidence Tree)

在第七章中，我们用如下策略脚本证明了 4 是偶数：
-/

theorem ev_4 : ev 4 := by
  apply ev.ev_SS
  apply ev.ev_SS
  exact ev.ev_0

/-- 通过 apply 显式提供证明对象参数 -/
theorem ev_4' : ev 4 := by
  exact (ev.ev_SS 2 (ev.ev_SS 0 ev.ev_0))

/-- 再次演示逐步应用 -/
theorem ev_4'' : ev 4 := by
  apply ev.ev_SS
  apply ev.ev_SS
  exact ev.ev_0

/-- 完全脱离策略，直接将证明写为常量定义（Proof Object Term） -/
def ev_4''' : ev 4 :=
  ev.ev_SS 2 (ev.ev_SS 0 ev.ev_0)

/-!
#### 练习：2 星, standard (eight_is_even)
-/

/-- 策略证明 8 是偶数 -/
theorem ev_8 : ev 8 := by
  sorry

/-- 显式函数项证明 8 是偶数 -/
def ev_8' : ev 8 :=
  sorry

/- ================================================================== -/
/-! ## 2. 量词、蕴含与函数 (Quantifiers, Implications, and Functions) -/
/- ================================================================== -/

/-!
命题间的蕴含关系 `P → Q` 并不需要内置新的语法机制：
它不过是依赖全称量词 `∀ (_ : P), Q` 在后件不依赖于前件具体证据名字时的退化简记！
-/

/-- 策略证明：若 n 为偶数，则 4 + n 亦为偶数 -/
theorem ev_plus4 : ∀ n, ev n → ev (4 + n) := by
  intro n H
  rw [Nat.add_comm]
  apply ev.ev_SS
  apply ev.ev_SS
  exact H

/-- 显式 Lambda 证据变换函数证明 ev_plus4' -/
def ev_plus4' : ∀ n, ev n → ev (4 + n) :=
  fun n H => Nat.add_comm n 4 ▸ ev.ev_SS (n + 2) (ev.ev_SS n H)

/-- 将参数置于冒号左侧的函数定义写法 -/
def ev_plus4'' (n : Nat) (H : ev n) : ev (4 + n) :=
  Nat.add_comm n 4 ▸ ev.ev_SS (n + 2) (ev.ev_SS n H)

/-- 显式给出证据参数名的全称命题 -/
def ev_plus2 : Prop :=
  ∀ n, ∀ (_ : ev n), ev (n + 2)

/-- 使用匿名占位符下划线的等价命题声明 -/
def ev_plus2' : Prop :=
  ∀ n, ∀ (_ : ev n), ev (n + 2)

/-- 最自然的常规箭头表示 -/
def ev_plus2'' : Prop :=
  ∀ n, ev n → ev (n + 2)

/- ================================================================== -/
/-! ## 3. 用策略编写普通程序 (Programming with Tactics) -/
/- ================================================================== -/

/-!
既然可以用写程序的方式写证明，那么反过来：可以用证明策略来写普通程序吗？
答案是毫无疑问的！
下面的加一函数展示了在程序定义中进入策略模式直接构造数值：
-/

/-- 借助策略模式编写后继加一函数 -/
def add1 : Nat → Nat := by
  intro n
  exact n.succ

#eval add1 2
-- 输出: 3

/- ================================================================== -/
/-! ## 4. 逻辑联结词的归纳本质 (Logical Connectives as Inductive Types) -/
/- ================================================================== -/

namespace Props

/-!
### 4.1 合取即乘积类型 (Conjunction as Product)
-/

namespace And

/-- 逻辑合取归纳定义：拥有且仅拥有一个双参数构造子 -/
inductive and (P Q : Prop) : Prop where
  | conj : P → Q → and P Q

scoped notation:35 (priority := high) P:36 " /\\ " Q:35 => and P Q

/-- 策略投影证明 -/
theorem proj1' (P Q : Prop) (HPQ : and P Q) : P := by
  cases HPQ with
  | conj hp _ => exact hp

/-- 策略证明合取交换律 -/
theorem and_comm (P Q : Prop) : (and P Q) ↔ (and Q P) := by
  constructor
  · intro | and.conj hp hq => exact and.conj hq hp
  · intro | and.conj hq hp => exact and.conj hp hq

end And

open And

/-- 纯模式匹配手写投影函数 -/
def proj1'' (P Q : Prop) (HPQ : and P Q) : P :=
  match HPQ with
  | and.conj hp _ => hp

/-- 合取交换单向辅助函数 -/
def and_comm'_aux (P Q : Prop) (H : and P Q) : and Q P :=
  match H with
  | and.conj hp hq => and.conj hq hp

/-- 纯函数项构造合取双向等价 -/
def and_comm' (P Q : Prop) : (and P Q) ↔ (and Q P) :=
  ⟨and_comm'_aux P Q, and_comm'_aux Q P⟩

/-!
#### 练习：2 星, standard (conj_fact)
-/

/-- 显式函数项构造传递合取证据 -/
def conj_fact : ∀ P Q R, P ∧ Q → Q ∧ R → P ∧ R :=
  sorry

/-!
### 4.2 析取即和类型 (Disjunction as Sum)
-/

namespace Or

/-- 逻辑析取归纳定义：拥有左、右两个构造子 -/
inductive or (P Q : Prop) : Prop where
  | or_introl : P → or P Q
  | or_intror : Q → or P Q

scoped notation:30 (priority := high) P:31 " \\/ " Q:30 => or P Q

/-- 显式函数项左注入 -/
def inj_l (P Q : Prop) (HP : P) : or P Q :=
  or.or_introl HP

/-- 策略左注入 -/
theorem inj_l' (P Q : Prop) (HP : P) : or P Q := by
  exact or.or_introl HP

/-- 显式模式匹配消去析取（分支分类讨论） -/
def or_elim (P Q R : Prop) (HPQ : or P Q) (HPR : P → R) (HQR : Q → R) : R :=
  match HPQ with
  | or.or_introl hp => HPR hp
  | or.or_intror hq => HQR hq

/-- 策略模式下的析取消去（对应 cases/destruct） -/
theorem or_elim' (P Q R : Prop) (HPQ : or P Q) (HPR : P → R) (HQR : Q → R) : R := by
  cases HPQ with
  | or_introl hp => exact HPR hp
  | or_intror hq => exact HQR hq

end Or

/-!
#### 练习：2 星, standard (or_commut')
-/

/-- 纯函数项证明标准库析取的交换律 -/
def or_commut' : ∀ P Q, P ∨ Q → Q ∨ P :=
  sorry

/-!
### 4.3 存在量词即依赖数对 (Existential Quantification as Dependent Pair)
-/

namespace Ex

/-- 存在量词归纳定义：包含一个见证者 x 与命题 P x 的证据 -/
inductive ex {A : Type} (P : A → Prop) : Prop where
  | ex_intro : ∀ x : A, P x → ex P

end Ex

/-- 构造“存在一个偶数”的具体证据项（见证者选 4） -/
def some_nat_is_even : Ex.ex (fun n => ev n) :=
  Ex.ex.ex_intro 4 (ev.ev_SS 2 (ev.ev_SS 0 ev.ev_0))

/-!
#### 练习：2 星, standard (ex_ev_Sn)
-/

/-- 构造“存在一个数其后继为偶数”的证据（见证者选 1） -/
def ex_ev_Sn : Ex.ex (fun n => ev (n + 1)) :=
  sorry

/-- 对存在证据与析取证据进行双重嵌套模式匹配解构 -/
def dist_exists_or_term (X : Type) (P Q : X → Prop) :
    (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x) :=
  fun ⟨x, hpq⟩ =>
    match hpq with
    | Or.inl hp => Or.inl ⟨x, hp⟩
    | Or.inr hq => Or.inr ⟨x, hq⟩

/-!
#### 练习：2 星, standard (ex_match)
-/

/-- 纯函数项实现存在量词谓词变换 -/
def ex_match : ∀ (A : Type) (P Q : A → Prop),
    (∀ x, P x → Q x) → (∃ x, P x) → (∃ x, Q x) :=
  sorry

/-!
### 4.4 真与假 (True and False)
-/

/-- 恒真命题归纳定义：具有唯一无需前置条件的无信息构造子 -/
inductive True' : Prop where
  | I : True'

/-!
#### 练习：1 星, standard (p_implies_true)
-/

/-- 任意命题皆蕴含真 -/
def p_implies_true : ∀ P, P → True :=
  sorry

/-- 绝对荒谬归纳定义：具有 0 个构造子的空类型 -/
inductive False' : Prop

/-- 假蕴含零等于一（对 0 构造子类型匹配无需任何分支） -/
def false_implies_zero_eq_one : False → 0 = 1 :=
  fun contra => nomatch contra

/-!
#### 练习：1 星, standard (ex_falso_quodlibet')
-/

/-- 矛盾生万物（从荒谬推出任意断言） -/
def ex_falso_quodlibet' : ∀ P, False → P :=
  sorry

end Props

/- ================================================================== -/
/-! ## 5. 等式的归纳本质与莱布尼茨相等性 (Equality as Inductive Relation) -/
/- ================================================================== -/

namespace EqualityPlayground
open Poly
open Poly.list

/-- 等式关系的纯归纳定义：仅凭唯一自反构造子生成 -/
inductive eq {X : Type} : X → X → Prop where
  | eq_refl (x : X) : eq x x

scoped notation:50 (priority := high) x:51 " == " y:51 => eq x y

/-- 2 + 2 == 1 + 3 可直接由同个证据自反得证（归约至相同范式） -/
theorem four : (2 + 2 == 1 + 3) := eq.eq_refl 4
def four' : (2 + 2 == 1 + 3) := eq.eq_refl 4

/-- 列表单元素拼接自反证据项 -/
def singleton (X : Type) (x : X) :
    (Poly.list.nil ++ (x :: Poly.list.nil) == x :: Poly.list.nil) :=
  eq.eq_refl (x :: Poly.list.nil)

/-- 对等式证据 Heq 执行模式匹配，将两边端点统一为同一变量 -/
def eq_add (n1 n2 : Nat) (Heq : n1 == n2) : (n1 + 1 == n2 + 1) :=
  match Heq with
  | eq.eq_refl _ => eq.eq_refl (n1 + 1)

/-- 策略反演消去等式证据 -/
theorem eq_add' (n1 n2 : Nat) (Heq : n1 == n2) : (n1 + 1 == n2 + 1) := by
  cases Heq
  exact eq.eq_refl (n1 + 1)

/-!
#### 练习：2 星, standard (eq_cons)
-/

/-- 列表头尾同等提升引理的纯函数项证明 -/
def eq_cons : ∀ (X : Type) (h1 h2 : X) (t1 t2 : list X),
    (h1 == h2) → (t1 == t2) → (h1 :: t1 == h2 :: t2) :=
  sorry

/-!
#### 练习：2 星, standard (equality__leibniz_equality)
-/

/-- 归纳等式蕴含莱布尼茨等式：具有相同性质的个体完全不可区分 -/
theorem equality__leibniz_equality (X : Type) (x y : X)
    (Heq : x == y) (P : X → Prop) (h : P x) : P y := by
  sorry

/-!
#### 练习：2 星, standard (equality__leibniz_equality_term)
-/

/-- 纯函数项实现归纳等式到莱布尼茨等式的转换 -/
def equality__leibniz_equality_term (X : Type) (x y : X)
    (Heq : x == y) (P : X → Prop) (h : P x) : P y :=
  sorry

/-!
#### 练习：3 星, standard, optional (leibniz_equality__equality)
-/

/-- 莱布尼茨等式亦反向蕴含归纳等式（构造自反性质谓词） -/
theorem leibniz_equality__equality (X : Type) (x y : X)
    (H : ∀ P : X → Prop, P x → P y) : x == y := by
  sorry

end EqualityPlayground

/- ================================================================== -/
/-! ## 6. 纯函数项逻辑定理实战 (More Exercises) -/
/- ================================================================== -/

/-!
#### 练习：2 星, standard (and_assoc)
-/

/-- 合取结合律函数项 -/
def and_assoc : ∀ P Q R : Prop, P ∧ (Q ∧ R) → (P ∧ Q) ∧ R :=
  sorry

/-!
#### 练习：3 星, standard (or_distributes_over_and)
-/

/-- 析取对合取的分配律函数项 -/
def or_distributes_over_and : ∀ P Q R : Prop,
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
  sorry

/-!
#### 练习：3 星, standard (negations)
-/

/-- 双重否定引入 -/
def double_neg : ∀ P : Prop, P → ¬¬P :=
  sorry

/-- 矛盾导出任意性 -/
def contradiction_implies_anything : ∀ P Q : Prop, (P ∧ ¬P) → Q :=
  sorry

/-- 德摩根定律经典析取形式 -/
def de_morgan_not_or : ∀ P Q : Prop, ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  sorry

/-!
#### 练习：2 星, standard (currying)
-/

/-- 柯里化变换：将数对输入转化为连续单输入 -/
def curry : ∀ P Q R : Prop, ((P ∧ Q) → R) → (P → Q → R) :=
  sorry

/-- 反柯里化变换：将连续单输入转化为数对输入 -/
def uncurry : ∀ P Q R : Prop, (P → Q → R) → ((P ∧ Q) → R) :=
  sorry

/- ================================================================== -/
/-! ## 7. 命题外延性与证明无关性 (Proof Irrelevance) -/
/- ================================================================== -/

/-- 命题外延性公理断言：逻辑双向等价的命题即为相等的类型 -/
def propositional_extensionality : Prop :=
  ∀ (P Q : Prop), (P ↔ Q) → P = Q

/-!
#### 练习：1 星, advanced (pe_implies_or_eq)
-/

/-- 命题外延性蕴含析取交换律的类型等式 -/
theorem pe_implies_or_eq (PE : propositional_extensionality) (P Q : Prop) :
    (P ∨ Q) = (Q ∨ P) := by
  sorry

/-!
#### 练习：1 星, advanced (pe_implies_true_eq)
-/

/-- 命题外延性蕴含任意可证命题均与 True 相等 -/
theorem pe_implies_true_eq (PE : propositional_extensionality) (P : Prop) (HP : P) :
    True = P := by
  sorry

/-- 证明无关性断言：同一命题下的任意两个证据项在语义上恒等 -/
def proof_irrelevance : Prop :=
  ∀ (P : Prop) (pf1 pf2 : P), pf1 = pf2

/-!
#### 练习：3 星, advanced (pe_implies_pi)
-/

/-- 命题外延性必蕴含证明无关性 -/
theorem pe_implies_pi (PE : propositional_extensionality) : proof_irrelevance := by
  sorry

end ProofObjects
