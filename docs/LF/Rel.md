---
title: "Rel: 二元关系：性质、自反传递闭包与全序"
---

```lean
import SFLean4.LF.Basics
import SFLean4.LF.Induction
import SFLean4.LF.Lists
import SFLean4.LF.Poly
import SFLean4.LF.Tactics
import SFLean4.LF.Logic
import SFLean4.LF.IndProp

set_option linter.defProp false
set_option linter.ambiguousOpen false
```

# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)

## 第十一章：二元关系及其性质 (Rel: Properties of Relations)

本章（在原书中为选读章节）系统讨论了在依赖类型论中二元关系（Binary Relations）的形式化建模与性质分类。
这些关于二元关系的核心定义后续将在第二卷《程序语言基础》（*Programming Language Foundations*, PLF）的 `Smallstep` 章节中大放异彩。
对于希望精通依赖类型与关系推演的读者而言，本章提供了一系列极佳的证明推导与归纳练习。

---

### 本章核心学习目标：
1. **二元关系的形式化定义**：
   - 理解二元关系作为类型族 `X → X → Prop` 的数学本质；
   - 对比集合论中的关系概念与类型论中谓词化关系（Parameterized Proposition Families）的区别。
2. **关系的基本代数与拓扑性质**：
   - **单值性与偏函数 (Partial Functions)**：证明 `next_nat` 是偏函数，而 `<=` 不是；
   - **自反性 (Reflexivity)** 与 **传递性 (Transitivity)**；
   - **对称性 (Symmetry)** 与 **反对称性 (Antisymmetry)**；
   - **等价关系 (Equivalence Relations)**、**偏序 (Partial Orders)** 与 **预序 (Preorders)**。
3. **自反传递闭包 (Reflexive Transitive Closure)**：
   - **结构式闭包 (`clos_refl_trans`)**：通过自反规则、单步规则与双向传递规则直接生成的最小闭包；
   - **链式/正规单步闭包 (`clos_refl_trans_1n`)**：将传递规则正规化为单步归纳展开（$1+n$ 结构），显著简化归纳推导树；
   - **等价性定理 (`rtc_rsc_coincide`)**：形式化证明结构式闭包与单步链式闭包定义在逻辑上的完全等价性。

## 关系 (Relations)

```lean
namespace Rel

open IndProp
open IndProp.Playground hiding le_trans
open IndProp.Playground.le
```

### 1. 二元关系的基本概念

在集合 `X` 上的一个二元**关系**（Relation），是由两个 `X` 中的元素参数化的命题族——
换句话说，它是关于 `X` 中元素对的一个谓词（Proposition on pairs of elements of `X`）。

```lean
/-- 在类型 `X` 上的二元关系：接受两个 `X` 类型的元素，返回一个命题 `Prop` -/
def relation (X : Type) := X → X → Prop
```

自然数上的小于等于关系 `le` 就是一个典型的二元关系，通常记作 `n1 <= n2`。
我们可以检查它的类型：

## 基本性质 (Basic Properties)

```lean
#check (le : Nat → Nat → Prop)
#check (le : relation Nat)
```

正如任何学过离散数学课程的人所了解的那样，关于关系本身有非常丰富的代数与结构分类，
包括单值性（偏函数）、自反性、传递性、对称性、反对称性等。

```lean
-- *** 偏函数 (Partial Functions)
```

### 2.1 偏函数 (Partial Functions)

如果对于集合 `X` 上的关系 `R`，对任意 `x`，至多存在一个 `y` 使得 `R x y` 成立，
则称关系 `R` 为一个**偏函数**（Partial Function）。
即：若 `R x y1` 且 `R x y2`，则必定有 `y1 = y2`。

```lean
/-- 偏函数定义：任意原像对应的像若存在则必然唯一 -/
def partial_function {X : Type} (R : relation X) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2

/-- 后继关系：`next_nat n (n + 1)` 成立 -/
inductive next_nat : Nat → Nat → Prop where
  | nn (n : Nat) : next_nat n (n + 1)

#check (next_nat : relation Nat)

/-- `next_nat` 是一个偏函数（实际上是一个全函数，因为每个自然数有且仅有一个后继） -/
theorem next_nat_partial_function : partial_function next_nat := by
  intro x y1 y2 H1 H2
  cases H1
  cases H2
  rfl

/-- 小于等于关系 `<=` 不是偏函数（反证法：若它是偏函数，由于 `0 <= 0` 且 `0 <= 1`，将导出 `0 = 1`） -/
theorem le_not_a_partial_function : ¬ (partial_function le) := by
  intro Hc
  have Nonsense : 0 = 1 := Hc 0 0 1 le_n (le_S 0 le_n)
  cases Nonsense

/-- 全域二元关系：任意两个自然数之间均成立 -/
inductive total_relation : Nat → Nat → Prop where
  | total_rel (n m : Nat) : total_relation n m
```

### 🎯 练习：`total_relation_not_partial_function` <Badge type="info" text="2 星 · standard, optional" />

证明在 `IndProp` 中引入的 `total_relation` 不是偏函数。

```lean
theorem total_relation_not_partial_function :
    ¬ (partial_function total_relation) := by
  sorry

/-- 空关系：不存在任何证据的二元关系 -/
inductive empty_relation : Nat → Nat → Prop
```

### 🎯 练习：`empty_relation_partial_function` <Badge type="info" text="2 星 · standard, optional" />

证明在 `IndProp` 中引入的 `empty_relation` 是一个偏函数。

```lean
theorem empty_relation_partial_function :
    partial_function empty_relation := by
  sorry

-- *** 自反关系 (Reflexive Relations)
```

### 2.2 自反关系 (Reflexive Relations)

若集合 `X` 上的二元关系 `R` 满足每个元素都与自身相关联，则称 `R` 具有**自反性**。

```lean
/-- 自反性定义 -/
def reflexive {X : Type} (R : relation X) :=
  ∀ a : X, R a a

/-- `<=` 具有自反性 -/
theorem le_reflexive : reflexive le := by
  intro n
  exact le_n

-- *** 传递关系 (Transitive Relations)
```

### 2.3 传递关系 (Transitive Relations)

若关系 `R` 满足只要 `R a b` 且 `R b c` 成立，就必然有 `R a c` 成立，则称 `R` 具有**传递性**。

```lean
/-- 传递性定义 -/
def transitive {X : Type} (R : relation X) :=
  ∀ a b c : X, R a b → R b c → R a c

/-- `<=` 具有传递性 -/
theorem le_trans : transitive le := by
  intro n m o Hnm Hmo
  induction Hmo with
  | le_n => exact Hnm
  | le_S m' _ ih => exact le_S m' ih

/-- 严格小于关系 `<` 具有传递性 -/
theorem lt_trans : transitive lt := by
  intro n m o Hnm Hmo
  have Hnm' : n + 1 <= m + 1 := le_S m Hnm
  exact le_trans (n + 1) (m + 1) o Hnm' Hmo
```

### 🎯 练习：`le_trans_hard_way` <Badge type="info" text="2 星 · standard, optional" />

我们也可以不直接调用 `le_trans`，而是通过对证据进行归纳来繁复地证明 `lt_trans`。请完成该证明。

```lean
theorem lt_trans' : transitive lt := by
  -- 提示：对 m 小于 o 的推导证据进行归纳
  sorry
```

### 🎯 练习：`lt_trans''` <Badge type="info" text="2 星 · standard, optional" />

再次证明严格小于关系的传递性，这次改为直接对自然数 `o` 进行结构归纳。

```lean
theorem lt_trans'' : transitive lt := by
  sorry
```

`le` 的传递性可以进一步用来证明一些后续非常有用的辅助引理（例如后文的反对称性证明）：

```lean
/-- 若 `n + 1 <= m`，则必有 `n <= m` -/
theorem le_Sn_le : ∀ n m, n + 1 <= m → n <= m := by
  intro n m H
  exact le_trans n (n + 1) m (le_S n le_n) H
```

### 🎯 练习：`le_S_n` <Badge type="tip" text="1 星 · standard, optional" />

证明若两数后继满足小于等于关系，则其自身也满足小于等于关系。

```lean
theorem le_S_n : ∀ n m, (n + 1 <= m + 1) → (n <= m) := by
  sorry
```

### 🎯 练习：`le_Sn_n_inf` <Badge type="info" text="2 星 · standard, optional" />

给出以下定理的一个非形式化数学证明：

定理：对于任意自然数 `n`，都有 `¬ (n + 1 <= n)`（即 `S n <= n` 不可能成立）。

在完成后续的形式化证明前，先尝试写出非形式化证明。

证明思路（非形式化）：
对自然数 `n` 进行数学归纳：
- 基本情况（n = 0）：
  需要证明 `¬ (1 <= 0)`。
  根据 `<=` 的归纳定义，证据构造仅可能为自反项 `n <= n` 或后继扩展 `n <= m + 1`。
  但对于 `1 <= 0`，0 既不等于 1，也不是任何后继（`0 ≠ m + 1`），因此不可能存在任何证据，产生矛盾。
- 归纳步骤：
  归纳假设：对某个自然数 `n'`，假设 `¬ (n' + 1 <= n')` 成立。
  我们需要证明：`¬ ((n' + 1) + 1 <= n' + 1)`。
  反证法：假设 `(n' + 1) + 1 <= n' + 1` 成立。
  根据引理 `le_S_n`，两端同时剥去一个后继，可直接推导出 `n' + 1 <= n'`。
  这与归纳假设直接矛盾！
  综合上述两步，对所有自然数 `n`，`¬ (n + 1 <= n)` 均成立。证毕。

### 🎯 练习：`le_Sn_n` <Badge type="tip" text="1 星 · standard, optional" />

完成 `¬ (n + 1 <= n)` 的形式化证明。

```lean
theorem le_Sn_n : ∀ n, ¬ (n + 1 <= n) := by
  sorry

-- *** 对称与反对称关系 (Symmetric and Antisymmetric Relations)
```

### 2.4 对称与反对称关系

若二元关系 `R` 满足 `R a b` 蕴含 `R b a`，则称 `R` 为**对称关系**。

```lean
/-- 对称性定义 -/
def symmetric {X : Type} (R : relation X) :=
  ∀ a b : X, R a b → R b a
```

### 🎯 练习：`le_not_symmetric` <Badge type="info" text="2 星 · standard, optional" />

证明自然数上的 `<=` 不是对称关系。

```lean
theorem le_not_symmetric : ¬ (symmetric le) := by
  sorry
```

若关系 `R` 满足 `R a b` 与 `R b a` 同时成立时必能导出 `a = b`，则称 `R` 为**反对称关系**。
换言之，`R` 中唯一的“双向回环”只能是平凡的自反环。

```lean
/-- 反对称性定义 -/
def antisymmetric {X : Type} (R : relation X) :=
  ∀ a b : X, R a b → R b a → a = b
```

### 🎯 练习：`le_antisymmetric` <Badge type="info" text="2 星 · standard, optional" />

证明自然数上的 `<=` 满足反对称性。

```lean
theorem le_antisymmetric : antisymmetric le := by
  sorry
```

### 🎯 练习：`le_step` <Badge type="info" text="2 星 · standard, optional" />

```lean
theorem le_step : ∀ n m p, n < m → m <= p + 1 → n <= p := by
  sorry

-- *** 等价关系与偏序关系 (Equivalence Relations & Orderings)
```

### 2.5 等价关系、偏序与预序

一个二元关系如果同时满足**自反性**、**对称性**与**传递性**，则被称为**等价关系**（Equivalence Relation）。

```lean
/-- 等价关系定义 -/
def equivalence {X : Type} (R : relation X) :=
  (reflexive R) ∧ (symmetric R) ∧ (transitive R)
```

若一个二元关系满足**自反性**、**反对称性**与**传递性**，则被称为**偏序关系**（Partial Order，在 Coq 标准库中简称为 `order`）。

```lean
/-- 偏序关系定义 -/
def order {X : Type} (R : relation X) :=
  (reflexive R) ∧ (antisymmetric R) ∧ (transitive R)
```

**预序**（Preorder）与偏序类似，但不需要满足反对称性（只要求自反性与传递性）。

## 自反传递闭包 (Reflexive, Transitive Closure)

```lean
/-- 预序关系定义 -/
def preorder {X : Type} (R : relation X) :=
  (reflexive R) ∧ (transitive R)

/-- `<=` 是自然数上的偏序关系 -/
theorem le_order : order le := by
  refine ⟨le_reflexive, le_antisymmetric, le_trans⟩
```

### 3. 自反传递闭包 (Reflexive, Transitive Closure)

关系 `R` 的**自反传递闭包**是包含 `R` 且同时满足自反性与传递性的**最小二元关系**。
在 Coq 标准库 `Relations` 模块与数学定义中，它通过以下三个公理式规则归纳生成：
1. `rt_step`: 基础步，若 `R x y`，则闭包关系成立；
2. `rt_refl`: 自反步，任意元素 `x` 与自身构成闭包关系；
3. `rt_trans`: 传递步，若 `x` 与 `y`、`y` 与 `z` 构成闭包关系，则 `x` 与 `z` 构成闭包关系。

```lean
/-- 自反传递闭包的标准公理化归纳定义 -/
inductive clos_refl_trans {A : Type} (R : relation A) : relation A where
  | rt_step (x y : A) (H : R x y) : clos_refl_trans R x y
  | rt_refl (x : A) : clos_refl_trans R x x
  | rt_trans (x y z : A)
      (Hxy : clos_refl_trans R x y)
      (Hyz : clos_refl_trans R y z) :
      clos_refl_trans R x z
```

例如，自然数单步递增关系 `next_nat` 的自反传递闭包正好就是小于等于关系 `<=`：

```lean
theorem next_nat_closure_is_le :
    ∀ n m, (n <= m) ↔ ((clos_refl_trans next_nat) n m) := by
  intro n m
  constructor
  · intro H
    induction H with
    | le_n => exact clos_refl_trans.rt_refl _
    | le_S m' _ ih =>
      exact clos_refl_trans.rt_trans _ _ _ ih (clos_refl_trans.rt_step _ _ (next_nat.nn m'))
  · intro H
    induction H with
    | rt_step x y H =>
      cases H
      exact le_S _ le_n
    | rt_refl x => exact le_n
    | rt_trans x y z _ _ ih1 ih2 =>
      exact le_trans x y z ih1 ih2
```

上述 `clos_refl_trans` 的定义虽然极为自然直观，但在进行形式化证明时却常常不甚方便：
因为 `rt_trans` 规则中中间节点 `y` 的存在带来了“非确定性”（Nondeterminism），在归纳反演时容易产生复杂的推导树分支。

为此，我们引入另一种更适合证明的等价定义：**单步左结合链式闭包 (`clos_refl_trans_1n`)**。
该定义将任意多次传递紧凑地“打包”为自反基础情况与一个单步跃迁（$1 + n$ 形式）：

> **Lean 4 语法与参数设计注解**：
> 在 Coq 中，原书将起始节点 `(x : A)` 放在冒号左侧声明为参数。
> 但在 Lean 4 中，归纳类型的所有参数在递归调用中必须保持绝对统一（Uniform Parameters）。
> 由于在传递步骤 `rt1n_trans` 中，后续链条 `Hrest` 的起始节点由 `x` 转变为 `y`，
> 因此在 Lean 4 中起始点与终止点均作为索引类型（`A → A → Prop`），这是类型论在归纳定义严谨性上的优秀体现。

```lean
/-- 单步链式自反传递闭包 (1+n 形式) -/
inductive clos_refl_trans_1n {A : Type} (R : relation A) : A → A → Prop where
  | rt1n_refl (x : A) : clos_refl_trans_1n R x x
  | rt1n_trans (x y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z
```

在展示两个闭包定义完全等价之前，我们首先证明两个辅助引理：
表明 `clos_refl_trans_1n` 能够完美模拟 `clos_refl_trans` 中“缺失”的单步嵌入和一般传递。

```lean
/-- 单步嵌入：单步关系 `R` 可以直接嵌入到 1-n 链式闭包中 -/
theorem rsc_R : ∀ (X : Type) (R : relation X) (x y : X),
    R x y → clos_refl_trans_1n R x y := by
  intro X R x y H
  exact clos_refl_trans_1n.rt1n_trans x y y H (clos_refl_trans_1n.rt1n_refl y)
```

### 🎯 练习：`rsc_trans` <Badge type="info" text="2 星 · standard, optional" />

证明 1-n 链式闭包满足一般传递性。

```lean
theorem rsc_trans :
    ∀ (X : Type) (R : relation X) (x y z : X),
      clos_refl_trans_1n R x y →
      clos_refl_trans_1n R y z →
      clos_refl_trans_1n R x z := by
  sorry
```

### 🎯 练习：`rtc_rsc_coincide` <Badge type="warning" text="3 星 · standard, optional" />

最终综合上述所有结果，证明结构式公理闭包 `clos_refl_trans` 与单步链式闭包 `clos_refl_trans_1n` 逻辑上完全等价！

```lean
theorem rtc_rsc_coincide :
    ∀ (X : Type) (R : relation X) (x y : X),
      clos_refl_trans R x y ↔ clos_refl_trans_1n R x y := by
  sorry

end Rel
```
