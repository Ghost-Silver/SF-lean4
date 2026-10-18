import SFLean4.VFA.Perm
import SFLean4.VFA.Sort

namespace VFA.BagPerm

open VFA.Perm
open VFA.Sort

/-!
# 《软件基础》(Software Foundations) 卷三：函数式算法验证 (VFA)

## 第四章：基于包的多重集置换 (BagPerm: Insertion Sort With Bags)

在上一章中，我们使用高阶特征函数 `value → Nat` 形式化了多重集。
在本章中，我们将采用一种更为初等、直接的表示：**直接使用列表本身作为多重集（Bag / 包）**，
并通过显式计数函数 `count` 来定义两包之间的等价关系 `bag_eqv`。

我们不仅将基于 `bag_eqv` 再次证明插入排序的正确性，还将建立一个极具理论深度的核心定理：
**两列表多重集等价充要于置换关系 (`bag_eqv al bl ↔ Permutation al bl`)**！
-/

/-- 使用列表直接表示包（多重集） -/
abbrev bag := List Nat

/-- 计算特定数值在包中出现的总次数 -/
def count (v : Nat) (s : bag) : Nat :=
  match s with
  | [] => 0
  | h :: t => (if h == v then 1 else 0) + count v t

/-- 两个包等价：对任意数值其出现频次均完全一致 -/
def bag_eqv (b1 b2 : bag) : Prop :=
  ∀ n, count n b1 = count n b2

/-!
#### 练习：2 星, standard (bag_eqv_properties)
证明 `bag_eqv` 是一个等价关系。
-/
theorem bag_eqv_refl : ∀ b, bag_eqv b b := by
  intro b n
  rfl

theorem bag_eqv_sym : ∀ b1 b2, bag_eqv b1 b2 → bag_eqv b2 b1 := by
  intro b1 b2 h n
  exact (h n).symm

theorem bag_eqv_trans : ∀ b1 b2 b3, bag_eqv b1 b2 → bag_eqv b2 b3 → bag_eqv b1 b3 := by
  intro b1 b2 b3 h12 h23 n
  exact (h12 n).trans (h23 n)

theorem bag_eqv_cons : ∀ x b1 b2, bag_eqv b1 b2 → bag_eqv (x :: b1) (x :: b2) := by
  intro x b1 b2 h n
  dsimp [count]
  rw [h n]

/- ################################################################# -/
/-! ## 1. 正确性规约 (Correctness) -/
/- ################################################################# -/

/-- 基于包等价性的排序正确性规约 -/
def is_a_sorting_algorithm' (f : List Nat → List Nat) : Prop :=
  ∀ al, bag_eqv al (f al) ∧ sorted (f al)

/-!
#### 练习：3 星, standard (insert_bag)
-/
theorem insert_bag : ∀ x l, bag_eqv (x :: l) (Sort.insert x l) := by
  sorry

/-!
#### 练习：2 星, standard (sort_bag)
-/
theorem sort_bag : ∀ l, bag_eqv l (Sort.sort l) := by
  sorry

/-- 插入排序基于包等价性规约的正确性定理 -/
theorem insertion_sort_correct :
  is_a_sorting_algorithm' Sort.sort := by
  intro al
  exact ⟨sort_bag al, sort_sorted al⟩

/-!
#### 练习：1 星, standard (permutations_vs_multiset)
-/
def manual_grade_for_permutations_vs_multiset : Option (Nat × String) := none

/- ################################################################# -/
/-! ## 2. 置换与包等价性的双向等价 (Permutations and Multisets) -/
/- ################################################################# -/

/-!
#### 练习：3 星, standard (perm_bag)
-/
theorem perm_bag : ∀ al bl : List Nat,
  Permutation al bl → bag_eqv al bl := by
  sorry

/-!
#### 练习：2 星, advanced (bag_nil_inv)
-/
theorem bag_nil_inv : ∀ b, bag_eqv ([] : bag) b → b = ([] : bag) := by
  sorry

/-!
#### 练习：3 星, advanced (bag_cons_inv)
-/
theorem bag_cons_inv : ∀ l x n,
  Nat.succ n = count x l →
  ∃ l1 l2,
    l = l1 ++ x :: l2 ∧ count x (l1 ++ l2) = n := by
  sorry

/-!
#### 练习：2 星, advanced (count_insert_other)
-/
theorem count_insert_other : ∀ l1 l2 x y,
  y ≠ x → count y (l1 ++ x :: l2) = count y (l1 ++ l2) := by
  sorry

/-!
#### 练习：3 星, advanced (bag_perm)
-/
theorem bag_perm : ∀ al bl,
  bag_eqv al bl → Permutation al bl := by
  sorry

/-- 主定理：包等价与置换关系完全充要等价 -/
theorem bag_eqv_iff_perm : ∀ al bl,
  bag_eqv al bl ↔ Permutation al bl := by
  intro al bl
  exact ⟨bag_perm al bl, perm_bag al bl⟩

/-- 推论：基于置换与基于包的排序规约完全等价 -/
theorem sort_specifications_equivalent : ∀ sort : List Nat → List Nat,
  Sort.is_a_sorting_algorithm sort ↔ is_a_sorting_algorithm' sort := by
  intro s
  dsimp [Sort.is_a_sorting_algorithm, is_a_sorting_algorithm']
  constructor
  · intro h al
    obtain ⟨hp, hs⟩ := h al
    exact ⟨(bag_eqv_iff_perm al (s al)).mpr hp, hs⟩
  · intro h al
    obtain ⟨hb, hs⟩ := h al
    exact ⟨(bag_eqv_iff_perm al (s al)).mp hb, hs⟩

end VFA.BagPerm
