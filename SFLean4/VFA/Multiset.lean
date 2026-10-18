import SFLean4.VFA.Perm
import SFLean4.VFA.Sort

namespace VFA.Multiset

open VFA.Perm
open VFA.Sort

/-!
# 《软件基础》(Software Foundations) 卷三：函数式算法验证 (VFA)

## 第三章：基于多重集的规约 (Multiset: Multisets)

在上一章中，我们将排序算法的置换性质表述为 `Permutation al (f al)`。
置换关系是一个归纳定义的二元谓词。
在本章中，我们将探讨一种截然不同的替代方案：**多重集（Multiset，亦称 Bag / 包）**。

多重集记录了每个元素在集合中出现的**重数（Multiplicity / 频次）**。
两个列表是相互置换的，当且仅当它们对应完全相同的多重集。
这种基于特征函数（Characteristic Function）的方法往往使某些高阶性质的证明变得极其简洁。
-/

/-- 多重集中存储的元素类型 -/
abbrev value := Nat

/-- 多重集：由元素映射到其出现次数的频次函数 -/
def multiset : Type := value → Nat

/-- 空多重集：所有元素的计数均为 0 -/
def empty : multiset := fun _ => 0

/-- 单例多重集：指定元素计数为 1，其余均为 0 -/
def singleton (v : value) : multiset :=
  fun x => if x == v then 1 else 0

/-- 多重集的并集：频次直接相加 -/
def union (a b : multiset) : multiset :=
  fun x => a x + b x

/-!
#### 练习：1 星, standard (union_assoc)
-/
theorem union_assoc : ∀ a b c : multiset,
  union a (union b c) = union (union a b) c := by
  sorry

/-!
#### 练习：1 星, standard (union_comm)
-/
theorem union_comm : ∀ a b : multiset,
  union a b = union b a := by
  sorry

/-!
#### 练习：2 星, standard (union_swap)
-/
theorem union_swap : ∀ a b c : multiset,
  union a (union b c) = union b (union a c) := by
  sorry

/-- 将列表转化为对应的多重集频次表 -/
def contents (al : List value) : multiset :=
  match al with
  | [] => empty
  | a :: bl => union (singleton a) (contents bl)

theorem sort_pi_same_contents :
  contents [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = contents [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by
  sorry

/-- 基于多重集内容的排序算法正确性替代规约 -/
def is_a_sorting_algorithm' (f : List Nat → List Nat) : Prop :=
  ∀ al, contents al = contents (f al) ∧ sorted (f al)

/-!
#### 练习：3 星, standard (insert_contents)
-/
theorem insert_contents : ∀ (x : Nat) (l : List Nat),
  contents (Sort.insert x l) = contents (x :: l) := by
  sorry

/-!
#### 练习：2 星, standard (sort_contents)
-/
theorem sort_contents : ∀ l : List value,
  contents l = contents (Sort.sort l) := by
  sorry

/-!
#### 练习：1 星, standard (insertion_sort_correct)
-/
theorem insertion_sort_correct :
  is_a_sorting_algorithm' Sort.sort := by
  sorry

/-!
#### 练习：1 星, standard (permutations_vs_multiset)
思考题：置换归纳定义与多重集特征函数规约各有何优劣？
-/
def manual_grade_for_permutations_vs_multiset : Option (Nat × String) := none

/-!
#### 练习：3 星, standard (perm_contents)
证明置换必然产生相同的多重集。
-/
theorem perm_contents : ∀ al bl : List Nat,
  Permutation al bl → contents al = contents bl := by
  sorry

/-!
#### 练习：2 星, advanced (contents_nil_inv)
-/
theorem contents_nil_inv : ∀ l : List value,
  (∀ x : value, 0 = contents l x) → l = ([] : List value) := by
  sorry

/-!
#### 练习：3 星, advanced (contents_cons_inv)
-/
theorem contents_cons_inv : ∀ (l : List value) (x : value) (n : Nat),
  Nat.succ n = contents l x →
  ∃ l1 l2 : List value,
    l = l1 ++ x :: l2 ∧ contents (l1 ++ l2) x = n := by
  sorry

/-!
#### 练习：2 星, advanced (contents_insert_other)
-/
theorem contents_insert_other : ∀ (l1 l2 : List value) (x y : value),
  y ≠ x → contents (l1 ++ x :: l2) y = contents (l1 ++ l2) y := by
  sorry

/-!
#### 练习：3 星, advanced (contents_perm)
-/
theorem contents_perm : ∀ al bl : List value,
  contents al = contents bl → Permutation al bl := by
  sorry

/-- 双向等价定理：多重集相等充要于置换关系 -/
theorem same_contents_iff_perm : ∀ al bl : List value,
  contents al = contents bl ↔ Permutation al bl := by
  sorry

/-- 两套排序规约在数学上完全等价 -/
theorem sort_specifications_equivalent : ∀ sort : List Nat → List Nat,
  Sort.is_a_sorting_algorithm sort ↔ is_a_sorting_algorithm' sort := by
  sorry

end VFA.Multiset
