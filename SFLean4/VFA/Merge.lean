import SFLean4.VFA.Perm
import SFLean4.VFA.Sort

namespace VFA.Merge

open VFA.Perm
open VFA.Sort

/-!
# 《软件基础》(Software Foundations) 卷三：函数式算法验证 (VFA)

## 第七章：归并排序及其规范与正确性证明 (Merge: Merge Sort, With Specification and Proof of Correctness)

归并排序（Mergesort）是一种经典的分治排序算法。其基本思想是：
1. **划分 (Split)**：将待排序列划分为大小大致相等的左右两个子序列；
2. **递归求解 (Recurse)**：对左右两个子序列分别递归进行归并排序；
3. **合并 (Merge)**：将已排序的两个子序列合并为一个完整且有序的序列。

在数组等命令式结构中，归并排序具有 $\mathcal{O}(n \log n)$ 的最坏时间复杂度和 $\mathcal{O}(n)$ 的辅助空间。
在纯函数式列表上，列表切分需要 $\mathcal{O}(n)$ 时间，但由于合并步骤本身也是 $\mathcal{O}(n)$，
因此整体的渐近时间复杂度仍保持为理想的 $\mathcal{O}(n \log n)$。

在本章中，我们将形式化定义列表上的归并排序，深入探讨“双步归纳原理 (Two-step Induction Principle)”，
并完整形式化验证归并排序的保序性与置换性。

---

## 1. 列表划分及其性质 (Split and its Properties)
-/

/-- 将列表元素交替分配到两个子列表中 -/
def split {X : Type} (l : List X) : List X × List X :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x1 :: x2 :: l' =>
    let (l1, l2) := split l'
    (x1 :: l1, x2 :: l2)

/-!
### 1.1 双步归纳原理 (Two-Step Induction Principle)

普通列表的标准归纳原理假设性质对 `tail` 成立以推导整个非空列表。
但在处理 `split` 时，递归步跨越了两个元素（`x1 :: x2 :: l'`），
因此需要一个对跨步为 2 的列表生效的双步归纳原理。
-/

/-- 双步列表归纳原理的命题陈述 -/
def list_ind2_principle : Prop :=
  ∀ (A : Type) (P : List A → Prop),
    P [] →
    (∀ a, P [a]) →
    (∀ a b l, P l → P (a :: b :: l)) →
    ∀ l, P l

/-- 双步归纳原理的具体构造实现 -/
theorem list_ind2 {A : Type} {P : List A → Prop}
    (h_nil : P [])
    (h_one : ∀ a, P [a])
    (h_two : ∀ a b l, P l → P (a :: b :: l)) :
    ∀ l, P l
  | [] => h_nil
  | [a] => h_one a
  | a :: b :: rest => h_two a b rest (list_ind2 h_nil h_one h_two rest)

/-- 若假设双步归纳原理，则 `split` 后两子列表长度均不大于原列表长度 -/
theorem split_len' : list_ind2_principle →
    ∀ {X : Type} (l l1 l2 : List X),
      split l = (l1, l2) →
      l1.length ≤ l.length ∧ l2.length ≤ l.length := by
  intro _IP X l
  induction l using list_ind2 with
  | h_nil =>
    intro l1 l2 h; injection h with h1 h2; subst h1 h2; simp
  | h_one a =>
    intro l1 l2 h; injection h with h1 h2; subst h1 h2; simp
  | h_two a b l' ih =>
    intro l1 l2 h
    simp [split] at h
    match hrec : split l' with
    | (r1, r2) =>
      rw [hrec] at h
      rcases h with ⟨rfl, rfl⟩
      have := ih r1 r2 hrec
      simp
      omega

/-- 使用证明好的 `list_ind2` 确立 `split_len` -/
theorem split_len : ∀ {X : Type} (l l1 l2 : List X),
    split l = (l1, l2) →
    l1.length ≤ l.length ∧ l2.length ≤ l.length := by
  intro X l
  induction l using list_ind2 with
  | h_nil =>
    intro l1 l2 h; injection h with h1 h2; subst h1 h2; simp
  | h_one a =>
    intro l1 l2 h; injection h with h1 h2; subst h1 h2; simp
  | h_two a b l' ih =>
    intro l1 l2 h
    simp [split] at h
    match hrec : split l' with
    | (r1, r2) =>
      rw [hrec] at h
      rcases h with ⟨rfl, rfl⟩
      have := ih r1 r2 hrec
      simp
      omega

/-- 辅助引理：当原列表长度至少为 2 时，`split` 划分出的两个子列表长度严格小于原列表 -/
theorem split_strict_len : ∀ {X : Type} (a b : X) (rest l1 l2 : List X),
    split (a :: b :: rest) = (l1, l2) →
    l1.length < (a :: b :: rest).length ∧ l2.length < (a :: b :: rest).length := by
  intro X a b rest l1 l2 h
  simp [split] at h
  match hrec : split rest with
  | (r1, r2) =>
    rw [hrec] at h
    rcases h with ⟨rfl, rfl⟩
    have := split_len rest r1 r2 hrec
    simp
    omega

/-- #### 练习：3 星 (split_perm)
证明原列表与切分后拼接的双列表互为置换。 -/
theorem split_perm : ∀ {X : Type} (l l1 l2 : List X),
    split l = (l1, l2) → Permutation l (l1 ++ l2) := by
  sorry

/-!
---
## 2. 合并两个已排序列表 (Defining Merge)
-/

/-- 将两个升序列表按大小顺序归并为一个有序列表。
在 Lean 4 中，以两列表长度和 `l1.length + l2.length` 作为良基度量，系统自动完成终止性验证。 -/
def merge (l1 l2 : List Nat) : List Nat :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1 :: l1', a2 :: l2' =>
    if a1 ≤ a2 then
      a1 :: merge l1' (a2 :: l2')
    else
      a2 :: merge (a1 :: l1') l2'
termination_by l1.length + l2.length

/-- 空列表在左侧时的合并退化情形 -/
theorem merge_nil_l : ∀ l, merge [] l = l := by
  intro l
  rw [merge]

/-- 头部元素满足序关系时的合并前进步伐 -/
theorem merge2 : ∀ (x1 x2 : Nat) r1 r2,
    x1 ≤ x2 →
    merge (x1 :: r1) (x2 :: r2) = x1 :: merge r1 (x2 :: r2) := by
  intro x1 x2 r1 r2 h
  conv => lhs; rw [merge]
  simp [h]

/-!
---
## 3. 归并排序主算法 (Defining Mergesort)
-/

/-- 完整的归并排序算法：
对于基准情况（空列表与单元素列表）直接返回；
对于长度至少为 2 的列表，切分为两半并递归排序后合并。 -/
def mergesort (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | [x] => [x]
  | x1 :: x2 :: l' =>
    match heq : split (x1 :: x2 :: l') with
    | (l1, l2) =>
      have _hlen := split_strict_len x1 x2 l' l1 l2 heq
      merge (mergesort l1) (mergesort l2)
termination_by l.length
decreasing_by
  · exact _hlen.1
  · exact _hlen.2

/-- 归并排序计算验证示例 -/
theorem mergesort_example : mergesort [5, 2, 8, 3, 1, 9, 4, 6, 7] = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  sorry

/-- 归并排序展开方程 -/
theorem mergesort_equation : ∀ l : List Nat,
    mergesort l =
      match l with
      | [] => []
      | [x] => [x]
      | x1 :: x2 :: l' =>
        let (l1, l2) := split (x1 :: x2 :: l')
        merge (mergesort l1) (mergesort l2) := by
  intro l
  rw [mergesort.eq_def]

/-- 适合归并排序结构的特化归纳原理 -/
theorem mergesort_ind : ∀ (P : List Nat → List Nat → Prop),
    (∀ l, l = ([] : List Nat) → P [] []) →
    (∀ l (x : Nat), l = ([x] : List Nat) → P [x] [x]) →
    (∀ l _x, l = _x →
      (match _x with | _ :: _ :: _ => True | _ => False) →
      ∀ l1 l2, split l = (l1, l2) →
      P l1 (mergesort l1) →
      P l2 (mergesort l2) →
      P _x (merge (mergesort l1) (mergesort l2))) →
    ∀ l, P l (mergesort l) := by
  sorry

/-!
---
## 4. 正确性证明：保序性 (Correctness: Sortedness)
-/

/-- #### 练习：2 星 (sorted_merge1)
证明若首元素不大于待合并两列表的首元素，则将其置于合并结果前仍保持有序。 -/
theorem sorted_merge1 : ∀ x x1 l1 x2 l2,
    x ≤ x1 → x ≤ x2 →
    sorted (merge (x1 :: l1) (x2 :: l2)) →
    sorted (x :: merge (x1 :: l1) (x2 :: l2)) := by
  sorry

/-- #### 练习：4 星 (sorted_merge)
核心引理：两个有序列表合并后的结果仍有序。 -/
theorem sorted_merge : ∀ l1, sorted l1 →
    ∀ l2, sorted l2 →
    sorted (merge l1 l2) := by
  sorry

/-- #### 练习：2 星 (mergesort_sorts)
证明归并排序产出的列表必然升序有序。 -/
theorem mergesort_sorts : ∀ l, sorted (mergesort l) := by
  sorry

/-!
---
## 5. 正确性证明：置换性 (Correctness: Permutation)
-/

/-- #### 练习：3 星，进阶 (merge_perm)
核心引理：合并两个列表得到的结果是原两列表拼接结果的一个置换。 -/
theorem merge_perm : ∀ (l1 l2 : List Nat),
    Permutation (l1 ++ l2) (merge l1 l2) := by
  sorry

/-- #### 练习：3 星，进阶 (mergesort_perm)
证明归并排序产出的列表是输入的置换。 -/
theorem mergesort_perm : ∀ l, Permutation l (mergesort l) := by
  sorry

/-- 最终结论：归并排序是一个完全正确的排序算法！ -/
theorem mergesort_correct :
    is_a_sorting_algorithm mergesort := by
  intro al
  exact ⟨mergesort_perm al, mergesort_sorts al⟩

end VFA.Merge
