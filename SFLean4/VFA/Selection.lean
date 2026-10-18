import SFLean4.VFA.Perm
import SFLean4.VFA.Sort
import SFLean4.VFA.Multiset

namespace VFA.Selection

open VFA.Perm
open VFA.Sort
open VFA.Multiset

/-!
# 《软件基础》(Software Foundations) 卷三：函数式算法验证 (VFA)

## 第六章：选择排序 (Selection: Selection Sort)

选择排序（Selection Sort）是一种直观的排序算法。其基本思想是：
每次从待排序的数据中“选择”出最小的元素，将其放置于排序结果的最前端，
然后对剩余的所有元素递归进行相同的选择操作，直至待排列表变空。

与插入排序不同，选择排序在纯函数式语言中引入了一个全新的挑战：
递归调用 `selsort` 时，传入的剩余列表并不是原列表在语法上的“直接子项（structural subterm）”，
而是由抽取函数 `select` 动态计算得出的结果。
在 Coq 和 Lean 4 中，这需要我们向系统证明递归必定终止：
- **方案一：燃油技术 (Fuel)** —— 引入一个单纯用于计数减小的燃油参数 `n`；
- **方案二：基于度量的良基归纳 (Well-founded recursion via Measure)** —— 使用列表长度作为度量函数（Measure），证明递归参数的度量严格单调递减。

---

## 1. 选择排序的程序实现 (The Selection-Sort Program)
-/

/-- 从非空元素集合 `x :: l` 中抽选出最小元素。
返回二元组 `(y, l')`，其中 `y` 是最小元素，`l'` 是除 `y` 之外剩余的元素构成的列表。 -/
def select (x : Nat) (l : List Nat) : Nat × List Nat :=
  match l with
  | [] => (x, [])
  | h :: t =>
    if x <= h then
      let (j, l') := select x t
      (j, h :: l')
    else
      let (j, l') := select h t
      (j, x :: l')

/-!
如果我们直接尝试写出如下递归：
```lean
def selsort (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | x :: r =>
    let (y, r') := select x r
    y :: selsort r'
```
系统无法凭语法结构自动判定 `r'` 严格小于 `x :: r`（因为 `r'` 是由 `select` 函数返回的）。
因此，我们首先使用**燃油（Fuel）**模式实现一个结构递归版本：
-/

/-- 带有步数限制（燃油 `n`）的选择排序函数 -/
def selsort (l : List Nat) (n : Nat) : List Nat :=
  match l, n with
  | _, 0 => []
  | [], _ => []
  | x :: r, n' + 1 =>
    let (y, r') := select x r
    y :: selsort r' n'

/-- 若燃油不足，算法提前终止，无法得到完整有序列表 -/
example : selsort [3, 1, 4, 1, 5] 3 ≠ [1, 1, 3, 4, 5] := by
  decide

/-- 充足的燃油能保证排序完成 -/
example : selsort [3, 1, 4, 1, 5] 10 = [1, 1, 3, 4, 5] := by
  decide

/-- 完整的选择排序算法：以列表自身长度 `length l` 作为精确燃油量 -/
def selection_sort (l : List Nat) : List Nat :=
  selsort l l.length

example : selection_sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by
  rfl

/-!
---
## 2. 正确性规约 (Proof of Correctness)
-/

/-- 列表全序排序的归纳定义（与 `Sort` 章节一致） -/
inductive sorted : List Nat → Prop where
  | sorted_nil : sorted []
  | sorted_1 (i : Nat) : sorted [i]
  | sorted_cons (i j : Nat) (l : List Nat) : i ≤ j → sorted (j :: l) → sorted (i :: j :: l)

/-- 排序算法的完全正确性规约：输入与输出为互为置换，且输出完全保序 -/
def is_a_sorting_algorithm (f : List Nat → List Nat) : Prop :=
  ∀ al, Permutation al (f al) ∧ sorted (f al)

/-- 拆分二元组模式匹配的示例 -/
example (a _c x : Nat) (b _d l : List Nat) :
    (a, b) = (let (c, d) := select x l; (c, d)) →
    (a, b) = select x l := by
  intro h
  exact h

/-!
### 练习：抽取性质与置换定理
-/

/-- #### 练习：2 星 (select_perm)
证明 `select` 返回的最小项与剩余列表合并后是原输入的一个置换。 -/
theorem select_perm : ∀ x l y r,
    select x l = (y, r) → Permutation (x :: l) (y :: r) := by
  sorry

/-- 私有辅助引理：用于支持后续良基递归的无 sorry 度量减小证明 -/
private theorem select_rest_length_aux : ∀ x l y r,
    select x l = (y, r) → l.length = r.length := by
  intro x l
  induction l generalizing x with
  | nil =>
    intro y r h
    injection h with h1 h2
    subst h2; rfl
  | cons h t ih =>
    intro y r hsel
    simp [select] at hsel
    split at hsel
    · match hrec : select x t with
      | (j, l') =>
        rw [hrec] at hsel
        injection hsel with h1 h2
        subst h2
        simp [ih x j l' hrec]
    · match hrec : select h t with
      | (j, l') =>
        rw [hrec] at hsel
        injection hsel with h1 h2
        subst h2
        simp [ih h j l' hrec]

/-- #### 练习：1 星 (select_rest_length)
证明 `select` 返回的剩余列表长度与传入尾部列表长度相同。 -/
theorem select_rest_length : ∀ x l y r,
    select x l = (y, r) → l.length = r.length := by
  sorry

/-- #### 练习：3 星 (selsort_perm)
证明在提供足够燃油时，`selsort` 产生的列表是原列表的置换。 -/
theorem selsort_perm : ∀ n l,
    l.length = n → Permutation l (selsort l n) := by
  sorry

/-- #### 练习：1 星 (selection_sort_perm)
证明完整的 `selection_sort` 产生一个置换。 -/
theorem selection_sort_perm : ∀ l,
    Permutation l (selection_sort l) := by
  sorry

/-- #### 练习：2 星 (select_fst_leq)
证明 `select x _` 返回的首个分量不超过 `x`。 -/
theorem select_fst_leq : ∀ al bl x y,
    select x al = (y, bl) → y ≤ x := by
  sorry

/-- 列表成员判定关系 -/
def In {A : Type} (x : A) (l : List A) : Prop := List.Mem x l

/-- 元素对列表中所有元素均小于等于的关系判定 -/
def le_all (x : Nat) (xs : List Nat) : Prop :=
  Forall (fun y => x ≤ y) xs

scoped infix:70 " <=* " => le_all

/-- #### 练习：1 星 (le_all__le_one)
证明如果 `y` 小于等于列表中的所有元素，且 `n` 在列表中，则 `y ≤ n`。 -/
theorem le_all__le_one : ∀ lst y n,
    y <=* lst → In n lst → y ≤ n := by
  sorry

/-- #### 练习：2 星 (select_smallest)
证明 `select` 返回的第一项不大于剩余列表中的任何项。 -/
theorem select_smallest : ∀ al bl x y,
    select x al = (y, bl) → y <=* bl := by
  sorry

/-- #### 练习：2 星 (select_in)
证明 `select` 返回的元素必定属于原始输入的元素集合。 -/
theorem select_in : ∀ al bl x y,
    select x al = (y, bl) → In y (x :: al) := by
  sorry

/-- #### 练习：3 星 (cons_of_small_maintains_sort)
证明将足够小的元素添加到有序选择排序结果前，仍保持全局有序。 -/
theorem cons_of_small_maintains_sort : ∀ bl y n,
    n = bl.length →
    y <=* bl →
    sorted (selsort bl n) →
    sorted (y :: selsort bl n) := by
  sorry

/-- #### 练习：2 星 (selsort_sorted)
证明在充足燃油下，`selsort` 得到的结果必为有序列表。 -/
theorem selsort_sorted : ∀ n al,
    al.length = n → sorted (selsort al n) := by
  sorry

/-- #### 练习：1 星 (selection_sort_sorted)
证明 `selection_sort` 产生的列表完全有序。 -/
theorem selection_sort_sorted : ∀ al,
    sorted (selection_sort al) := by
  sorry

/-- #### 练习：1 星 (selection_sort_is_correct)
结论：`selection_sort` 满足全套排序算法正确性规约！ -/
theorem selection_sort_is_correct :
    is_a_sorting_algorithm selection_sort := by
  sorry

/-!
---
## 3. 非结构递归的函数定义与度量递归 (Measure-based Recursion)

在现代定理证明器中，我们无需始终手动携带“燃油”参数。
在 Lean 4 中，我们可以直接使用 `termination_by` 声明度量函数（此处为 `l.length`），
并通过抽取引理向良基系统证明每次递归调用处参数的长度都严格减小。
-/

/-- 基于长度良基度量的直接选择排序 -/
def selsort' (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | x :: r =>
    have hsel : (select x r).2.length < (x :: r).length := by
      have h := select_rest_length_aux x r (select x r).1 (select x r).2 (Prod.eta (select x r)).symm
      simp [h]
    (select x r).1 :: selsort' (select x r).2
termination_by l.length
decreasing_by
  exact hsel

theorem selsort'_example : selsort' [3, 1, 4, 1, 5, 9, 2, 6, 5] = [1, 1, 2, 3, 4, 5, 5, 6, 9] := by
  sorry

/-- #### 练习：1 星 (selsort'_perm) -/
theorem selsort'_perm : ∀ n l,
    l.length = n → Permutation l (selsort' l) := by
  sorry

/-- #### 练习：1 星 (cons_of_small_maintains_sort') -/
theorem cons_of_small_maintains_sort' : ∀ bl y,
    y <=* bl →
    sorted (selsort' bl) →
    sorted (y :: selsort' bl) := by
  sorry

/-- #### 练习：1 星 (selsort'_sorted) -/
theorem selsort'_sorted : ∀ n al,
    al.length = n → sorted (selsort' al) := by
  sorry

/-- #### 练习：1 星 (selsort'_is_correct) -/
theorem selsort'_is_correct :
    is_a_sorting_algorithm selsort' := by
  sorry

/-!
---
## 4. 基于多重集（Multiset）验证选择排序 (Selection Sort with Multisets)
-/

/-- #### 练习：3 星，选做 (select_contents)
证明选择操作保持元素多重集的守恒性。 -/
theorem select_contents : ∀ al bl x y,
    select x al = (y, bl) →
    union (singleton x) (contents al) = union (singleton y) (contents bl) := by
  sorry

/-- #### 练习：3 星，选做 (selection_sort_contents)
证明完整的选择排序保持元素多重集守恒。 -/
theorem selection_sort_contents : ∀ n l,
    l.length = n →
    contents l = contents (selection_sort l) := by
  sorry

/-- #### 练习：2 星，选做 (sorted_iff_sorted)
证明本章定义的 `sorted` 谓词与 `Sort` 章节中的 `Sort.sorted` 谓词等价。 -/
theorem sorted_iff_sorted : ∀ l,
    sorted l ↔ VFA.Sort.sorted l := by
  sorry

/-- #### 练习：1 星，选做 (selection_sort_correct')
在多重集规约框架下，证明 `selection_sort` 的完全正确性。 -/
theorem selection_sort_correct' :
    VFA.Multiset.is_a_sorting_algorithm' selection_sort := by
  sorry

end VFA.Selection
