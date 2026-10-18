---
title: "Sort: 插入排序及其形式化规约：有序性与置换保持"
---

```lean
import SFLean4.VFA.Perm

namespace VFA.Sort

open VFA.Perm
```

# 《软件基础》(Software Foundations) 卷三：函数式算法验证 (VFA)

## 第二章：插入排序 (Sort: Insertion Sort)

排序算法可在期望 $O(N \log N)$ 时间内完成（如快速排序、归并排序、堆排序等）。
但对于规模较小的输入，简单且具有二次时间复杂度 $O(N^2)$ 的算法（如插入排序）往往常数极小且实际运行速度更快。
更重要的是，插入排序逻辑直观，更易于用纯函数式风格实现并开展完备的形式化验证。

本章将：
1. 实现函数式链表上的插入排序程序（`insert` 与 `sort`）；
2. 形式化规约“已排序”的数学定义（归纳关系 `sorted` 与索引定义 `sorted'` / `sorted''`）；
3. 严格形式化证明插入排序的功能正确性：**保序性**（输出为有序列表）与**置换性**（输出是输入的合法排列，不增删元素）。

```lean
/- ################################################################# -/
```

## 1. 插入排序程序实现 (The Insertion-Sort Program)

```lean
/- ################################################################# -/

/-- 向已排序的列表中插入一个元素，使其仍然保持升序 -/
def insert (i : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => [i]
  | h :: t => if i <= h then i :: h :: t else h :: insert i t

/-- 插入排序主函数：对列表进行结构归纳递归排序 -/
def sort (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)

theorem sort_pi :
  sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by
  rfl

/- ################################################################# -/
```

## 2. 正确性规约 (Specification of Correctness)

```lean
/- ################################################################# -/

/-- 核心规约：已排序列表的归纳定义 -/
inductive sorted : List Nat → Prop where
  | sorted_nil : sorted []
  | sorted_1 : ∀ x, sorted [x]
  | sorted_cons : ∀ x y l, x ≤ y → sorted (y :: l) → sorted (x :: y :: l)

/-- 提供默认返回值的列表安全索引取值函数（对齐 Coq 的 `nth`） -/
def nth {A : Type} (n : Nat) (l : List A) (default : A) : A :=
  (l[n]?).getD default

/-- 列表索引安全取值函数（对齐 Coq 的 `nth_error`） -/
def nth_error {A : Type} (l : List A) (n : Nat) : Option A :=
  l[n]?

/-- 基于显式范围界定和默认值的有序性定义 -/
def sorted'' (al : List Nat) : Prop :=
  ∀ i j, i < j ∧ j < al.length →
    nth i al 0 ≤ nth j al 0

/-- 基于安全索引 `nth_error` 的等价有序性定义 -/
def sorted' (al : List Nat) : Prop :=
  ∀ i j iv jv, i < j →
    nth_error al i = some iv →
    nth_error al j = some jv →
    iv ≤ jv

/-- 排序算法的整体正确性规约：输出必须既是有序的，又是原输入的一个置换 -/
def is_a_sorting_algorithm (f : List Nat → List Nat) : Prop :=
  ∀ al, Permutation al (f al) ∧ sorted (f al)

/- ################################################################# -/
```

## 3. 正确性证明 (Proof of Correctness)

```lean
/- ################################################################# -/
```

### 🎯 练习：`insert_sorted` <Badge type="warning" text="3 星 · standard" />
证明插入操作保持列表的有序性。

```lean
theorem insert_sorted : ∀ a l,
  sorted l → sorted (insert a l) := by
  sorry
```

### 🎯 练习：`sort_sorted` <Badge type="info" text="2 星 · standard" />
证明插入排序的结果必然有序。

```lean
theorem sort_sorted : ∀ l, sorted (sort l) := by
  sorry
```

### 🎯 练习：`insert_perm` <Badge type="warning" text="3 星 · standard" />
证明插入单个元素所产生的列表是 `(x :: l)` 的合法置换。

```lean
theorem insert_perm : ∀ x l,
  Permutation (x :: l) (insert x l) := by
  sorry
```

### 🎯 练习：`sort_perm` <Badge type="warning" text="3 星 · standard" />
证明排序后的列表是原列表的置换。

```lean
theorem sort_perm : ∀ l, Permutation l (sort l) := by
  sorry
```

### 🎯 练习：`insertion_sort_correct` <Badge type="tip" text="1 星 · standard" />
综合证明插入排序满足排序算法的完整形式化规约！

```lean
theorem insertion_sort_correct :
  is_a_sorting_algorithm sort := by
  sorry

/- ################################################################# -/
```

## 4. 规约的等价性验证 (Validating the Specification)

```lean
/- ################################################################# -/
```

### 🎯 练习：`sorted_sorted'` <Badge type="danger" text="4 星 · advanced" />
证明归纳定义的有序性蕴含基于索引的有序性定义。

```lean
theorem sorted_sorted' : ∀ al, sorted al → sorted' al := by
  sorry
```

### 🎯 练习：`sorted'_sorted` <Badge type="warning" text="3 星 · advanced" />
证明基于索引的有序性定义蕴含归纳定义的有序性。

```lean
theorem sorted'_sorted : ∀ al, sorted' al → sorted al := by
  sorry

/- ################################################################# -/
```

## 5. 基于替代规约直接证明正确性 (Alternative Spec)

```lean
/- ################################################################# -/
```

### 🎯 练习：`insert_sorted'` <Badge type="danger" text="5 星 · standard, optional" />

```lean
theorem nth_error_insert : ∀ l a i iv,
  nth_error (insert a l) i = some iv →
  a = iv ∨ ∃ i', nth_error l i' = some iv := by
  sorry

theorem insert_sorted' : ∀ a l,
  sorted' l → sorted' (insert a l) := by
  sorry

theorem sort_sorted' : ∀ l, sorted' (sort l) := by
  sorry

end VFA.Sort
```
