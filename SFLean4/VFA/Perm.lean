import SFLean4.LF.IndProp

namespace VFA.Perm

open IndProp

/-!
# 《软件基础》(Software Foundations) 卷三：函数式算法验证 (VFA)

## 第一章：数值比较与置换技术基础 (Perm: Basic Techniques for Comparisons and Permutations)

在深入研究排序与搜索算法的形式化验证之前，我们需要建立两项核心的推理工具：
1. **自然数的不等式与大小比较推理**（在 Coq 中使用 `lia`，在 Lean 4 中使用强大的现代算术策略 `omega`）；
2. **列表的置换关系 (Permutation)**：判断两个列表是否具有完全相同的元素（仅排列顺序不同，元素重数保持一致）。

---

## 1. 自然数的大小关系与判定 (The Less-Than Order on Natural Numbers)
-/

/-- 大于等于的布尔判定函数 -/
def geb (n m : Nat) : Bool := m <= n

/-- 大于的布尔判定函数 -/
def gtb (n m : Nat) : Bool := m < n

scoped infix:70 " >=? " => geb
scoped infix:70 " >? " => gtb

/-!
### 1.1 算术求解策略：从手写归约到 `omega`

考虑如下不等式推导：
-/

theorem lia_example1 : ∀ i j k : Nat,
    i < j →
    ¬ (k - 3 ≤ j) →
    k > i := by
  intro i j k h1 h2
  omega

/-- 截断减法的性质反例：在自然数上 `k > k - 3` 并不对所有的 `k` 均成立（当 `k = 0` 时反例） -/
theorem truncated_subtraction : ¬ (∀ k : Nat, k > k - 3) := by
  intro contra
  have h := contra 0
  contradiction

theorem lia_example2 : ∀ i j k : Nat,
    i < j →
    ¬ (k - 3 ≤ j) →
    k > i := by
  intro i j k h1 h2
  omega

theorem lia_example_3 : ∀ (f : Nat → Nat → Nat) a b x y,
    f x y > a * b → f x y + 3 ≥ a * b := by
  intro f a b x y h
  omega

/- ################################################################# -/
/-! ## 2. 元素条件交换 (Swapping) -/
/- ################################################################# -/

/-- 若列表的前两个元素顺序颠倒，则将其交换；否则保持不变 -/
def maybe_swap (al : List Nat) : List Nat :=
  match al with
  | a :: b :: ar => if a >? b then b :: a :: ar else a :: b :: ar
  | _ => al

theorem maybe_swap_123 :
  maybe_swap [1, 2, 3] = [1, 2, 3] := by
  rfl

theorem maybe_swap_321 :
  maybe_swap [3, 2, 1] = [2, 3, 1] := by
  rfl

/-- `maybe_swap` 是幂等的：连续应用两次与应用一次完全等价 -/
theorem maybe_swap_idempotent : ∀ al : List Nat,
    maybe_swap (maybe_swap al) = maybe_swap al := by
  sorry

/- ################################################################# -/
/-! ## 3. 布尔反射 (Reflection) -/
/- ################################################################# -/

theorem eqb_reflect : ∀ x y : Nat, reflect (x = y) (x == y) := by
  intro x y
  cases h : (x == y) with
  | true =>
    apply reflect.ReflectT
    exact of_decide_eq_true h
  | false =>
    apply reflect.ReflectF
    exact of_decide_eq_false h

theorem ltb_reflect : ∀ x y : Nat, reflect (x < y) (decide (x < y)) := by
  intro x y
  cases h : (decide (x < y)) with
  | true =>
    apply reflect.ReflectT
    exact of_decide_eq_true h
  | false =>
    apply reflect.ReflectF
    exact of_decide_eq_false h

theorem leb_reflect : ∀ x y : Nat, reflect (x ≤ y) (decide (x ≤ y)) := by
  intro x y
  cases h : (decide (x ≤ y)) with
  | true =>
    apply reflect.ReflectT
    exact of_decide_eq_true h
  | false =>
    apply reflect.ReflectF
    exact of_decide_eq_false h

theorem gtb_reflect : ∀ x y : Nat, reflect (x > y) (gtb x y) := by
  intro x y
  dsimp [gtb]
  cases h : (decide (y < x)) with
  | true =>
    apply reflect.ReflectT
    exact of_decide_eq_true h
  | false =>
    apply reflect.ReflectF
    exact of_decide_eq_false h

theorem geb_reflect : ∀ x y : Nat, reflect (x ≥ y) (geb x y) := by
  intro x y
  dsimp [geb]
  cases h : (decide (y ≤ x)) with
  | true =>
    apply reflect.ReflectT
    exact of_decide_eq_true h
  | false =>
    apply reflect.ReflectF
    exact of_decide_eq_false h

theorem reflect_example1 : ∀ a : Nat,
    (if a < 5 then a else 2) < 6 := by
  intro a
  split <;> omega

theorem reflect_example1' : ∀ a : Nat,
    (if a < 5 then a else 2) < 6 := by
  intro a
  split <;> omega

theorem reflect_example2 : ∀ a : Nat,
    (if a < 5 then a else 2) < 6 := by
  intro a
  split <;> omega

/- ################################################################# -/
/-! ## 4. 列表置换关系 (Permutations) -/
/- ################################################################# -/

/-- 使用 Lean 4 内置的 `List.Perm` 形式化置换关系 -/
abbrev Permutation {A : Type} (l1 l2 : List A) : Prop := List.Perm l1 l2

/-!
#### 练习：2 星, standard (Permutation_properties)

思考置换关系应该具备的性质：
1. 长度守恒：`l1.Perm l2 → l1.length = l2.length`
2. 对称性：`l1.Perm l2 → l2.Perm l1`
3. 元素重数保持：非简单包含关系，`[1, 1]` 不是 `[1, 2]` 的置换。
-/
def manual_grade_for_Permutation_properties : Option (Nat × String) := none

/-- 置换重排演示示例 -/
theorem butterfly : ∀ b u t e r f l y : Nat,
  Permutation ([b, u, t, t, e, r] ++ [f, l, y]) ([f, l, u, t, t, e, r] ++ [b, y]) := by
  sorry

/-!
#### 练习：3 星, standard (permut_example)
-/
theorem permut_example : ∀ (a b : List Nat),
  Permutation (5 :: 6 :: a ++ b) ((5 :: b) ++ (6 :: a ++ ([] : List Nat))) := by
  sorry

/-!
#### 练习：2 星, standard (not_a_permutation)
-/
theorem not_a_permutation :
  ¬ Permutation [1, 1] [1, 2] := by
  sorry

/-- `maybe_swap` 产生的结果必然是原列表的一个置换 -/
theorem maybe_swap_perm : ∀ al : List Nat,
  Permutation al (maybe_swap al) := by
  sorry

/-- 判断列表的前两个元素是否按升序排列 -/
def first_le_second (al : List Nat) : Prop :=
  match al with
  | a :: b :: _ => a ≤ b
  | _ => True

/-- `maybe_swap` 正确性定理：既保持置换关系，又保证前两个元素已升序排好 -/
theorem maybe_swap_correct : ∀ al : List Nat,
    Permutation al (maybe_swap al) ∧ first_le_second (maybe_swap al) := by
  sorry

/- ################################################################# -/
/-! ## 5. 元素全称命题与置换保持 (Forall and Permutations) -/
/- ################################################################# -/

/-- 列表元素全称满足谓词的归纳定义（对齐 Coq 的 `Forall`） -/
inductive Forall {A : Type} (P : A → Prop) : List A → Prop where
  | Forall_nil : Forall P []
  | Forall_cons : ∀ (x : A) (l : List A), P x → Forall P l → Forall P (x :: l)

/-!
#### 练习：3 星, standard (Forall_perm)
-/
theorem Forall_perm : ∀ {A : Type} (f : A → Prop) al bl,
  Permutation al bl →
  Forall f al → Forall f bl := by
  sorry

end VFA.Perm
