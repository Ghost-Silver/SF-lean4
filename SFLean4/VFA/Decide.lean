import SFLean4.VFA.Perm

/-!
# 判定过程编程 (Decide: Programming with Decision Procedures)

在形式化证明与函数式算法中，我们常常需要沟通两个世界：
1. **命题世界（`Prop`）**：例如 $a < b$，用于逻辑断言与形式化规约，但不具备直接的计算解释；
2. **布尔/可计算世界（`Bool` / 构造性数据类型）**：例如 $a <? b$，可直接在程序中求值分支，但无法直接在证明上下文中提供蕴含前提。

连接这两个世界有两种经典技术：
- **布尔反射（Boolean Reflection）**：利用 `reflect P b` 归纳类型，将布尔值的 true/false 与命题 $P$ 的真伪对应（如第一章中的 `bdestruct`）；
- **带有证据的析取类型（`sumbool`，即 `{P} + {¬P}`）**：在 Lean 4 中表现为核心类型类 `Decidable P`（包含 `isTrue (h : P)` 与 `isFalse (h : ¬P)`）。

本章深入探讨两者的机制、计算性、不透明性（`Qed` vs `Defined`）以及在排序与成员关系判定中的应用。
-/

namespace VFA.Decide

open VFA.Perm

/-!
## 1. 利用 reflect 表征判定过程 (Using reflect to Characterize Decision Procedures)
-/

/-- 反射归纳类型：将命题 `P` 与布尔值 `b` 关联 -/
inductive reflect (P : Prop) : Bool → Type where
  | ReflectT : P → reflect P true
  | ReflectF : ¬ P → reflect P false

/-- 自然数严格小于关系的反射定理（定义于 Type） -/
def ltb_reflect (x y : Nat) : reflect (x < y) (decide (x < y)) := by
  cases h : (decide (x < y)) with
  | true =>
    apply reflect.ReflectT
    exact of_decide_eq_true h
  | false =>
    apply reflect.ReflectF
    exact of_decide_eq_false h

/-- 自然数小于等于关系的反射定理（定义于 Type） -/
def leb_reflect (x y : Nat) : reflect (x ≤ y) (decide (x ≤ y)) := by
  cases h : (decide (x ≤ y)) with
  | true =>
    apply reflect.ReflectT
    exact of_decide_eq_true h
  | false =>
    apply reflect.ReflectF
    exact of_decide_eq_false h

example : (decide (3 < 7) = true) := by
  rfl

/-- 利用反射类型在证明中进行分支推理（方法一：destruct）
由于 3 < 7 计算为 true，Lean 自动推断无需处理 ReflectF 分支 -/
theorem three_less_seven_1 : 3 < 7 := by
  have H := ltb_reflect 3 7
  cases H with
  | ReflectT P => exact P

/-- 利用反射类型在证明中进行分支推理（方法二：反演） -/
theorem three_less_seven_2 : 3 < 7 := by
  have H := ltb_reflect 3 7
  cases H with
  | ReflectT P => exact P

/-!
## 2. 利用 sumbool 表征判定过程 (Using sumbool to Characterize Decision Procedures)
-/

namespace ScratchPad

/-- 构造性命题或类型（Coq 的 `sumbool`） -/
inductive sumbool (A B : Prop) : Type where
  | left : A → sumbool A B
  | right : B → sumbool A B

notation:max "{" A "}" " + " "{" B "}" => sumbool A B

def t1 := { 3 < 7 } + { 3 > 2 }
theorem less37 : 3 < 7 := by omega
theorem greater23 : 3 > 2 := by omega

def v1a : t1 := sumbool.left less37
def v1b : t1 := sumbool.right greater23

def t2 := { 3 < 7 } + { 2 > 3 }
def v2a : t2 := sumbool.left less37

def t4 := ∀ a b : Nat, { a < b } + { ¬ (a < b) }

def v3 : { 3 < 7 } + { ¬ (3 < 7) } := sumbool.left less37

def is_3_less_7 : Bool :=
  match v3 with
  | sumbool.left _ => true
  | sumbool.right _ => false

#eval is_3_less_7  -- true

/-- 利用反射构建小于关系的判定过程 -/
def lt_dec (a b : Nat) : { a < b } + { ¬ (a < b) } :=
  match decide (a < b), ltb_reflect a b with
  | true, reflect.ReflectT P => sumbool.left P
  | false, reflect.ReflectF Q => sumbool.right Q

/-- 利用策略构建等价的判定过程 -/
def lt_dec' (a b : Nat) : { a < b } + { ¬ (a < b) } :=
  lt_dec a b

theorem lt_dec_equivalent (a b : Nat) : lt_dec a b = lt_dec' a b := by
  rfl

end ScratchPad

/-!
## 3. 标准库与插入排序中的判定过程 (sumbool in Standard Library)
-/

namespace ScratchPad2

open ScratchPad

/-- 小于判定过程 -/
def lt_dec (a b : Nat) : { a < b } + { ¬ (a < b) } :=
  if h : a < b then sumbool.left h else sumbool.right h

/-- 小于等于判定过程 -/
def le_dec (a b : Nat) : { a ≤ b } + { ¬ (a ≤ b) } :=
  if h : a ≤ b then sumbool.left h else sumbool.right h

/-- 使用 `le_dec` 判定过程编写的插入函数 -/
def insert (x : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => [x]
  | h :: t =>
    match le_dec x h with
    | sumbool.left _ => x :: h :: t
    | sumbool.right _ => h :: insert x t

/-- 插入排序 -/
def sort (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)

/-- 列表有序谓词 -/
inductive sorted : List Nat → Prop where
  | sorted_nil : sorted []
  | sorted_1 : ∀ x, sorted [x]
  | sorted_cons : ∀ x y l, x ≤ y → sorted (y :: l) → sorted (x :: y :: l)

/-!
### 练习：insert_sorted_le_dec (2 星)
证明使用 `le_dec` 的插入排序正确维护列表有序性。
-/
theorem insert_sorted (a : Nat) (l : List Nat) (h : sorted l) :
    sorted (insert a l) := by
  sorry

/-!
### 公理化与计算性讨论
-/

/-- 排中律公理（命题级） -/
axiom lt_dec_axiom_1 : ∀ i j : Nat, i < j ∨ ¬ (i < j)

/-- 判定性排中公理（数据级） -/
axiom lt_dec_axiom_2 : ∀ i j : Nat, { i < j } + { ¬ (i < j) }

/-- 使用公理定义函数（因公理无计算规约规则，标记为 noncomputable） -/
noncomputable def max_with_axiom (i j : Nat) : Nat :=
  match lt_dec_axiom_2 i j with
  | sumbool.left _ => j
  | sumbool.right _ => i

theorem prove_with_max_axiom : max_with_axiom 3 7 = 7 := by
  unfold max_with_axiom
  cases lt_dec_axiom_2 3 7 with
  | left h => rfl
  | right h =>
    exfalso
    apply h
    omega

end ScratchPad2

open ScratchPad
open ScratchPad2

/-!
## 4. 列表成员关系的判定过程 (List Membership Decidability)
-/

/-- 列表元素包含谓词 -/
def In (x : Nat) (l : List Nat) : Prop := x ∈ l

/-- 列表相等性的判定过程 -/
def list_nat_eq_dec (al bl : List Nat) : { al = bl } + { al ≠ bl } :=
  if h : al = bl then sumbool.left h else sumbool.right h

#eval match list_nat_eq_dec [1, 3, 4] [1, 4, 3] with | sumbool.left _ => true | sumbool.right _ => false  -- false
#eval match list_nat_eq_dec [1, 3, 4] [1, 3, 4] with | sumbool.left _ => true | sumbool.right _ => false  -- true

/-!
### 练习：list_nat_in (2 星)
实现自然数列表成员关系的判定过程。
-/
def list_nat_in (i : Nat) (al : List Nat) : { In i al } + { ¬ In i al } :=
  match al with
  | [] => sumbool.right (by intro h; cases h)
  | h :: t =>
    if heq : i = h then
      sumbool.left (heq ▸ List.Mem.head t)
    else
      match list_nat_in i t with
      | sumbool.left hin => sumbool.left (List.Mem.tail h hin)
      | sumbool.right hnin =>
        sumbool.right (by
          intro hmem
          cases hmem with
          | head => exact heq rfl
          | tail _ hmem' => exact hnin hmem')

example :
    (match list_nat_in 4 [3, 1, 4, 1, 5, 9, 2, 6] with
     | sumbool.left _ => true
     | sumbool.right _ => false) = true := by
  decide

end VFA.Decide
