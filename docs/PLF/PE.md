---
title: "PE: 偏评估与在线特化：符号执行与流程图特化"
---

```lean
import SFLean4.PLF.Maps
import SFLean4.LF.Imp
import SFLean4.LF.IndProp
import SFLean4.PLF.Smallstep

namespace PLF.PE

open Maps
open Imp
open IndProp
open Smallstep
```

# 《软件基础》(Software Foundations) 卷二：程序语言基础 (PLF)

## 偏求值与程序特化 (PE: Partial Evaluation)

在前面的章节中，我们学习了常量折叠（Constant Folding），它能对显式常量进行化简（例如将 `Y := 3 + 1` 简化为 `Y := 4`）。
但常量折叠无法沿着数据流传播已知的常量信息。例如对于序列：
```
X := 3; Y := X + 1
```
常规常量折叠并不能直接将其化简为：
```
X := 3; Y := 4
```
因为在处理到 `Y` 的赋值时，系统已经遗忘了 `X` 在此处的静态已知值 `3`。

**偏求值（Partial Evaluation，亦称在线特化 / Program Specialization）** 正是这一思想的推广：
当一个程序的**部分输入**在编译期已知（称为**静态数据 (Static Data)**），而其余输入未知（称为**动态数据 (Dynamic Data)**）时，
偏求值器在已知数据上“预先执行”程序，展开循环、消除已知分支，从而生成一个更精简、更高效的**剩余程序 (Residual Program)**。

```lean
/- ################################################################# -/
```

## 1. 推广常量折叠：部分状态 (Partial States)

```lean
/- ################################################################# -/

/-- 部分状态：以具象列表 `List (String × Nat)` 记录当前已确定取值的变量及其静态数值 -/
abbrev pe_state := List (String × Nat)

/-- 在部分状态中查找变量的值 -/
def pe_lookup (pe_st : pe_state) (V : String) : Option Nat :=
  match pe_st with
  | [] => none
  | (V', n') :: rest =>
    if V == V' then some n'
    else pe_lookup rest V

/-- 空部分状态：表示对所有变量的值一无所知 -/
def empty_pe_state : pe_state := []

/-- 列表成员谓词 -/
def In {A : Type} (a : A) : List A → Prop
  | [] => False
  | b :: m => b = a ∨ In a m

/-- 若在部分状态中查找到某变量，则该变量必然存在于状态列表的键域中 -/
theorem pe_domain : ∀ (pe_st : pe_state) (V : String) (n : Nat),
  pe_lookup pe_st V = some n →
  In V (pe_st.map Prod.fst) := by
  intro pe_st V n h
  induction pe_st with
  | nil => contradiction
  | cons p rest ih =>
    obtain ⟨V', n'⟩ := p
    dsimp [pe_lookup] at h
    split at h
    · rename_i heq
      have heq' : V = V' := of_decide_eq_true heq
      subst heq'
      left
      rfl
    · right
      exact ih h

/-- 检验元素是否属于列表的布尔谓词 -/
def inb {A : Type} (eqb : A → A → Bool) (a : A) (l : List A) : Bool :=
  match l with
  | [] => false
  | a' :: l' => eqb a a' || inb eqb a l'

/-- `inb` 与命题列表成员 `In` 的布尔反射定理 -/
theorem inbP : ∀ (A : Type) (eqb : A → A → Bool),
  (∀ a1 a2, reflect (a1 = a2) (eqb a1 a2)) →
  ∀ a l, reflect (In a l) (inb eqb a l) := by
  sorry

/- ################################################################# -/
```

## 2. 算术表达式的偏求值 (Arithmetic Expressions)

```lean
/- ################################################################# -/

/-- 算术表达式的偏求值函数：结合部分状态折叠已知变量与常量 -/
def pe_aexp (pe_st : pe_state) (a : aexp) : aexp :=
  match a with
  | aexp.ANum n => aexp.ANum n
  | aexp.AId i =>
    match pe_lookup pe_st i with
    | some n => aexp.ANum n
    | none => aexp.AId i
  | aexp.APlus a1 a2 =>
    match pe_aexp pe_st a1, pe_aexp pe_st a2 with
    | aexp.ANum n1, aexp.ANum n2 => aexp.ANum (n1 + n2)
    | a1', a2' => aexp.APlus a1' a2'
  | aexp.AMinus a1 a2 =>
    match pe_aexp pe_st a1, pe_aexp pe_st a2 with
    | aexp.ANum n1, aexp.ANum n2 => aexp.ANum (n1 - n2)
    | a1', a2' => aexp.AMinus a1' a2'
  | aexp.AMult a1 a2 =>
    match pe_aexp pe_st a1, pe_aexp pe_st a2 with
    | aexp.ANum n1, aexp.ANum n2 => aexp.ANum (n1 * n2)
    | a1', a2' => aexp.AMult a1' a2'

theorem test_pe_aexp1 :
  pe_aexp ([(X, 3)] : pe_state) (aexp.APlus (aexp.APlus X 1) Y) = aexp.APlus 4 Y := by
  rfl

theorem text_pe_aexp2 :
  pe_aexp ([(Y, 3)] : pe_state) (aexp.APlus (aexp.APlus X 1) Y) = aexp.APlus (aexp.APlus X 1) 3 := by
  rfl

/-- 具体状态与部分状态的一致性：部分状态中记录的变量值必须与全状态完全吻合 -/
def pe_consistent (st : state) (pe_st : pe_state) : Prop :=
  ∀ V n, some n = pe_lookup pe_st V → st V = n

/-- 弱正确性：一致状态下求值结果不变 -/
theorem pe_aexp_correct_weak : ∀ st pe_st, pe_consistent st pe_st →
  ∀ a, aeval st a = aeval st (pe_aexp pe_st a) := by
  sorry

/-- 将部分状态中的已知赋值叠加覆盖到全域状态上 -/
def pe_update (st : state) (pe_st : pe_state) : state :=
  match pe_st with
  | [] => st
  | (V, n) :: pe_st' => (V !-> n; pe_update st pe_st')

theorem test_pe_update :
  pe_update (Y !-> 1) ([(X, 3), (Z, 2)] : pe_state) = (X !-> 3; Z !-> 2; Y !-> 1) := by
  rfl

/-- 字符串不相等时布尔判等为假 -/
theorem false_eqb_string : ∀ x y : String, x ≠ y → (x == y) = false := by
  intro x y h
  simp [h]

/-- `pe_update` 的查找语义正确性 -/
theorem pe_update_correct : ∀ st pe_st V0,
  pe_update st pe_st V0 =
  match pe_lookup pe_st V0 with
  | some n => n
  | none => st V0 := by
  sorry

/-- 覆盖更新后的状态必然与该部分状态一致 -/
theorem pe_update_consistent : ∀ st pe_st,
  pe_consistent (pe_update st pe_st) pe_st := by
  sorry

/-- 若原状态已经一致，则叠加覆盖不会产生变化 -/
theorem pe_consistent_update : ∀ st pe_st,
  pe_consistent st pe_st → ∀ V, st V = pe_update st pe_st V := by
  sorry

/-- 算术表达式偏求值的强正确性定理 -/
theorem pe_aexp_correct : ∀ (pe_st : pe_state) (a : aexp) (st : state),
  aeval (pe_update st pe_st) a = aeval st (pe_aexp pe_st a) := by
  sorry

/- ################################################################# -/
```

## 3. 布尔表达式的偏求值 (Boolean Expressions)

```lean
/- ################################################################# -/

/-- 布尔表达式的偏求值函数 -/
def pe_bexp (pe_st : pe_state) (b : bexp) : bexp :=
  match b with
  | bexp.BTrue => bexp.BTrue
  | bexp.BFalse => bexp.BFalse
  | bexp.BEq a1 a2 =>
    match pe_aexp pe_st a1, pe_aexp pe_st a2 with
    | aexp.ANum n1, aexp.ANum n2 => if n1 == n2 then bexp.BTrue else bexp.BFalse
    | a1', a2' => bexp.BEq a1' a2'
  | bexp.BNeq a1 a2 =>
    match pe_aexp pe_st a1, pe_aexp pe_st a2 with
    | aexp.ANum n1, aexp.ANum n2 => if !(n1 == n2) then bexp.BTrue else bexp.BFalse
    | a1', a2' => bexp.BNeq a1' a2'
  | bexp.BLe a1 a2 =>
    match pe_aexp pe_st a1, pe_aexp pe_st a2 with
    | aexp.ANum n1, aexp.ANum n2 => if n1 <= n2 then bexp.BTrue else bexp.BFalse
    | a1', a2' => bexp.BLe a1' a2'
  | bexp.BGt a1 a2 =>
    match pe_aexp pe_st a1, pe_aexp pe_st a2 with
    | aexp.ANum n1, aexp.ANum n2 => if n1 <= n2 then bexp.BFalse else bexp.BTrue
    | a1', a2' => bexp.BGt a1' a2'
  | bexp.BNot b1 =>
    match pe_bexp pe_st b1 with
    | bexp.BTrue => bexp.BFalse
    | bexp.BFalse => bexp.BTrue
    | b1' => bexp.BNot b1'
  | bexp.BAnd b1 b2 =>
    match pe_bexp pe_st b1, pe_bexp pe_st b2 with
    | bexp.BTrue, bexp.BTrue => bexp.BTrue
    | bexp.BTrue, bexp.BFalse => bexp.BFalse
    | bexp.BFalse, bexp.BTrue => bexp.BFalse
    | bexp.BFalse, bexp.BFalse => bexp.BFalse
    | b1', b2' => bexp.BAnd b1' b2'

theorem test_pe_bexp1 :
  pe_bexp ([(X, 3)] : pe_state) (bexp.BNot (bexp.BLe X 3)) = bexp.BFalse := by
  rfl

theorem test_pe_bexp2 : ∀ b : bexp,
  b = bexp.BNot (bexp.BLe X (aexp.APlus X 1)) →
  pe_bexp [] b = b := by
  intro b hb
  subst hb
  rfl

/-- 布尔表达式偏求值的正确性定理 -/
theorem pe_bexp_correct : ∀ (pe_st : pe_state) (b : bexp) (st : state),
  beval (pe_update st pe_st) b = beval st (pe_bexp pe_st b) := by
  sorry

/- ################################################################# -/
```

## 4. 无循环命令的偏求值 (Commands Without Loops)

```lean
/- ################################################################# -/

/-- 从部分状态中移除指定变量（使其重新变为动态未知） -/
def pe_remove (pe_st : pe_state) (V : String) : pe_state :=
  match pe_st with
  | [] => []
  | (V', n') :: rest =>
    if V == V' then pe_remove rest V
    else (V', n') :: pe_remove rest V

theorem pe_remove_correct : ∀ pe_st V V0,
  pe_lookup (pe_remove pe_st V) V0 = if V == V0 then none else pe_lookup pe_st V0 := by
  sorry

/-- 向部分状态添加或更新一个静态常量赋值 -/
def pe_add (pe_st : pe_state) (V : String) (n : Nat) : pe_state :=
  (V, n) :: pe_remove pe_st V

theorem pe_add_correct : ∀ pe_st V n V0,
  pe_lookup (pe_add pe_st V n) V0 = if V == V0 then some n else pe_lookup pe_st V0 := by
  sorry

theorem pe_update_update_remove : ∀ st pe_st V n,
  (V !-> n; pe_update st pe_st) = pe_update (V !-> n; st) (pe_remove pe_st V) := by
  sorry

theorem pe_update_update_add : ∀ st pe_st V n,
  (V !-> n; pe_update st pe_st) = pe_update st (pe_add pe_st V n) := by
  sorry

/-- 检验两个部分状态在某变量处是否存在分歧 -/
def pe_disagree_at (pe_st1 pe_st2 : pe_state) (V : String) : Bool :=
  match pe_lookup pe_st1 V, pe_lookup pe_st2 V with
  | some x, some y => !(x == y)
  | none, none => false
  | _, _ => true

theorem pe_disagree_domain : ∀ (pe_st1 pe_st2 : pe_state) (V : String),
  true = pe_disagree_at pe_st1 pe_st2 V →
  In V (pe_st1.map Prod.fst ++ pe_st2.map Prod.fst) := by
  sorry

/-- 列表元素去重辅助函数 -/
def pe_unique (l : List String) : List String :=
  match l with
  | [] => []
  | x :: rest =>
    x :: (pe_unique rest).filter (fun y => !(x == y))

theorem pe_unique_correct : ∀ l x,
  In x l ↔ In x (pe_unique l) := by
  sorry

/-- 计算两个部分状态产生分歧的所有变量列表 -/
def pe_compare (pe_st1 pe_st2 : pe_state) : List String :=
  pe_unique ((pe_st1.map Prod.fst ++ pe_st2.map Prod.fst).filter (pe_disagree_at pe_st1 pe_st2))

theorem pe_compare_correct : ∀ pe_st1 pe_st2 V,
  pe_lookup pe_st1 V = pe_lookup pe_st2 V ↔
  ¬ In V (pe_compare pe_st1 pe_st2) := by
  sorry

/-- 批量从部分状态中移除一组变量 -/
def pe_removes (pe_st : pe_state) (ids : List String) : pe_state :=
  match ids with
  | [] => pe_st
  | V :: rest => pe_remove (pe_removes pe_st rest) V

theorem pe_removes_correct : ∀ pe_st ids V,
  pe_lookup (pe_removes pe_st ids) V =
  if inb (· == ·) V ids then none else pe_lookup pe_st V := by
  sorry

theorem pe_compare_removes : ∀ pe_st1 pe_st2 V,
  pe_lookup (pe_removes pe_st1 (pe_compare pe_st1 pe_st2)) V =
  pe_lookup (pe_removes pe_st2 (pe_compare pe_st1 pe_st2)) V := by
  sorry

theorem pe_compare_update : ∀ pe_st1 pe_st2 st,
  pe_update st (pe_removes pe_st1 (pe_compare pe_st1 pe_st2)) =
  pe_update st (pe_removes pe_st2 (pe_compare pe_st1 pe_st2)) := by
  sorry

/-- 将分歧变量列表转化为相应的静态赋值命令序列，用于动态分支合并补偿 -/
def assign (pe_st : pe_state) (ids : List String) : com :=
  match ids with
  | [] => SKIP
  | V :: rest =>
    match pe_lookup pe_st V with
    | some n => (assign pe_st rest ;; (V ::= aexp.ANum n))
    | none => assign pe_st rest

/-- 静态赋值补偿命令序列对全域状态的作用效果 -/
def assigned (pe_st : pe_state) (ids : List String) (st : state) : state :=
  fun V =>
    if inb (· == ·) V ids then
      match pe_lookup pe_st V with
      | some n => n
      | none => st V
    else st V

theorem assign_removes : ∀ pe_st ids st,
  pe_update st pe_st =
  pe_update (assigned pe_st ids st) (pe_removes pe_st ids) := by
  sorry

theorem ceval_extensionality : ∀ c st st1 st2,
  (st =[ c ]=> st1) → (∀ V, st1 V = st2 V) → (st =[ c ]=> st2) := by
  sorry

theorem eval_assign : ∀ pe_st ids st,
  st =[ assign pe_st ids ]=> assigned pe_st ids st := by
  sorry

/-- 命令偏求值关系：`c / pe_st ==> c' / pe_st'` -/
inductive pe_com : com → pe_state → com → pe_state → Prop where
  | PE_Skip : ∀ pe_st,
      pe_com SKIP pe_st SKIP pe_st
  | PE_AsgnStatic : ∀ pe_st a1 (n1 : Nat) l,
      pe_aexp pe_st a1 = aexp.ANum n1 →
      pe_com (l ::= a1) pe_st SKIP (pe_add pe_st l n1)
  | PE_AsgnDynamic : ∀ pe_st a1 a1' l,
      pe_aexp pe_st a1 = a1' →
      (∀ n : Nat, a1' ≠ aexp.ANum n) →
      pe_com (l ::= a1) pe_st (l ::= a1') (pe_remove pe_st l)
  | PE_Seq : ∀ pe_st pe_st' pe_st'' c1 c2 c1' c2',
      pe_com c1 pe_st c1' pe_st' →
      pe_com c2 pe_st' c2' pe_st'' →
      pe_com (c1 ;; c2) pe_st (c1' ;; c2') pe_st''
  | PE_IfTrue : ∀ pe_st pe_st' b1 c1 c2 c1',
      pe_bexp pe_st b1 = bexp.BTrue →
      pe_com c1 pe_st c1' pe_st' →
      pe_com (TEST b1 THEN c1 ELSE c2 FI) pe_st c1' pe_st'
  | PE_IfFalse : ∀ pe_st pe_st' b1 c1 c2 c2',
      pe_bexp pe_st b1 = bexp.BFalse →
      pe_com c2 pe_st c2' pe_st' →
      pe_com (TEST b1 THEN c1 ELSE c2 FI) pe_st c2' pe_st'
  | PE_If : ∀ pe_st pe_st1 pe_st2 b1 c1 c2 c1' c2',
      pe_bexp pe_st b1 ≠ bexp.BTrue →
      pe_bexp pe_st b1 ≠ bexp.BFalse →
      pe_com c1 pe_st c1' pe_st1 →
      pe_com c2 pe_st c2' pe_st2 →
      pe_com (TEST b1 THEN c1 ELSE c2 FI) pe_st
        (TEST pe_bexp pe_st b1
         THEN (c1' ;; assign pe_st1 (pe_compare pe_st1 pe_st2))
         ELSE (c2' ;; assign pe_st2 (pe_compare pe_st1 pe_st2)) FI)
        (pe_removes pe_st1 (pe_compare pe_st1 pe_st2))

theorem pe_example1 :
  pe_com (X ::= 3 ;; Y ::= Z * (X + X)) []
    (SKIP ;; (Y ::= Z * 6)) ([(X, 3)] : pe_state) := by
  sorry

theorem pe_example2 :
  pe_com (X ::= 3 ;; TEST (bexp.BLe X 4) THEN X ::= 4 ELSE SKIP FI) []
    (SKIP ;; SKIP) ([(X, 4)] : pe_state) := by
  sorry

theorem pe_example3 :
  pe_com (X ::= 3 ;;
          TEST (bexp.BLe Y 4)
          THEN (Y ::= 4 ;; TEST (bexp.BEq X Y) THEN Y ::= 999 ELSE SKIP FI)
          ELSE SKIP FI) []
    (SKIP ;;
     TEST (bexp.BLe Y 4)
     THEN ((SKIP ;; SKIP) ;; (SKIP ;; (Y ::= 4)))
     ELSE (SKIP ;; SKIP) FI)
    ([(X, 3)] : pe_state) := by
  sorry

/-- 偏求值剩余程序的联合大步执行关系 -/
inductive pe_ceval (c' : com) (pe_st' : pe_state) (st : state) (st'' : state) : Prop where
  | pe_ceval_intro : ∀ st',
      (st =[ c' ]=> st') →
      pe_update st' pe_st' = st'' →
      pe_ceval c' pe_st' st st''

/-- 完备性定理：原程序在覆盖状态上的执行均可在剩余程序中重现 -/
theorem pe_com_complete :
  ∀ c pe_st pe_st' c', pe_com c pe_st c' pe_st' →
  ∀ st st'',
  (pe_update st pe_st =[ c ]=> st'') →
  pe_ceval c' pe_st' st st'' := by
  sorry

/-- 可靠性定理：剩余程序的执行完全忠实于原程序语义 -/
theorem pe_com_sound :
  ∀ c pe_st pe_st' c', pe_com c pe_st c' pe_st' →
  ∀ st st'',
  pe_ceval c' pe_st' st st'' →
  (pe_update st pe_st =[ c ]=> st'') := by
  sorry

/-- 主定理：命令偏求值的双向语义保持定理 -/
theorem pe_com_correct :
  ∀ c pe_st pe_st' c', pe_com c pe_st c' pe_st' →
  ∀ st st'',
  (pe_update st pe_st =[ c ]=> st'') ↔
  pe_ceval c' pe_st' st st'' := by
  sorry

/- ################################################################# -/
```

## 5. 循环语句的偏求值 (Partial Evaluation of Loops)

```lean
/- ################################################################# -/

namespace Loop

/-- 支持循环展开与在线卷起的偏求值关系 -/
inductive pe_com : com → pe_state → com → pe_state → com → Prop where
  | PE_Skip : ∀ pe_st,
      pe_com SKIP pe_st SKIP pe_st SKIP
  | PE_AsgnStatic : ∀ pe_st a1 (n1 : Nat) l,
      pe_aexp pe_st a1 = aexp.ANum n1 →
      pe_com (l ::= a1) pe_st SKIP (pe_add pe_st l n1) SKIP
  | PE_AsgnDynamic : ∀ pe_st a1 a1' l,
      pe_aexp pe_st a1 = a1' →
      (∀ n : Nat, a1' ≠ aexp.ANum n) →
      pe_com (l ::= a1) pe_st (l ::= a1') (pe_remove pe_st l) SKIP
  | PE_Seq : ∀ pe_st pe_st' pe_st'' c1 c2 c1' c2' c'',
      pe_com c1 pe_st c1' pe_st' SKIP →
      pe_com c2 pe_st' c2' pe_st'' c'' →
      pe_com (c1 ;; c2) pe_st (c1' ;; c2') pe_st'' c''
  | PE_IfTrue : ∀ pe_st pe_st' b1 c1 c2 c1' c'',
      pe_bexp pe_st b1 = bexp.BTrue →
      pe_com c1 pe_st c1' pe_st' c'' →
      pe_com (TEST b1 THEN c1 ELSE c2 FI) pe_st c1' pe_st' c''
  | PE_IfFalse : ∀ pe_st pe_st' b1 c1 c2 c2' c'',
      pe_bexp pe_st b1 = bexp.BFalse →
      pe_com c2 pe_st c2' pe_st' c'' →
      pe_com (TEST b1 THEN c1 ELSE c2 FI) pe_st c2' pe_st' c''
  | PE_If : ∀ pe_st pe_st1 pe_st2 b1 c1 c2 c1' c2' c'',
      pe_bexp pe_st b1 ≠ bexp.BTrue →
      pe_bexp pe_st b1 ≠ bexp.BFalse →
      pe_com c1 pe_st c1' pe_st1 c'' →
      pe_com c2 pe_st c2' pe_st2 c'' →
      pe_com (TEST b1 THEN c1 ELSE c2 FI) pe_st
        (TEST pe_bexp pe_st b1
         THEN (c1' ;; assign pe_st1 (pe_compare pe_st1 pe_st2))
         ELSE (c2' ;; assign pe_st2 (pe_compare pe_st1 pe_st2)) FI)
        (pe_removes pe_st1 (pe_compare pe_st1 pe_st2))
        c''
  | PE_WhileFalse : ∀ pe_st b1 c1,
      pe_bexp pe_st b1 = bexp.BFalse →
      pe_com (WHILE b1 DO c1 END) pe_st SKIP pe_st SKIP
  | PE_WhileTrue : ∀ pe_st pe_st' pe_st'' b1 c1 c1' c2' c2'',
      pe_bexp pe_st b1 = bexp.BTrue →
      pe_com c1 pe_st c1' pe_st' SKIP →
      pe_com (WHILE b1 DO c1 END) pe_st' c2' pe_st'' c2'' →
      pe_compare pe_st pe_st'' ≠ ([] : List String) →
      pe_com (WHILE b1 DO c1 END) pe_st (c1' ;; c2') pe_st'' c2''
  | PE_While : ∀ pe_st pe_st' pe_st'' b1 c1 c1' c2' c2'',
      pe_bexp pe_st b1 ≠ bexp.BFalse →
      pe_bexp pe_st b1 ≠ bexp.BTrue →
      pe_com c1 pe_st c1' pe_st' SKIP →
      pe_com (WHILE b1 DO c1 END) pe_st' c2' pe_st'' c2'' →
      pe_compare pe_st pe_st'' ≠ ([] : List String) →
      (c2'' = SKIP ∨ c2'' = (WHILE b1 DO c1 END)) →
      pe_com (WHILE b1 DO c1 END) pe_st
        (TEST pe_bexp pe_st b1
         THEN (c1' ;; c2' ;; assign pe_st'' (pe_compare pe_st pe_st''))
         ELSE assign pe_st (pe_compare pe_st pe_st'') FI)
        (pe_removes pe_st (pe_compare pe_st pe_st''))
        c2''
  | PE_WhileFixedEnd : ∀ pe_st b1 c1,
      pe_bexp pe_st b1 ≠ bexp.BFalse →
      pe_com (WHILE b1 DO c1 END) pe_st SKIP pe_st (WHILE b1 DO c1 END)
  | PE_WhileFixedLoop : ∀ pe_st pe_st' pe_st'' b1 c1 c1' c2',
      pe_bexp pe_st b1 = bexp.BTrue →
      pe_com c1 pe_st c1' pe_st' SKIP →
      pe_com (WHILE b1 DO c1 END) pe_st' c2' pe_st'' (WHILE b1 DO c1 END) →
      pe_compare pe_st pe_st'' = ([] : List String) →
      pe_com (WHILE b1 DO c1 END) pe_st (WHILE bexp.BTrue DO SKIP END) pe_st SKIP
  | PE_WhileFixed : ∀ pe_st pe_st' pe_st'' b1 c1 c1' c2',
      pe_bexp pe_st b1 ≠ bexp.BFalse →
      pe_bexp pe_st b1 ≠ bexp.BTrue →
      pe_com c1 pe_st c1' pe_st' SKIP →
      pe_com (WHILE b1 DO c1 END) pe_st' c2' pe_st'' (WHILE b1 DO c1 END) →
      pe_compare pe_st pe_st'' = ([] : List String) →
      pe_com (WHILE b1 DO c1 END) pe_st (WHILE pe_bexp pe_st b1 DO c1' ;; c2' END) pe_st SKIP

/-- 重复平方循环示例程序 -/
def square_loop : com :=
  WHILE (bexp.BLe 1 X) DO
    (Y ::= Y * Y ;;
     X ::= X - 1)
  END

theorem pe_loop_example1 :
  pe_com square_loop []
    (WHILE (bexp.BLe 1 X) DO
       ((Y ::= Y * Y ;; X ::= X - 1) ;; SKIP)
     END) [] SKIP := by
  sorry

theorem pe_loop_example2 :
  pe_com (X ::= 3 ;; square_loop) []
    (SKIP ;;
     ((Y ::= Y * Y ;; SKIP) ;;
      ((Y ::= Y * Y ;; SKIP) ;;
       ((Y ::= Y * Y ;; SKIP) ;; SKIP)))) ([(X, 0)] : pe_state) SKIP := by
  sorry

theorem pe_loop_example3 :
  pe_com (Z ::= 3 ;; subtract_slowly) []
    (SKIP ;;
     TEST (bexp.BNeq X 0)
     THEN ((SKIP ;; X ::= X - 1) ;;
           TEST (bexp.BNeq X 0)
           THEN ((SKIP ;; X ::= X - 1) ;;
                 TEST (bexp.BNeq X 0)
                 THEN ((SKIP ;; X ::= X - 1) ;;
                       WHILE (bexp.BNeq X 0) DO (SKIP ;; X ::= X - 1) ;; SKIP END ;;
                       (SKIP ;; Z ::= 0))
                 ELSE (SKIP ;; Z ::= 1) FI ;;
                 SKIP)
           ELSE (SKIP ;; Z ::= 2) FI ;;
           SKIP)
     ELSE (SKIP ;; Z ::= 3) FI) [] SKIP := by
  sorry

theorem pe_loop_example4 :
  pe_com (X ::= 0 ;;
          WHILE (bexp.BLe X 2) DO
            X ::= 1 - X
          END) []
    (SKIP ;; WHILE bexp.BTrue DO SKIP END) ([(X, 0)] : pe_state) SKIP := by
  sorry

/-- 带有循环步数计数的求值关系，用于为循环展开归纳提供良基度量 -/
inductive ceval_count : com → state → state → Nat → Prop where
  | E'Skip : ∀ st,
      ceval_count SKIP st st 0
  | E'Asgn : ∀ st a1 n l,
      aeval st a1 = n →
      ceval_count (l ::= a1) st (l !-> n; st) 0
  | E'Seq : ∀ c1 c2 st st' st'' n1 n2,
      ceval_count c1 st st' n1 →
      ceval_count c2 st' st'' n2 →
      ceval_count (c1 ;; c2) st st'' (n1 + n2)
  | E'IfTrue : ∀ st st' b1 c1 c2 n,
      beval st b1 = true →
      ceval_count c1 st st' n →
      ceval_count (TEST b1 THEN c1 ELSE c2 FI) st st' n
  | E'IfFalse : ∀ st st' b1 c1 c2 n,
      beval st b1 = false →
      ceval_count c2 st st' n →
      ceval_count (TEST b1 THEN c1 ELSE c2 FI) st st' n
  | E'WhileFalse : ∀ b1 st c1,
      beval st b1 = false →
      ceval_count (WHILE b1 DO c1 END) st st 0
  | E'WhileTrue : ∀ st st' st'' b1 c1 n1 n2,
      beval st b1 = true →
      ceval_count c1 st st' n1 →
      ceval_count (WHILE b1 DO c1 END) st' st'' n2 →
      ceval_count (WHILE b1 DO c1 END) st st'' (Nat.succ (n1 + n2))

theorem ceval_count_complete : ∀ c st st',
  (st =[ c ]=> st') → ∃ n, ceval_count c st st' n := by
  sorry

theorem ceval_count_sound : ∀ c st st' n,
  ceval_count c st st' n → (st =[ c ]=> st') := by
  sorry

theorem pe_compare_nil_lookup : ∀ pe_st1 pe_st2,
  pe_compare pe_st1 pe_st2 = ([] : List String) →
  ∀ V, pe_lookup pe_st1 V = pe_lookup pe_st2 V := by
  sorry

theorem pe_compare_nil_update : ∀ pe_st1 pe_st2,
  pe_compare pe_st1 pe_st2 = ([] : List String) →
  ∀ st, pe_update st pe_st1 = pe_update st pe_st2 := by
  sorry

/-- 带有步数计数的循环偏求值语义关系 -/
inductive pe_ceval_count (c' : com) (pe_st' : pe_state) (c'' : com)
                         (st : state) (st'' : state) (n : Nat) : Prop where
  | pe_ceval_count_intro : ∀ st' n',
      (st =[ c' ]=> st') →
      ceval_count c'' (pe_update st' pe_st') st'' n' →
      n' ≤ n →
      pe_ceval_count c' pe_st' c'' st st'' n

theorem pe_ceval_count_le : ∀ c' pe_st' c'' st st'' n n',
  n' ≤ n →
  pe_ceval_count c' pe_st' c'' st st'' n' →
  pe_ceval_count c' pe_st' c'' st st'' n := by
  sorry

theorem pe_com_complete :
  ∀ c pe_st pe_st' c' c'', pe_com c pe_st c' pe_st' c'' →
  ∀ st st'' n,
  ceval_count c (pe_update st pe_st) st'' n →
  pe_ceval_count c' pe_st' c'' st st'' n := by
  sorry

theorem pe_com_sound :
  ∀ c pe_st pe_st' c' c'', pe_com c pe_st c' pe_st' c'' →
  ∀ st st'' n,
  pe_ceval_count c' pe_st' c'' st st'' n →
  (pe_update st pe_st =[ c ]=> st'') := by
  sorry

theorem pe_com_correct :
  ∀ c pe_st pe_st' c', pe_com c pe_st c' pe_st' SKIP →
  ∀ st st'',
  (pe_update st pe_st =[ c ]=> st'') ↔
  (∃ st', (st =[ c' ]=> st') ∧ pe_update st' pe_st' = st'') := by
  sorry

end Loop

/- ################################################################# -/
```

## 6. 流程图程序的偏求值 (Flowchart Programs)

```lean
/- ################################################################# -/

/-- 基本块 (Basic Block)：以连续赋值开始，以条件跳转或无条件跳转结束 -/
inductive block (Label : Type) : Type where
  | Goto : Label → block Label
  | If : bexp → Label → Label → block Label
  | Assign : String → aexp → block Label → block Label

/-- 奇偶检验程序的四状态标签 -/
inductive parity_label : Type where
  | entry : parity_label
  | loop : parity_label
  | body : parity_label
  | done : parity_label
  deriving Repr, DecidableEq

/-- 循环体基本块 -/
def parity_body : block parity_label :=
  block.Assign Y (aexp.AMinus Y 1)
    (block.Assign X (aexp.AMinus 1 X)
      (block.Goto parity_label.loop))

/-- 基本块求值函数 -/
def keval {L : Type} (st : state) (k : block L) : state × L :=
  match k with
  | block.Goto l => (st, l)
  | block.If b l1 l2 => (st, if beval st b then l1 else l2)
  | block.Assign i a k' => keval (i !-> aeval st a; st) k'

theorem keval_example :
  keval empty_st parity_body = ((X !-> 1; Y !-> 0; empty_st), parity_label.loop) := by
  rfl

/-- 流程图程序：从标签到基本块的映射表 -/
def program (L : Type) : Type := L → Option (block L)

/-- 奇偶检验流程图程序 -/
def parity : program parity_label := fun l =>
  match l with
  | parity_label.entry => some (block.Assign X 0 (block.Goto parity_label.loop))
  | parity_label.loop => some (block.If (bexp.BLe 1 Y) parity_label.body parity_label.done)
  | parity_label.body => some parity_body
  | parity_label.done => none

/-- 流程图程序的求值归纳关系 -/
inductive peval {L : Type} (p : program L) : state → L → state → L → Prop where
  | E_None : ∀ st l,
      p l = none →
      peval p st l st l
  | E_Some : ∀ st l k st' l' st'' l'',
      p l = some k →
      keval st k = (st', l') →
      peval p st' l' st'' l'' →
      peval p st l st'' l''

theorem parity_eval : peval parity empty_st parity_label.entry empty_st parity_label.done := by
  sorry

/-- 基本块的偏求值转换：将标签提升为 `(pe_state × L)` 组合标签 -/
def pe_block {L : Type} (pe_st : pe_state) (k : block L) : block (pe_state × L) :=
  match k with
  | block.Goto l => block.Goto (pe_st, l)
  | block.If b l1 l2 =>
    match pe_bexp pe_st b with
    | bexp.BTrue => block.Goto (pe_st, l1)
    | bexp.BFalse => block.Goto (pe_st, l2)
    | b' => block.If b' (pe_st, l1) (pe_st, l2)
  | block.Assign i a k' =>
    match pe_aexp pe_st a with
    | aexp.ANum n => pe_block (pe_add pe_st i n) k'
    | a' => block.Assign i a' (pe_block (pe_remove pe_st i) k')

theorem pe_block_example :
  pe_block ([(X, 0)] : pe_state) parity_body =
    block.Assign Y (aexp.AMinus Y 1) (block.Goto (([(X, 1)] : pe_state), parity_label.loop)) := by
  rfl

/-- 基本块偏求值的正确性定理 -/
theorem pe_block_correct : ∀ (L : Type) st pe_st k st' pe_st' (l' : L),
  keval st (pe_block pe_st k) = (st', (pe_st', l')) →
  keval (pe_update st pe_st) k = (pe_update st' pe_st', l') := by
  sorry

/-- 流程图程序的偏求值特化：全程序标签展开 -/
def pe_program {L : Type} (p : program L) : program (pe_state × L) :=
  fun ⟨pe_st, l⟩ => (p l).map (pe_block pe_st)

/-- 偏求值特化后程序的联合求值关系 -/
inductive pe_peval {L : Type} (p : program L)
  (st : state) (pe_st : pe_state) (l : L) (st'o : state) (l' : L) : Prop where
  | pe_peval_intro : ∀ st' pe_st',
      peval (pe_program p) st (pe_st, l) st' (pe_st', l') →
      pe_update st' pe_st' = st'o →
      pe_peval p st pe_st l st'o l'

/-- 流程图程序偏求值的端到端正确性主定理 -/
theorem pe_program_correct :
  ∀ (L : Type) (p : program L) st pe_st l st'o l',
  peval p (pe_update st pe_st) l st'o l' ↔
  pe_peval p st pe_st l st'o l' := by
  sorry

end PLF.PE
```
