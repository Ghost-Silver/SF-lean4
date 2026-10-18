---
title: "References: 可变状态与内存引用：存储堆模型与定型保持"
---

```lean
import SFLean4.PLF.Maps
import SFLean4.PLF.Smallstep
import SFLean4.PLF.Stlc

open Maps

namespace PLF.References
```

# 引用：类型化可变引用 (References: Typing Mutable References)

在先前的章节中，我们研究的都是**纯函数式**语言：项的求值不产生任何副作用。
而在实际编程中，绝大多数语言都提供了某种形式的**可变状态 (Mutable State)**。
本章形式化研究如何向简单类型 Lambda 演算中引入**一等引用 (First-Class Mutable References)**：
- 内存分配：`ref t`
- 解引用读取：`!t`
- 赋值写入：`t1 := t2`

引入可变状态后，小步操作语义必须演化为对“项与存储堆对偶” `t / st --> t' / st'` 的归约。
相应地，类型系统必须引入**存储定型 (Store Typing)** `ST`，以跟踪分配出的内存单元的位置类型，
并形式化证明带状态情况下的**进益定理 (Progress)** 与**保型性定理 (Preservation)**。

```lean
namespace STLCRef

/- ################################################################# -/
```

## 1. 语法与值 (Syntax and Values)

```lean
/- ################################################################# -/

/--
扩展类型的归纳定义：
- `Ty_Nat`: 自然数
- `Ty_Unit`: 单位类型
- `Ty_Arrow`: 函数箭头类型
- `Ty_Ref`: 引用类型 `Ref T`
-/
inductive ty : Type where
  | Ty_Nat : ty
  | Ty_Unit : ty
  | Ty_Arrow : ty → ty → ty
  | Ty_Ref : ty → ty
  deriving Repr, DecidableEq

open ty

/--
扩展项的归纳定义：
- 算术与分支：`tm_const`, `tm_succ`, `tm_pred`, `tm_mult`, `tm_if0`
- 单位元：`tm_unit`
- 引用原语：分配 `tm_ref`, 解引用 `tm_deref`, 赋值 `tm_assign`
- 运行时内存位置：`tm_loc`
-/
inductive tm : Type where
  | tm_var : String → tm
  | tm_app : tm → tm → tm
  | tm_abs : String → ty → tm → tm
  | tm_const : Nat → tm
  | tm_succ : tm → tm
  | tm_pred : tm → tm
  | tm_mult : tm → tm → tm
  | tm_if0 : tm → tm → tm → tm
  | tm_unit : tm
  | tm_ref : tm → tm
  | tm_deref : tm → tm
  | tm_assign : tm → tm → tm
  | tm_loc : Nat → tm
  deriving Repr, DecidableEq

open tm

/-- 值断言：抽象、自然数常数、单位元和内存位置均为值 -/
inductive value : tm → Prop where
  | v_abs (x : String) (T2 : ty) (t1 : tm) : value (tm_abs x T2 t1)
  | v_nat (n : Nat) : value (tm_const n)
  | v_unit : value tm_unit
  | v_loc (l : Nat) : value (tm_loc l)

/-- 变量代换函数 `[x := s] t` -/
def subst (x : String) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if x = y then s else t
  | tm_abs y T t1 =>
      if x = y then t else tm_abs y T (subst x s t1)
  | tm_app t1 t2 =>
      tm_app (subst x s t1) (subst x s t2)
  | tm_const n =>
      tm_const n
  | tm_succ t1 =>
      tm_succ (subst x s t1)
  | tm_pred t1 =>
      tm_pred (subst x s t1)
  | tm_mult t1 t2 =>
      tm_mult (subst x s t1) (subst x s t2)
  | tm_if0 t1 t2 t3 =>
      tm_if0 (subst x s t1) (subst x s t2) (subst x s t3)
  | tm_unit =>
      tm_unit
  | tm_ref t1 =>
      tm_ref (subst x s t1)
  | tm_deref t1 =>
      tm_deref (subst x s t1)
  | tm_assign t1 t2 =>
      tm_assign (subst x s t1) (subst x s t2)
  | tm_loc l =>
      tm_loc l

def x : String := "x"
def y : String := "y"
def z : String := "z"

/-- 顺序执行衍生语法：`t1 ; t2` 等价于 `(\x:Unit, t2) t1` -/
def tseq (t1 t2 : tm) : tm :=
  tm_app (tm_abs "x" Ty_Unit t2) t1
```

**** 练习: 1 星, standard, optional (store_draw)
思考练习：画出引用与计数器对象的存储单元内存布局。

**** 练习: 2 星, standard, especially useful (compact_update)
思考练习：嵌套引用的紧凑更新与别名分析。

```lean
def manual_grade_for_compact_update : Option (Nat × String) := none
```

**** 练习: 2 星, standard (type_safety_violation)
思考练习：空引用或手动释放内存对类型安全造成的破坏。

```lean
def manual_grade_for_type_safety_violation : Option (Nat × String) := none

/- ################################################################# -/
```

## 2. 存储与操作语义 (Stores and Operational Semantics)

```lean
/- ################################################################# -/

/-- 存储堆模型：以项的列表表示，下标为物理位置 -/
abbrev store : Type := List tm

/-- 存储堆读取 -/
def store_lookup (n : Nat) (st : store) : tm :=
  st.getD n tm_unit

/-- 存储堆位置更新替换函数 -/
def replace {A : Type} (n : Nat) (x : A) (l : List A) : List A :=
  match l with
  | List.nil => List.nil
  | List.cons h t =>
    match n with
    | 0 => List.cons x t
    | n' + 1 => List.cons h (replace n' x t)

theorem replace_nil {A : Type} (n : Nat) (x : A) :
    replace n x (List.nil : List A) = (List.nil : List A) := by
  cases n <;> rfl

theorem length_replace {A : Type} (l : List A) (n : Nat) (x : A) :
    (replace n x l).length = l.length := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons h t ih =>
      cases n with
      | zero => rfl
      | succ n' => simp [replace, ih]

theorem lookup_replace_eq {A : Type} (l : List A) (n : Nat) (x : A) :
    n < l.length → (replace n x l)[n]? = some x := by
  sorry

theorem lookup_replace_neq {A : Type} (l : List A) (n n' : Nat) (x : A) :
    n ≠ n' → (replace n' x l)[n]? = l[n]? := by
  sorry

/-- 带状态的小步操作语义 `(t, st) --> (t', st')` -/
inductive step : (tm × store) → (tm × store) → Prop where
  | ST_AppAbs (x : String) (T2 : ty) (t1 v2 : tm) (st : store) :
      value v2 →
      step (tm_app (tm_abs x T2 t1) v2, st) (subst x v2 t1, st)
  | ST_App1 (t1 t1' t2 : tm) (st st' : store) :
      step (t1, st) (t1', st') →
      step (tm_app t1 t2, st) (tm_app t1' t2, st')
  | ST_App2 (v1 t2 t2' : tm) (st st' : store) :
      value v1 →
      step (t2, st) (t2', st') →
      step (tm_app v1 t2, st) (tm_app v1 t2', st')
  | ST_SuccNat (n : Nat) (st : store) :
      step (tm_succ (tm_const n), st) (tm_const (n + 1), st)
  | ST_Succ (t1 t1' : tm) (st st' : store) :
      step (t1, st) (t1', st') →
      step (tm_succ t1, st) (tm_succ t1', st')
  | ST_PredNat (n : Nat) (st : store) :
      step (tm_pred (tm_const n), st) (tm_const (n - 1), st)
  | ST_Pred (t1 t1' : tm) (st st' : store) :
      step (t1, st) (t1', st') →
      step (tm_pred t1, st) (tm_pred t1', st')
  | ST_MultNats (n1 n2 : Nat) (st : store) :
      step (tm_mult (tm_const n1) (tm_const n2), st) (tm_const (n1 * n2), st)
  | ST_Mult1 (t1 t2 t1' : tm) (st st' : store) :
      step (t1, st) (t1', st') →
      step (tm_mult t1 t2, st) (tm_mult t1' t2, st')
  | ST_Mult2 (v1 t2 t2' : tm) (st st' : store) :
      value v1 →
      step (t2, st) (t2', st') →
      step (tm_mult v1 t2, st) (tm_mult v1 t2', st')
  | ST_If0 (t1 t1' t2 t3 : tm) (st st' : store) :
      step (t1, st) (t1', st') →
      step (tm_if0 t1 t2 t3, st) (tm_if0 t1' t2 t3, st')
  | ST_If0_Zero (t2 t3 : tm) (st : store) :
      step (tm_if0 (tm_const 0) t2 t3, st) (t2, st)
  | ST_If0_Nonzero (n : Nat) (t2 t3 : tm) (st : store) :
      step (tm_if0 (tm_const (n + 1)) t2 t3, st) (t3, st)
  | ST_RefValue (v : tm) (st : store) :
      value v →
      step (tm_ref v, st) (tm_loc st.length, st ++ List.cons v List.nil)
  | ST_Ref (t1 t1' : tm) (st st' : store) :
      step (t1, st) (t1', st') →
      step (tm_ref t1, st) (tm_ref t1', st')
  | ST_DerefLoc (st : store) (l : Nat) :
      l < st.length →
      step (tm_deref (tm_loc l), st) (store_lookup l st, st)
  | ST_Deref (t1 t1' : tm) (st st' : store) :
      step (t1, st) (t1', st') →
      step (tm_deref t1, st) (tm_deref t1', st')
  | ST_Assign (v : tm) (l : Nat) (st : store) :
      value v →
      l < st.length →
      step (tm_assign (tm_loc l) v, st) (tm_unit, replace l v st)
  | ST_Assign1 (t1 t1' t2 : tm) (st st' : store) :
      step (t1, st) (t1', st') →
      step (tm_assign t1 t2, st) (tm_assign t1' t2, st')
  | ST_Assign2 (v1 t2 t2' : tm) (st st' : store) :
      value v1 →
      step (t2, st) (t2', st') →
      step (tm_assign v1 t2, st) (tm_assign v1 t2', st')

def multistep : (tm × store) → (tm × store) → Prop := PLF.Smallstep.multi step
```

**** 练习: 3 星, standard (cyclic_store)
通过引用实现自引用的循环存储堆。

```lean
theorem cyclic_store :
    ∃ t, multistep (t, (List.nil : store))
      (tm_unit, List.cons (tm_abs "x" Ty_Nat (tm_app (tm_deref (tm_loc 1)) (tm_var "x")))
                 (List.cons (tm_abs "x" Ty_Nat (tm_app (tm_deref (tm_loc 0)) (tm_var "x"))) List.nil)) := by
  sorry

/- ################################################################# -/
```

## 3. 存储定型与定型关系 (Store Typings and Typing)

```lean
/- ################################################################# -/

abbrev store_ty : Type := List ty

def store_Tlookup (n : Nat) (ST : store_ty) : ty :=
  ST.getD n Ty_Unit

def context := partial_map ty

/--
存储定型下的定型关系：`has_type ST Gamma t T`
-/
inductive has_type (ST : store_ty) : context → tm → ty → Prop where
  | T_Var (Gamma : context) (x : String) (T1 : ty) :
      Gamma x = some T1 →
      has_type ST Gamma (tm_var x) T1
  | T_Abs (Gamma : context) (x : String) (T1 T2 : ty) (t1 : tm) :
      has_type ST (x |-> T2 ; Gamma) t1 T1 →
      has_type ST Gamma (tm_abs x T2 t1) (Ty_Arrow T2 T1)
  | T_App (T1 T2 : ty) (Gamma : context) (t1 t2 : tm) :
      has_type ST Gamma t1 (Ty_Arrow T2 T1) →
      has_type ST Gamma t2 T2 →
      has_type ST Gamma (tm_app t1 t2) T1
  | T_Nat (Gamma : context) (n : Nat) :
      has_type ST Gamma (tm_const n) Ty_Nat
  | T_Succ (Gamma : context) (t1 : tm) :
      has_type ST Gamma t1 Ty_Nat →
      has_type ST Gamma (tm_succ t1) Ty_Nat
  | T_Pred (Gamma : context) (t1 : tm) :
      has_type ST Gamma t1 Ty_Nat →
      has_type ST Gamma (tm_pred t1) Ty_Nat
  | T_Mult (Gamma : context) (t1 t2 : tm) :
      has_type ST Gamma t1 Ty_Nat →
      has_type ST Gamma t2 Ty_Nat →
      has_type ST Gamma (tm_mult t1 t2) Ty_Nat
  | T_If0 (Gamma : context) (t1 t2 t3 : tm) (T0 : ty) :
      has_type ST Gamma t1 Ty_Nat →
      has_type ST Gamma t2 T0 →
      has_type ST Gamma t3 T0 →
      has_type ST Gamma (tm_if0 t1 t2 t3) T0
  | T_Unit (Gamma : context) :
      has_type ST Gamma tm_unit Ty_Unit
  | T_Loc (Gamma : context) (l : Nat) :
      l < ST.length →
      has_type ST Gamma (tm_loc l) (Ty_Ref (store_Tlookup l ST))
  | T_Ref (Gamma : context) (t1 : tm) (T1 : ty) :
      has_type ST Gamma t1 T1 →
      has_type ST Gamma (tm_ref t1) (Ty_Ref T1)
  | T_Deref (Gamma : context) (t1 : tm) (T1 : ty) :
      has_type ST Gamma t1 (Ty_Ref T1) →
      has_type ST Gamma (tm_deref t1) T1
  | T_Assign (Gamma : context) (t1 t2 : tm) (T2 : ty) :
      has_type ST Gamma t1 (Ty_Ref T2) →
      has_type ST Gamma t2 T2 →
      has_type ST Gamma (tm_assign t1 t2) Ty_Unit

/- ################################################################# -/
```

## 4. 性质验证：良定存储与类型安全 (Properties)

```lean
/- ################################################################# -/

/-- 粗糙的保型性陈述（未考虑存储扩张与良定性，不可证明） -/
def preservation_wrong : Prop :=
  ∀ ST T t st t' st',
    has_type ST empty t T →
    step (t, st) (t', st') →
    has_type ST empty t' T

/-- 存储堆与存储定型的一致良定性关系 -/
def store_well_typed (ST : store_ty) (st : store) : Prop :=
  ST.length = st.length ∧
  (∀ l, l < st.length → has_type ST empty (store_lookup l st) (store_Tlookup l ST))

/--
**** 练习: 3 星, standard (store_not_unique)
同一存储堆可能对应多个不同存储定型的反例。
-/
theorem store_not_unique :
    ∃ st ST1 ST2,
      store_well_typed ST1 st ∧
      store_well_typed ST2 st ∧
      ST1 ≠ ST2 := by
  sorry

/-- 未考虑存储定型延伸的较粗糙保型性断言 -/
def preservation_lesswrong : Prop :=
  ∀ ST T t st t' st',
    has_type ST empty t T →
    step (t, st) (t', st') →
    store_well_typed ST st →
    has_type ST empty t' T

/-- 存储定型的延伸关系：仅在末尾追加新的位置类型 -/
inductive «extends» : store_ty → store_ty → Prop where
  | extends_nil (ST' : store_ty) : «extends» ST' (List.nil : store_ty)
  | extends_cons (x : ty) (ST' ST : store_ty) :
      «extends» ST' ST → «extends» (List.cons x ST') (List.cons x ST)

theorem extends_lookup (l : Nat) (ST ST' : store_ty) :
    l < ST.length →
    «extends» ST' ST →
    store_Tlookup l ST' = store_Tlookup l ST := by
  sorry

theorem length_extends (ST ST' : store_ty) :
    «extends» ST' ST → ST.length ≤ ST'.length := by
  sorry

theorem extends_app (ST T : store_ty) :
    «extends» (ST ++ T) ST := by
  sorry

theorem extends_refl (ST : store_ty) :
    «extends» ST ST := by
  sorry

/-- 严谨的保型性定理命题形式 -/
def preservation_theorem : Prop :=
  ∀ ST t t' T st st',
    has_type ST empty t T →
    store_well_typed ST st →
    step (t, st) (t', st') →
    ∃ ST', «extends» ST' ST ∧ has_type ST' empty t' T ∧ store_well_typed ST' st'

theorem weakening (Gamma Gamma' : context) (ST : store_ty) (t : tm) (T : ty) :
    includedin Gamma Gamma' →
    has_type ST Gamma t T →
    has_type ST Gamma' t T := by
  sorry

theorem weakening_empty (Gamma : context) (ST : store_ty) (t : tm) (T : ty) :
    has_type ST empty t T →
    has_type ST Gamma t T := by
  sorry

theorem substitution_preserves_typing (Gamma : context) (ST : store_ty) (x : String) (U : ty) (t v : tm) (T : ty) :
    has_type ST (x |-> U ; Gamma) t T →
    has_type ST empty v U →
    has_type ST Gamma (subst x v t) T := by
  sorry

theorem assign_pres_store_typing (ST : store_ty) (st : store) (l : Nat) (t : tm) (T : ty) :
    store_well_typed ST st →
    has_type ST empty t T →
    store_Tlookup l ST = T →
    store_well_typed ST (replace l t st) := by
  sorry

theorem store_weakening (Gamma : context) (ST ST' : store_ty) (t : tm) (T : ty) :
    «extends» ST' ST →
    has_type ST Gamma t T →
    has_type ST' Gamma t T := by
  sorry

theorem store_well_typed_app (ST : store_ty) (st : store) (t1 : tm) (T1 : ty) :
    store_well_typed ST st →
    has_type ST empty t1 T1 →
    store_well_typed (ST ++ List.cons T1 List.nil) (st ++ List.cons t1 List.nil) := by
  sorry

theorem nth_eq_last {A : Type} (l : List A) (x : A) :
    (l ++ List.cons x List.nil)[l.length]? = some x := by
  sorry

/-- 保型性定理 (Preservation Theorem) -/
theorem preservation (t t' : tm) (st st' : store) (T : ty) (ST : store_ty) :
    has_type ST empty t T →
    store_well_typed ST st →
    step (t, st) (t', st') →
    ∃ ST', «extends» ST' ST ∧ has_type ST' empty t' T ∧ store_well_typed ST' st' := by
  sorry

/--
**** 练习: 3 星, standard, optional (preservation_informal)
保型性定理的非形式化证明论证。
-/
def manual_grade_for_preservation_informal : Option (Nat × String) := none

/-- 进益定理 (Progress Theorem) -/
theorem progress (ST : store_ty) (t : tm) (st : store) (T : ty) :
    has_type ST empty t T →
    store_well_typed ST st →
    value t ∨ ∃ t' st', step (t, st) (t', st') := by
  sorry

/- ################################################################# -/
```

## 5. 引用与图灵完备停机问题 (References and Nontermination)

```lean
/- ################################################################# -/

namespace RefsAndNontermination

def x : String := "x"
def y : String := "y"
def r : String := "r"
def s : String := "s"

/-- 自引用循环递归函数 -/
def loop_fun : tm :=
  tm_abs "x" Ty_Unit (tm_app (tm_deref (tm_var r)) tm_unit)

/-- 无需定点组合子、仅靠引用制造的发散项 -/
def loop : tm :=
  tm_app
    (tm_abs r (Ty_Ref (Ty_Arrow Ty_Unit Ty_Unit))
      (tseq (tm_assign (tm_var r) loop_fun) (tm_app (tm_deref (tm_var r)) tm_unit)))
    (tm_ref (tm_abs "x" Ty_Unit tm_unit))

theorem loop_typeable :
    ∃ T, has_type (List.nil : store_ty) empty loop T := by
  sorry

/-- 单步或多步严格可及闭包 -/
inductive step_closure {X : Type} (R : X → X → Prop) : X → X → Prop where
  | sc_one (x y : X) : R x y → step_closure R x y
  | sc_step (x y z : X) : R x y → step_closure R y z → step_closure R x z

def multistep1 : (tm × store) → (tm × store) → Prop := step_closure step

theorem loop_steps_to_loop_fun :
    multistep (loop, (List.nil : store))
      (tm_app (tm_deref (tm_loc 0)) tm_unit, List.cons (subst r (tm_loc 0) loop_fun) List.nil) := by
  sorry

theorem loop_fun_step_self :
    multistep1 (tm_app (tm_deref (tm_loc 0)) tm_unit, List.cons (subst r (tm_loc 0) loop_fun) List.nil)
      (tm_app (tm_deref (tm_loc 0)) tm_unit, List.cons (subst r (tm_loc 0) loop_fun) List.nil) := by
  sorry

/--
**** 练习: 4 stars, standard (factorial_ref)
使用引用实现阶乘计算函数。
-/
def factorial : tm :=
  tm_unit

theorem factorial_type :
    has_type (List.nil : store_ty) empty factorial (Ty_Arrow Ty_Nat Ty_Nat) := by
  sorry

theorem factorial_4 :
    ∃ st, multistep (tm_app factorial (tm_const 4), (List.nil : store)) (tm_const 24, st) := by
  sorry
```

**** 练习: 5 星, standard, optional (garbage_collector)
挑战练习：形式化垃圾回收（Garbage Collection）与不可达内存单元安全回收性质。

```lean
end RefsAndNontermination

end STLCRef

end PLF.References
```
