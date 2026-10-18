import SFLean4.PLF.Maps
import SFLean4.PLF.Types
import SFLean4.PLF.Smallstep
import SFLean4.PLF.Stlc

/-!
# 软件基础 第二卷：程序语言基础 (PLF)

## 模块：子类型化 (Sub: Subtyping)

在本章中，我们转向面向对象程序设计与高级类型系统中的关键机制：**子类型化（Subtyping）**。

### 核心思想与安全代换原则
- **安全代换原则（Liskov Substitution Principle）**：
  若类型 $S$ 是类型 $T$ 的子类型（记作 $S <: T$），则在任何期望类型 $T$ 的表达式的上下文中，
  都可以安全地传入类型 $S$ 的值，而程序绝不会陷入未定义的“卡住（Stuck）”状态。
- **包容规则（Rule of Subsumption）**：
  $$\frac{\Gamma \vdash t : S \quad S <: T}{\Gamma \vdash t : T} \quad (T\_Sub)$$
  包容规则允许类型系统在需要时“遗忘”项的部分特化信息（例如，将具有更多字段的派生记录当做基础记录使用）。

### 箭头子类型化的逆变性 (Contravariance of Arrows)
箭头类型的子类型规则是类型论中最迷人、最经典的概念之一：
$$\frac{T_1 <: S_1 \quad S_2 <: T_2}{S_1 \to S_2 <: T_1 \to T_2} \quad (S\_Arrow)$$
- **参数位置是逆变（Contravariant）的**：函数接受的参数范围必须更加宽松（$T_1 <: S_1$）；
- **返回值位置是协变（Covariant）的**：函数产生的返回值必须更加精细（$S_2 <: T_2$）。
-/

namespace PLF.Sub

open Maps
open PLF.Smallstep

/-!
## 概念思考题评分标记 (Conceptual Exercises)
-/

/--
**** 练习: 2 星, standard, especially useful (arrow_sub_wrong)
逆变性思考：为什么箭头类型参数位置必须是逆变的？若改为协变会引发何种运行时错误？
-/
def manual_grade_for_arrow_sub_wrong : Option (Nat × String) := none

/-!
**** 练习: 1 星, standard, optional (subtype_instances_tf_1)
子类型实例真假判断 1。
-/

/--
**** 练习: 2 星, standard (subtype_order)
偏序关系思考：子类型关系是预序（前序关系）还是偏序关系？
-/
def manual_grade_for_subtype_order : Option (Nat × String) := none

/--
**** 练习: 1 星, standard (subtype_instances_tf_2)
子类型实例真假判断 2。
-/
def manual_grade_for_subtype_instances_tf_2 : Option (Nat × String) := none

/--
**** 练习: 1 星, standard (subtype_concepts_tf)
子类型概念真假判断。
-/
def manual_grade_for_subtype_concepts_tf : Option (Nat × String) := none

/--
**** 练习: 2 星, standard (proper_subtypes)
严格子类型（Proper Subtypes）探讨。
-/
def manual_grade_for_proper_subtypes : Option (Nat × String) := none

/--
**** 练习: 2 星, standard (small_large_1)
极小与极大类型问题 1。
-/
def manual_grade_for_small_large_1 : Option (Nat × String) := none

/--
**** 练习: 2 星, standard (small_large_2)
极小与极大类型问题 2。
-/
def manual_grade_for_small_large_2 : Option (Nat × String) := none

/-!
**** 练习: 2 星, standard, optional (small_large_3)
极小与极大类型问题 3。
-/

/--
**** 练习: 2 星, standard (small_large_4)
极小与极大类型问题 4。
-/
def manual_grade_for_small_large_4 : Option (Nat × String) := none

/--
**** 练习: 2 星, standard (smallest_1)
最小公共超类型问题 1。
-/
def manual_grade_for_smallest_1 : Option (Nat × String) := none

/--
**** 练习: 2 星, standard (smallest_2)
最小公共超类型问题 2。
-/
def manual_grade_for_smallest_2 : Option (Nat × String) := none

/-!
**** 练习: 3 星, standard, optional (count_supertypes)
计算超类型数量。
-/

/--
**** 练习: 2 星, standard (pair_permutation)
积类型与置换子类型化。
-/
def manual_grade_for_pair_permutation : Option (Nat × String) := none

/-!
## 形式化系统 (Formal Definitions)
-/

namespace STLCSub

/-- 子类型化系统的类型定义：
- `Ty_Top`: 顶类型 $\top$（所有类型的超类型）
- `Ty_Bool`: 布尔类型
- `Ty_Base`: 抽象基础类型（用于模拟类名如 Person, Student 等）
- `Ty_Arrow`: 函数类型
- `Ty_Unit`: 单位类型
- `Ty_Prod`: 积类型
-/
inductive ty : Type where
  | Ty_Top : ty
  | Ty_Bool : ty
  | Ty_Base : String → ty
  | Ty_Arrow : ty → ty → ty
  | Ty_Unit : ty
  | Ty_Prod : ty → ty → ty
  deriving Repr, DecidableEq

open ty

/-- 语言项定义 -/
inductive tm : Type where
  | tm_var : String → tm
  | tm_app : tm → tm → tm
  | tm_abs : String → ty → tm → tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm → tm → tm → tm
  | tm_unit : tm
  | tm_pair : tm → tm → tm
  | tm_fst : tm → tm
  | tm_snd : tm → tm
  deriving Repr, DecidableEq

open tm

/-- 代换操作 -/
def subst (x : String) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if x = y then s else tm_var y
  | tm_abs y T t1 =>
      if x = y then tm_abs y T t1 else tm_abs y T (subst x s t1)
  | tm_app t1 t2 =>
      tm_app (subst x s t1) (subst x s t2)
  | tm_true =>
      tm_true
  | tm_false =>
      tm_false
  | tm_if t1 t2 t3 =>
      tm_if (subst x s t1) (subst x s t2) (subst x s t3)
  | tm_unit =>
      tm_unit
  | tm_pair t1 t2 =>
      tm_pair (subst x s t1) (subst x s t2)
  | tm_fst t0 =>
      tm_fst (subst x s t0)
  | tm_snd t0 =>
      tm_snd (subst x s t0)

/-- 值谓词 -/
inductive value : tm → Prop where
  | v_abs (x : String) (T2 : ty) (t1 : tm) : value (tm_abs x T2 t1)
  | v_true : value tm_true
  | v_false : value tm_false
  | v_unit : value tm_unit
  | v_pair (v1 v2 : tm) : value v1 → value v2 → value (tm_pair v1 v2)

/-- 小步单步归约关系 -/
inductive step : tm → tm → Prop where
  | ST_AppAbs (x : String) (T2 : ty) (t1 : tm) (v2 : tm) :
      value v2 → step (tm_app (tm_abs x T2 t1) v2) (subst x v2 t1)
  | ST_App1 (t1 t1' t2 : tm) :
      step t1 t1' → step (tm_app t1 t2) (tm_app t1' t2)
  | ST_App2 (v1 t2 t2' : tm) :
      value v1 → step t2 t2' → step (tm_app v1 t2) (tm_app v1 t2')
  | ST_IfTrue (t1 t2 : tm) :
      step (tm_if tm_true t1 t2) t1
  | ST_IfFalse (t1 t2 : tm) :
      step (tm_if tm_false t1 t2) t2
  | ST_If (t1 t1' t2 t3 : tm) :
      step t1 t1' → step (tm_if t1 t2 t3) (tm_if t1' t2 t3)
  | ST_Pair1 (t1 t1' t2 : tm) :
      step t1 t1' → step (tm_pair t1 t2) (tm_pair t1' t2)
  | ST_Pair2 (v1 t2 t2' : tm) :
      value v1 → step t2 t2' → step (tm_pair v1 t2) (tm_pair v1 t2')
  | ST_Fst1 (t1 t1' : tm) :
      step t1 t1' → step (tm_fst t1) (tm_fst t1')
  | ST_FstPair (v1 v2 : tm) :
      value v1 → value v2 → step (tm_fst (tm_pair v1 v2)) v1
  | ST_Snd1 (t1 t1' : tm) :
      step t1 t1' → step (tm_snd t1) (tm_snd t1')
  | ST_SndPair (v1 v2 : tm) :
      value v1 → value v2 → step (tm_snd (tm_pair v1 v2)) v2

scoped notation:40 t " --> " t' => step t t'
def multistep : tm → tm → Prop := PLF.Smallstep.multi step
scoped notation:40 t1 " -->* " t2 => multistep t1 t2

/-!
### 子类型关系 (Subtyping Relation)
-/

inductive subtype : ty → ty → Prop where
  | S_Refl (T : ty) :
      subtype T T
  | S_Trans (S U T : ty) :
      subtype S U → subtype U T → subtype S T
  | S_Top (S : ty) :
      subtype S Ty_Top
  | S_Arrow (S1 S2 T1 T2 : ty) :
      subtype T1 S1 → subtype S2 T2 → subtype (Ty_Arrow S1 S2) (Ty_Arrow T1 T2)
  | S_Prod (S1 S2 T1 T2 : ty) :
      subtype S1 T1 → subtype S2 T2 → subtype (Ty_Prod S1 S2) (Ty_Prod T1 T2)

scoped notation:40 T " <: " U => subtype T U

namespace Examples

def x : String := "x"
def y : String := "y"
def z : String := "z"

def A : ty := Ty_Base "A"
def B : ty := Ty_Base "B"
def C : ty := Ty_Base "C"

def String_ty : ty := Ty_Base "String"
def Float : ty := Ty_Base "Float"
def Integer : ty := Ty_Base "Integer"

theorem subtyping_example_0 :
  subtype (Ty_Arrow C Ty_Bool) (Ty_Arrow C Ty_Top) := by
  apply subtype.S_Arrow
  · exact subtype.S_Refl C
  · exact subtype.S_Top Ty_Bool

/-!
**** 练习: 2 星, standard, optional (subtyping_judgements)
-/
def Person : ty := Ty_Prod String_ty Ty_Top
def Student : ty := Ty_Prod String_ty Float
def Employee : ty := Ty_Prod String_ty Integer

theorem sub_student_person : subtype Student Person := by
  sorry

theorem sub_employee_person : subtype Employee Person := by
  sorry

/--
**** 练习: 1 星, standard, optional (subtyping_example_1)
-/
theorem subtyping_example_1 :
  subtype (Ty_Arrow Ty_Top Student) (Ty_Arrow (Ty_Arrow C C) Person) := by
  sorry

/--
**** 练习: 1 星, standard, optional (subtyping_example_2)
-/
theorem subtyping_example_2 :
  subtype (Ty_Arrow Ty_Top Person) (Ty_Arrow Person Ty_Top) := by
  sorry

end Examples

export Examples (Person Student Employee sub_student_person sub_employee_person subtyping_example_0 subtyping_example_1 subtyping_example_2)

/-!
### 定型关系与包容规则 (Typing & Subsumption)
-/

def context : Type := partial_map ty

inductive has_type : context → tm → ty → Prop where
  | T_Var (Gamma : context) (x : String) (T1 : ty) :
      Gamma x = some T1 → has_type Gamma (tm_var x) T1
  | T_Abs (Gamma : context) (x : String) (T1 T2 : ty) (t1 : tm) :
      has_type (x |-> T2 ; Gamma) t1 T1 → has_type Gamma (tm_abs x T2 t1) (Ty_Arrow T2 T1)
  | T_App (T1 T2 : ty) (Gamma : context) (t1 t2 : tm) :
      has_type Gamma t1 (Ty_Arrow T2 T1) → has_type Gamma t2 T2 → has_type Gamma (tm_app t1 t2) T1
  | T_True (Gamma : context) :
      has_type Gamma tm_true Ty_Bool
  | T_False (Gamma : context) :
      has_type Gamma tm_false Ty_Bool
  | T_If (t1 t2 t3 : tm) (T1 : ty) (Gamma : context) :
      has_type Gamma t1 Ty_Bool → has_type Gamma t2 T1 → has_type Gamma t3 T1 → has_type Gamma (tm_if t1 t2 t3) T1
  | T_Unit (Gamma : context) :
      has_type Gamma tm_unit Ty_Unit
  | T_Sub (Gamma : context) (t1 : tm) (T1 T2 : ty) :
      has_type Gamma t1 T1 → subtype T1 T2 → has_type Gamma t1 T2
  | T_Pair (Gamma : context) (t1 t2 : tm) (T1 T2 : ty) :
      has_type Gamma t1 T1 → has_type Gamma t2 T2 → has_type Gamma (tm_pair t1 t2) (Ty_Prod T1 T2)
  | T_Fst (Gamma : context) (t : tm) (T1 T2 : ty) :
      has_type Gamma t (Ty_Prod T1 T2) → has_type Gamma (tm_fst t) T1
  | T_Snd (Gamma : context) (t : tm) (T1 T2 : ty) :
      has_type Gamma t (Ty_Prod T1 T2) → has_type Gamma (tm_snd t) T2

/-!
**** 练习: 1 星, standard, optional (typing_example_0)
**** 练习: 2 星, standard, optional (typing_example_1)
**** 练习: 2 星, standard, optional (typing_example_2)
-/

/-!
### 子类型反转引理 (Subtyping Inversion Lemmas)
-/

/--
**** 练习: 2 星, standard, optional (sub_inversion_Bool)
-/
theorem sub_inversion_Bool (U : ty) :
  subtype U Ty_Bool →
  U = Ty_Bool := by
  sorry

/--
**** 练习: 3 星, standard (sub_inversion_arrow)
箭头类型的子类型反转引理。
-/
theorem sub_inversion_arrow (U V1 V2 : ty) :
  subtype U (Ty_Arrow V1 V2) →
  ∃ U1 U2, U = Ty_Arrow U1 U2 ∧ subtype V1 U1 ∧ subtype U2 V2 := by
  sorry

/--
**** 练习: 2 星, standard, optional (sub_inversion_Unit)
-/
theorem sub_inversion_Unit (U : ty) :
  subtype U Ty_Unit →
  U = Ty_Unit := by
  sorry

/--
**** 练习: 2 星, standard, optional (sub_inversion_Base)
-/
theorem sub_inversion_Base (U : ty) (s : String) :
  subtype U (Ty_Base s) →
  U = Ty_Base s := by
  sorry

/--
**** 练习: 2 星, standard, optional (sub_inversion_Top)
-/
theorem sub_inversion_Top (U : ty) :
  subtype Ty_Top U →
  U = Ty_Top := by
  sorry

/--
**** 练习: 3 星, standard, optional (canonical_forms_of_arrow_types)
-/
theorem canonical_forms_of_arrow_types (Gamma : context) (s : tm) (T1 T2 : ty) :
  has_type Gamma s (Ty_Arrow T1 T2) →
  value s →
  ∃ x S1 s2, s = tm_abs x S1 s2 := by
  sorry

theorem canonical_forms_of_Bool (Gamma : context) (s : tm) :
  has_type Gamma s Ty_Bool →
  value s →
  s = tm_true ∨ s = tm_false := by
  sorry

/-- 进益定理 -/
theorem progress (t : tm) (T : ty) :
  has_type empty t T →
  value t ∨ ∃ t', step t t' := by
  sorry

/-!
### 定型反转引理 (Typing Inversion Lemmas)
-/

theorem typing_inversion_abs (Gamma : context) (x : String) (S1 : ty) (t2 : tm) (T : ty) :
  has_type Gamma (tm_abs x S1 t2) T →
  ∃ S2, subtype (Ty_Arrow S1 S2) T ∧ has_type (x |-> S1 ; Gamma) t2 S2 := by
  sorry

/--
**** 练习: 3 星, standard, optional (typing_inversion_var)
-/
theorem typing_inversion_var (Gamma : context) (x : String) (T : ty) :
  has_type Gamma (tm_var x) T →
  ∃ S, Gamma x = some S ∧ subtype S T := by
  sorry

/--
**** 练习: 3 星, standard, optional (typing_inversion_app)
-/
theorem typing_inversion_app (Gamma : context) (t1 t2 : tm) (T2 : ty) :
  has_type Gamma (tm_app t1 t2) T2 →
  ∃ T1, has_type Gamma t1 (Ty_Arrow T1 T2) ∧ has_type Gamma t2 T1 := by
  sorry

theorem typing_inversion_unit (Gamma : context) (T : ty) :
  has_type Gamma tm_unit T →
  subtype Ty_Unit T := by
  sorry

theorem abs_arrow (x : String) (S1 : ty) (s2 : tm) (T1 T2 : ty) :
  has_type empty (tm_abs x S1 s2) (Ty_Arrow T1 T2) →
  subtype T1 S1 ∧ has_type (x |-> S1 ; empty) s2 T2 := by
  sorry

theorem weakening (Gamma Gamma' : context) (t : tm) (T : ty) :
  includedin Gamma Gamma' →
  has_type Gamma t T →
  has_type Gamma' t T := by
  sorry

theorem weakening_empty (Gamma : context) (t : tm) (T : ty) :
  has_type empty t T →
  has_type Gamma t T := by
  intro H
  apply weakening empty Gamma t T _ H
  intro x v Hx
  cases Hx

theorem substitution_preserves_typing (Gamma : context) (x : String) (U : ty) (t v : tm) (T : ty) :
  has_type (x |-> U ; Gamma) t T →
  has_type empty v U →
  has_type Gamma (subst x v t) T := by
  sorry

theorem preservation (t t' : tm) (T : ty) :
  has_type empty t T →
  step t t' →
  has_type empty t' T := by
  sorry

/--
**** 练习: 2 星, standard (variations)
-/
def manual_grade_for_variations : Option (Nat × String) := none

/--
**** 练习: 5 星, standard (products)
积类型扩展系列评分标记。
-/
def manual_grade_for_products_value_step : Option (Nat × String) := none
def manual_grade_for_products_subtype_has_type : Option (Nat × String) := none
def manual_grade_for_products_progress : Option (Nat × String) := none
def manual_grade_for_products_preservation : Option (Nat × String) := none

/-!
### 思考题的形式化命题 (Formalized Thought Exercises)
-/

namespace FormalThoughtExercises

def TF (P : Prop) : Prop := P ∨ ¬ P

/--
**** 练习: 1 星, standard, optional (formal_subtype_instances_tf_1a)
-/
theorem formal_subtype_instances_tf_1a :
  TF (∀ S T U V, subtype S T → subtype U V → subtype (Ty_Arrow T S) (Ty_Arrow T S)) := by
  sorry

/--
**** 练习: 1 星, standard, optional (formal_subtype_instances_tf_1b)
-/
theorem formal_subtype_instances_tf_1b :
  TF (∀ S T U V, subtype S T → subtype U V → subtype (Ty_Arrow Ty_Top U) (Ty_Arrow S Ty_Top)) := by
  sorry

/--
**** 练习: 1 星, standard, optional (formal_subtype_instances_tf_1c)
-/
theorem formal_subtype_instances_tf_1c :
  TF (∀ S T U V, subtype S T → subtype U V →
    subtype (Ty_Arrow (Ty_Arrow Examples.C Examples.C) (Ty_Prod Examples.A Examples.B))
            (Ty_Arrow (Ty_Arrow Examples.C Examples.C) (Ty_Prod Ty_Top Examples.B))) := by
  sorry

/--
**** 练习: 1 星, standard, optional (formal_subtype_instances_tf_1d)
-/
theorem formal_subtype_instances_tf_1d :
  TF (∀ S T U V, subtype S T → subtype U V →
    subtype (Ty_Arrow T (Ty_Arrow T U)) (Ty_Arrow S (Ty_Arrow S V))) := by
  sorry

/--
**** 练习: 1 星, standard, optional (formal_subtype_instances_tf_1e)
-/
theorem formal_subtype_instances_tf_1e :
  TF (∀ S T U V, subtype S T → subtype U V →
    subtype (Ty_Arrow (Ty_Arrow T T) U) (Ty_Arrow (Ty_Arrow S S) V)) := by
  sorry

/--
**** 练习: 1 星, standard, optional (formal_subtype_instances_tf_1f)
-/
theorem formal_subtype_instances_tf_1f :
  TF (∀ S T U V, subtype S T → subtype U V →
    subtype (Ty_Arrow (Ty_Arrow (Ty_Arrow T S) T) U)
            (Ty_Arrow (Ty_Arrow (Ty_Arrow S T) S) V)) := by
  sorry

/--
**** 练习: 1 星, standard, optional (formal_subtype_instances_tf_1g)
-/
theorem formal_subtype_instances_tf_1g :
  TF (∀ S T U V, subtype S T → subtype U V →
    subtype (Ty_Prod S V) (Ty_Prod T U)) := by
  sorry

/--
**** 练习: 2 星, standard, optional (formal_subtype_instances_tf_2a)
-/
theorem formal_subtype_instances_tf_2a :
  TF (∀ S T, subtype S T → subtype (Ty_Arrow S S) (Ty_Arrow T T)) := by
  sorry

/--
**** 练习: 2 星, standard, optional (formal_subtype_instances_tf_2b)
-/
theorem formal_subtype_instances_tf_2b :
  TF (∀ S, subtype S (Ty_Arrow Examples.A Examples.A) → ∃ T, S = Ty_Arrow T T ∧ subtype T Examples.A) := by
  sorry

/--
**** 练习: 2 星, standard, optional (formal_subtype_instances_tf_2d)
-/
theorem formal_subtype_instances_tf_2d :
  TF (∃ S, subtype S (Ty_Arrow S S)) := by
  sorry

/--
**** 练习: 2 星, standard, optional (formal_subtype_instances_tf_2e)
-/
theorem formal_subtype_instances_tf_2e :
  TF (∃ S, subtype (Ty_Arrow S S) S) := by
  sorry

/--
**** 练习: 2 星, standard, optional (formal_subtype_concepts_tfa)
-/
theorem formal_subtype_concepts_tfa :
  TF (∃ T, ∀ S, subtype S T) := by
  sorry

/--
**** 练习: 2 星, standard, optional (formal_subtype_concepts_tfb)
-/
theorem formal_subtype_concepts_tfb :
  TF (∃ T, ∀ S, subtype T S) := by
  sorry

/--
**** 练习: 2 星, standard, optional (formal_subtype_concepts_tfc)
-/
theorem formal_subtype_concepts_tfc :
  TF (∃ T1 T2, ∀ S1 S2, subtype (Ty_Prod S1 S2) (Ty_Prod T1 T2)) := by
  sorry

/--
**** 练习: 2 星, standard, optional (formal_subtype_concepts_tfd)
-/
theorem formal_subtype_concepts_tfd :
  TF (∃ T1 T2, ∀ S1 S2, subtype (Ty_Prod T1 T2) (Ty_Prod S1 S2)) := by
  sorry

/--
**** 练习: 2 星, standard, optional (formal_subtype_concepts_tfe)
-/
theorem formal_subtype_concepts_tfe :
  TF (∃ T1 T2, ∀ S1 S2, subtype (Ty_Arrow S1 S2) (Ty_Arrow T1 T2)) := by
  sorry

/--
**** 练习: 2 星, standard, optional (formal_subtype_concepts_tff)
-/
theorem formal_subtype_concepts_tff :
  TF (∃ T1 T2, ∀ S1 S2, subtype (Ty_Arrow T1 T2) (Ty_Arrow S1 S2)) := by
  sorry

/--
**** 练习: 2 星, standard, optional (formal_subtype_concepts_tfg)
-/
theorem formal_subtype_concepts_tfg :
  TF (∃ f : Nat → ty, (∀ i j, i ≠ j → f i ≠ f j) ∧ (∀ i, subtype (f (i + 1)) (f i))) := by
  sorry

/--
**** 练习: 2 星, standard, optional (formal_subtype_concepts_tfh)
-/
theorem formal_subtype_concepts_tfh :
  TF (∃ f : Nat → ty, (∀ i j, i ≠ j → f i ≠ f j) ∧ (∀ i, subtype (f i) (f (i + 1)))) := by
  sorry

/--
**** 练习: 3 星, standard, optional (formal_proper_subtypes)
-/
theorem formal_proper_subtypes :
  TF (∀ T, ¬(T = Ty_Bool ∨ (∃ n, T = Ty_Base n) ∨ T = Ty_Unit) → ∃ S, subtype S T ∧ S ≠ T) := by
  sorry

end FormalThoughtExercises

export FormalThoughtExercises (
  TF formal_subtype_instances_tf_1a formal_subtype_instances_tf_1b formal_subtype_instances_tf_1c
  formal_subtype_instances_tf_1d formal_subtype_instances_tf_1e formal_subtype_instances_tf_1f
  formal_subtype_instances_tf_1g formal_subtype_instances_tf_2a formal_subtype_instances_tf_2b
  formal_subtype_instances_tf_2d formal_subtype_instances_tf_2e formal_subtype_concepts_tfa
  formal_subtype_concepts_tfb formal_subtype_concepts_tfc formal_subtype_concepts_tfd
  formal_subtype_concepts_tfe formal_subtype_concepts_tff formal_subtype_concepts_tfg
  formal_subtype_concepts_tfh formal_proper_subtypes
)

end STLCSub

end PLF.Sub
