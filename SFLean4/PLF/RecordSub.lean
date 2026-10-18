import SFLean4.PLF.Maps
import SFLean4.PLF.Smallstep
import SFLean4.PLF.Sub

open Maps

namespace PLF.RecordSub

/-!
# 记录子类型化 (RecordSub: Subtyping with Records)

在本章中，我们将简单类型 Lambda 演算的两项重要扩展结合起来：
- **记录 (Records)**：提供字段组织与投影访问机制；
- **子类型化 (Subtyping)**：引入类型包含关系 `<:` 与包容规则 `T_Sub`。

当记录与子类型相遇时，子类型的深度（字段协变）、宽度（允许更多字段）以及字段置换（字段顺序无关性）
规则赋予了记录类型强大的面向对象多态表达能力。
-/

namespace RecordSub

/- ################################################################# -/
/-! ## 1. 核心定义 (Core Definitions) -/
/- ################################################################# -/

/--
结合记录与子类型顶层类型的类型集合：
- `Ty_Top`: 最大顶层类型 Top
- `Ty_Base`: 基础类型
- `Ty_Arrow`: 函数箭头类型
- `Ty_RNil`: 空记录类型
- `Ty_RCons`: 头部字段类型追加
-/
inductive ty : Type where
  | Ty_Top : ty
  | Ty_Base : String → ty
  | Ty_Arrow : ty → ty → ty
  | Ty_RNil : ty
  | Ty_RCons : String → ty → ty → ty
  deriving Repr, DecidableEq

open ty

/--
记录项的语法集合：
- 基础项：变量、函数应用、抽象
- 记录专用项：字段投影 `tm_rproj`、空记录 `tm_rnil`、字段追加 `tm_rcons`
-/
inductive tm : Type where
  | tm_var : String → tm
  | tm_app : tm → tm → tm
  | tm_abs : String → ty → tm → tm
  | tm_rproj : tm → String → tm
  | tm_rnil : tm
  | tm_rcons : String → tm → tm → tm
  deriving Repr, DecidableEq

open tm

/-- 判定类型是否为记录形式 -/
inductive record_ty : ty → Prop where
  | RTnil : record_ty Ty_RNil
  | RTcons (i : String) (T1 T2 : ty) : record_ty (Ty_RCons i T1 T2)

/-- 判定项是否为记录形式 -/
inductive record_tm : tm → Prop where
  | rtnil : record_tm tm_rnil
  | rtcons (i : String) (t1 t2 : tm) : record_tm (tm_rcons i t1 t2)

/--
良构类型断言：
排除记录尾部为非记录类型的怪异情况，保证结构归纳法成立。
-/
inductive well_formed_ty : ty → Prop where
  | wfTop : well_formed_ty Ty_Top
  | wfBase (i : String) : well_formed_ty (Ty_Base i)
  | wfArrow (T1 T2 : ty) :
      well_formed_ty T1 →
      well_formed_ty T2 →
      well_formed_ty (Ty_Arrow T1 T2)
  | wfRNil : well_formed_ty Ty_RNil
  | wfRCons (i : String) (T1 T2 : ty) :
      well_formed_ty T1 →
      well_formed_ty T2 →
      record_ty T2 →
      well_formed_ty (Ty_RCons i T1 T2)

/-- 变量代换函数 `[x := s] t` -/
def subst (x : String) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if x = y then s else t
  | tm_abs y T t1 =>
      if x = y then t else tm_abs y T (subst x s t1)
  | tm_app t1 t2 =>
      tm_app (subst x s t1) (subst x s t2)
  | tm_rproj t1 i =>
      tm_rproj (subst x s t1) i
  | tm_rnil =>
      tm_rnil
  | tm_rcons i t1 tr =>
      tm_rcons i (subst x s t1) (subst x s tr)

/-- 值断言 -/
inductive value : tm → Prop where
  | v_abs (x : String) (T2 : ty) (t1 : tm) : value (tm_abs x T2 t1)
  | v_rnil : value tm_rnil
  | v_rcons (i : String) (v1 vr : tm) :
      value v1 →
      value vr →
      value (tm_rcons i v1 vr)

/-- 类型级字段类型查找 -/
def Tlookup (i : String) (Tr : ty) : Option ty :=
  match Tr with
  | Ty_RCons i' T Tr' =>
      if i = i' then some T else Tlookup i Tr'
  | _ => none

/-- 项级字段值查找 -/
def tlookup (i : String) (tr : tm) : Option tm :=
  match tr with
  | tm_rcons i' t tr' =>
      if i = i' then some t else tlookup i tr'
  | _ => none

/-- 小步操作语义 -/
inductive step : tm → tm → Prop where
  | ST_AppAbs (x : String) (T2 : ty) (t1 v2 : tm) :
      value v2 →
      step (tm_app (tm_abs x T2 t1) v2) (subst x v2 t1)
  | ST_App1 (t1 t1' t2 : tm) :
      step t1 t1' →
      step (tm_app t1 t2) (tm_app t1' t2)
  | ST_App2 (v1 t2 t2' : tm) :
      value v1 →
      step t2 t2' →
      step (tm_app v1 t2) (tm_app v1 t2')
  | ST_Proj1 (t1 t1' : tm) (i : String) :
      step t1 t1' →
      step (tm_rproj t1 i) (tm_rproj t1' i)
  | ST_ProjRcd (tr : tm) (i : String) (vi : tm) :
      value tr →
      tlookup i tr = some vi →
      step (tm_rproj tr i) vi
  | ST_Rcd_Head (i : String) (t1 t1' tr2 : tm) :
      step t1 t1' →
      step (tm_rcons i t1 tr2) (tm_rcons i t1' tr2)
  | ST_Rcd_Tail (i : String) (v1 tr2 tr2' : tm) :
      value v1 →
      step tr2 tr2' →
      step (tm_rcons i v1 tr2) (tm_rcons i v1 tr2')

/- ################################################################# -/
/-! ## 2. 记录子类型关系 (Subtyping) -/
/- ################################################################# -/

/--
记录子类型归纳关系 `subtype S T`：
- 自反性与传递性
- 最大类型 `Ty_Top`
- 函数逆变与协变 `S_Arrow`
- 记录宽度子类型化：更多字段是更少字段的子类型 `S_RcdWidth`
- 记录深度子类型化：字段内部的子类型关系 `S_RcdDepth`
- 记录置换子类型化：相邻字段交换顺序保持子类型等价 `S_RcdPerm`
-/
inductive subtype : ty → ty → Prop where
  | S_Refl (T : ty) :
      well_formed_ty T →
      subtype T T
  | S_Trans (S U T : ty) :
      subtype S U →
      subtype U T →
      subtype S T
  | S_Top (S : ty) :
      well_formed_ty S →
      subtype S Ty_Top
  | S_Arrow (S1 S2 T1 T2 : ty) :
      subtype T1 S1 →
      subtype S2 T2 →
      subtype (Ty_Arrow S1 S2) (Ty_Arrow T1 T2)
  | S_RcdWidth (i : String) (T1 T2 : ty) :
      well_formed_ty (Ty_RCons i T1 T2) →
      subtype (Ty_RCons i T1 T2) Ty_RNil
  | S_RcdDepth (i : String) (S1 T1 Sr2 Tr2 : ty) :
      subtype S1 T1 →
      subtype Sr2 Tr2 →
      record_ty Sr2 →
      record_ty Tr2 →
      subtype (Ty_RCons i S1 Sr2) (Ty_RCons i T1 Tr2)
  | S_RcdPerm (i1 i2 : String) (T1 T2 Tr3 : ty) :
      well_formed_ty (Ty_RCons i1 T1 (Ty_RCons i2 T2 Tr3)) →
      i1 ≠ i2 →
      subtype (Ty_RCons i1 T1 (Ty_RCons i2 T2 Tr3))
              (Ty_RCons i2 T2 (Ty_RCons i1 T1 Tr3))

/- ################################################################# -/
/-! ## 3. 子类型化示例 (Examples) -/
/- ################################################################# -/

namespace Examples

def x : String := "x"
def y : String := "y"
def z : String := "z"
def j : String := "j"
def k : String := "k"
def i : String := "i"
def A : ty := Ty_Base "A"
def B : ty := Ty_Base "B"
def C : ty := Ty_Base "C"

def TRcd_j : ty :=
  Ty_RCons j (Ty_Arrow B B) Ty_RNil

def TRcd_kj : ty :=
  Ty_RCons k (Ty_Arrow A A) TRcd_j

theorem subtyping_example_0 :
    subtype (Ty_Arrow C TRcd_kj) (Ty_Arrow C Ty_RNil) := by
  sorry

/--
**** 练习: 2 星, standard (subtyping_example_1)
-/
theorem subtyping_example_1 :
    subtype TRcd_kj TRcd_j := by
  sorry

/--
**** 练习: 1 星, standard (subtyping_example_2)
-/
theorem subtyping_example_2 :
    subtype (Ty_Arrow Ty_Top TRcd_kj)
            (Ty_Arrow (Ty_Arrow C C) TRcd_j) := by
  sorry

/--
**** 练习: 1 星, standard (subtyping_example_3)
-/
theorem subtyping_example_3 :
    subtype (Ty_Arrow Ty_RNil (Ty_RCons j A Ty_RNil))
            (Ty_Arrow (Ty_RCons k B Ty_RNil) Ty_RNil) := by
  sorry

/--
**** 练习: 2 星, standard (subtyping_example_4)
-/
theorem subtyping_example_4 :
    subtype (Ty_RCons x A (Ty_RCons y B (Ty_RCons z C Ty_RNil)))
            (Ty_RCons z C (Ty_RCons y B (Ty_RCons x A Ty_RNil))) := by
  sorry

end Examples

/- ################################################################# -/
/-! ## 4. 子类型性质 (Properties of Subtyping) -/
/- ################################################################# -/

theorem subtype__wf (S T : ty) :
    subtype S T →
    well_formed_ty T ∧ well_formed_ty S := by
  sorry

theorem wf_rcd_lookup (i : String) (T Ti : ty) :
    well_formed_ty T →
    Tlookup i T = some Ti →
    well_formed_ty Ti := by
  sorry

theorem rcd_types_match (S T : ty) (i : String) (Ti : ty) :
    subtype S T →
    Tlookup i T = some Ti →
    ∃ Si, Tlookup i S = some Si ∧ subtype Si Ti := by
  sorry

/--
**** 练习: 3 星, standard (rcd_types_match_informal)
记录字段类型匹配引理的非形式化论证。
-/
def manual_grade_for_rcd_types_match_informal : Option (Nat × String) := none

/--
**** 练习: 3 星, standard, optional (sub_inversion_arrow)
函数箭头类型的子类型反演引理。
-/
theorem sub_inversion_arrow (U V1 V2 : ty) :
    subtype U (Ty_Arrow V1 V2) →
    ∃ U1 U2, U = Ty_Arrow U1 U2 ∧ subtype V1 U1 ∧ subtype U2 V2 := by
  sorry

/- ################################################################# -/
/-! ## 5. 定型系统与包容规则 (Typing) -/
/- ################################################################# -/

def context := partial_map ty

/--
带记录与子类型的定型关系：
包含包容规则 `T_Sub`。
-/
inductive has_type : context → tm → ty → Prop where
  | T_Var (Gamma : context) (x : String) (T : ty) :
      Gamma x = some T →
      well_formed_ty T →
      has_type Gamma (tm_var x) T
  | T_Abs (Gamma : context) (x : String) (T11 T12 : ty) (t12 : tm) :
      well_formed_ty T11 →
      has_type (x |-> T11 ; Gamma) t12 T12 →
      has_type Gamma (tm_abs x T11 t12) (Ty_Arrow T11 T12)
  | T_App (T1 T2 : ty) (Gamma : context) (t1 t2 : tm) :
      has_type Gamma t1 (Ty_Arrow T1 T2) →
      has_type Gamma t2 T1 →
      has_type Gamma (tm_app t1 t2) T2
  | T_Proj (Gamma : context) (i : String) (t : tm) (T Ti : ty) :
      has_type Gamma t T →
      Tlookup i T = some Ti →
      has_type Gamma (tm_rproj t i) Ti
  | T_Sub (Gamma : context) (t : tm) (S T : ty) :
      has_type Gamma t S →
      subtype S T →
      has_type Gamma t T
  | T_RNil (Gamma : context) :
      has_type Gamma tm_rnil Ty_RNil
  | T_RCons (Gamma : context) (i : String) (t : tm) (T : ty) (tr : tm) (Tr : ty) :
      has_type Gamma t T →
      has_type Gamma tr Tr →
      record_ty Tr →
      record_tm tr →
      has_type Gamma (tm_rcons i t tr) (Ty_RCons i T Tr)

/- ################################################################# -/
/-! ## 6. 定型示例 (Typing Examples) -/
/- ################################################################# -/

namespace Examples2

open Examples

def trcd_kj : tm :=
  tm_rcons k (tm_abs "z" A (tm_var "z"))
    (tm_rcons j (tm_abs "z" B (tm_var "z")) tm_rnil)

/--
**** 练习: 1 星, standard (typing_example_0)
-/
theorem typing_example_0 :
    has_type empty trcd_kj TRcd_kj := by
  sorry

/--
**** 练习: 2 星, standard (typing_example_1)
-/
theorem typing_example_1 :
    has_type empty
      (tm_app (tm_abs "x" TRcd_j (tm_rproj (tm_var "x") j)) trcd_kj)
      (Ty_Arrow B B) := by
  sorry

/--
**** 练习: 2 星, standard, optional (typing_example_2)
-/
theorem typing_example_2 :
    has_type empty
      (tm_app
        (tm_abs "z" (Ty_Arrow (Ty_Arrow C C) TRcd_j)
          (tm_rproj (tm_app (tm_var "z") (tm_abs "x" C (tm_var "x"))) j))
        (tm_abs "z" (Ty_Arrow C C) trcd_kj))
      (Ty_Arrow B B) := by
  sorry

end Examples2

/- ################################################################# -/
/-! ## 7. 定型性质验证 (Properties of Typing) -/
/- ################################################################# -/

theorem has_type__wf (Gamma : context) (t : tm) (T : ty) :
    has_type Gamma t T → well_formed_ty T := by
  sorry

theorem step_preserves_record_tm (tr tr' : tm) :
    record_tm tr →
    step tr tr' →
    record_tm tr' := by
  sorry

theorem lookup_field_in_value (v : tm) (T : ty) (i : String) (Ti : ty) :
    value v →
    has_type empty v T →
    Tlookup i T = some Ti →
    ∃ vi, tlookup i v = some vi ∧ has_type empty vi Ti := by
  sorry

/--
**** 练习: 3 星, standard (canonical_forms_of_arrow_types)
箭头类型的规范形式引理。
-/
theorem canonical_forms_of_arrow_types (Gamma : context) (s : tm) (T1 T2 : ty) :
    has_type Gamma s (Ty_Arrow T1 T2) →
    value s →
    ∃ x S1 s2, s = tm_abs x S1 s2 := by
  sorry

/-- 进益定理 (Progress Theorem) -/
theorem progress (t : tm) (T : ty) :
    has_type empty t T →
    value t ∨ ∃ t', step t t' := by
  sorry

/-- 函数抽象定型反演引理 -/
theorem typing_inversion_abs (Gamma : context) (x : String) (S1 : ty) (t2 : tm) (T : ty) :
    has_type Gamma (tm_abs x S1 t2) T →
    ∃ S2, subtype (Ty_Arrow S1 S2) T ∧ has_type (x |-> S1 ; Gamma) t2 S2 := by
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
  sorry

theorem substitution_preserves_typing (Gamma : context) (x : String) (U : ty) (t v : tm) (T : ty) :
    has_type (x |-> U ; Gamma) t T →
    has_type empty v U →
    has_type Gamma (subst x v t) T := by
  sorry

/-- 保型性定理 (Preservation Theorem) -/
theorem preservation (t t' : tm) (T : ty) :
    has_type empty t T →
    step t t' →
    has_type empty t' T := by
  sorry

end RecordSub

end PLF.RecordSub
