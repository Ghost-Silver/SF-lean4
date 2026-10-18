import SFLean4.PLF.Maps
import SFLean4.PLF.Smallstep
import SFLean4.PLF.Stlc
import SFLean4.PLF.MoreStlc

open Maps

namespace PLF.Typechecking

/-!
# 类型检查：简单类型 Lambda 演算的类型检查器 (Typechecking: A Typechecker for STLC)

STLC 的 `has_type` 关系定义了在一个上下文中项属于某个类型的含义。
然而，该关系本身并没有直接给出判定一个项是否良类型的“算法”。

幸运的是，定义 `has_type` 的规则是**语法导向 (Syntax-Directed)** 的——即对语言的每种语法形式，
恰好只有一条定型规则可用。这使得将定型规则翻译为一个类型检查函数变得非常直接：
该函数接受项和上下文，要么返回该项的类型，要么报告该项不可定型。

本章构造了这样一个类型检查函数，并形式化证明了它的**可靠性 (Soundness)** 与**完备性 (Completeness)**。
-/

/- ################################################################# -/
/-! ## 1. 类型的判等比较 (Comparing Types) -/
/- ################################################################# -/

namespace STLCTypes

open PLF.Stlc.STLC
open PLF.Stlc.STLC.ty

/-- 比较两个简单类型是否相等的可计算布尔函数 -/
def eqb_ty (T1 T2 : ty) : Bool :=
  match T1, T2 with
  | Ty_Bool, Ty_Bool => true
  | Ty_Arrow T11 T12, Ty_Arrow T21 T22 =>
      (eqb_ty T11 T21) && (eqb_ty T12 T22)
  | _, _ => false

/-- `eqb_ty` 的自反性 -/
theorem eqb_ty_refl (T : ty) :
    eqb_ty T T = true := by
  induction T with
  | Ty_Bool => rfl
  | Ty_Arrow T1 T2 ih1 ih2 =>
      simp [eqb_ty, ih1, ih2]

/-- `eqb_ty` 的反映性：布尔相等蕴含命题相等 -/
theorem eqb_ty__eq (T1 T2 : ty) :
    eqb_ty T1 T2 = true → T1 = T2 := by
  induction T1 generalizing T2 with
  | Ty_Bool =>
      cases T2 with
      | Ty_Bool => intro _; rfl
      | _ => intro h; contradiction
  | Ty_Arrow T11 T12 ih1 ih2 =>
      cases T2 with
      | Ty_Arrow T21 T22 =>
          intro h
          simp [eqb_ty] at h
          rcases h with ⟨h1, h2⟩
          rw [ih1 _ h1, ih2 _ h2]
      | _ => intro h; contradiction

end STLCTypes

/- ################################################################# -/
/-! ## 2. 类型检查器初步尝试 (The Typechecker - First Try) -/
/- ################################################################# -/

namespace FirstTry

open PLF.Stlc.STLC
open PLF.Stlc.STLC.ty
open PLF.Stlc.STLC.tm
open STLCTypes

/--
直接模式匹配的初版类型检查器：
递归检查子项类型，失败时返回 `none`。
-/
def type_check (Gamma : context) (t : tm) : Option ty :=
  match t with
  | tm_var x => Gamma x
  | tm_abs x T2 t1 =>
      match type_check (x |-> T2 ; Gamma) t1 with
      | some T1 => some (Ty_Arrow T2 T1)
      | none => none
  | tm_app t1 t2 =>
      match type_check Gamma t1, type_check Gamma t2 with
      | some (Ty_Arrow T11 T12), some T2 =>
          if eqb_ty T11 T2 then some T12 else none
      | _, _ => none
  | tm_true => some Ty_Bool
  | tm_false => some Ty_Bool
  | tm_if guard t f =>
      match type_check Gamma guard with
      | some Ty_Bool =>
          match type_check Gamma t, type_check Gamma f with
          | some T1, some T2 =>
              if eqb_ty T1 T2 then some T1 else none
          | _, _ => none
      | _ => none

end FirstTry

/- ################################################################# -/
/-! ## 3. 单子风格的优雅类型检查器 (STLCChecker) -/
/- ################################################################# -/

namespace STLCChecker

open PLF.Stlc.STLC
open PLF.Stlc.STLC.ty
open PLF.Stlc.STLC.tm
open STLCTypes

/--
利用 Lean 4 的 `Option` 单子 `do` 记号，以命令式风格精炼表达的类型检查器。
-/
def type_check (Gamma : context) (t : tm) : Option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | some T => some T
      | none => none
  | tm_abs x T2 t1 => do
      let T1 ← type_check (x |-> T2 ; Gamma) t1
      return (Ty_Arrow T2 T1)
  | tm_app t1 t2 => do
      let T1 ← type_check Gamma t1
      let T2 ← type_check Gamma t2
      match T1 with
      | Ty_Arrow T11 T12 =>
          if eqb_ty T11 T2 then some T12 else none
      | _ => none
  | tm_true => some Ty_Bool
  | tm_false => some Ty_Bool
  | tm_if guard t1 t2 => do
      let Tguard ← type_check Gamma guard
      let T1 ← type_check Gamma t1
      let T2 ← type_check Gamma t2
      match Tguard with
      | Ty_Bool =>
          if eqb_ty T1 T2 then some T1 else none
      | _ => none

/-! ### 性质验证 (Properties) -/

/--
类型检查器的可靠性定理 (Soundness)：
若算法断言项 `t` 具有类型 `T`，则该项在原定义系统下确实良类型。
-/
theorem type_checking_sound (Gamma : context) (t : tm) (T : ty) :
    type_check Gamma t = some T → has_type Gamma t T := by
  sorry

/--
类型检查器的完备性定理 (Completeness)：
若项 `t` 在原系统中良类型，则算法必定成功并返回该类型。
-/
theorem type_checking_complete (Gamma : context) (t : tm) (T : ty) :
    has_type Gamma t T → type_check Gamma t = some T := by
  sorry

end STLCChecker

/- ################################################################# -/
/-! ## 4. 扩展特性的类型检查器 (TypecheckerExtensions) -/
/- ################################################################# -/

namespace TypecheckerExtensions

open PLF.MoreStlc.STLCExtended
open PLF.MoreStlc.STLCExtended.ty
open PLF.MoreStlc.STLCExtended.tm

/-- 丰富后类型系统的可判定相等比较函数 -/
def eqb_ty (T1 T2 : ty) : Bool :=
  match T1, T2 with
  | Ty_Nat, Ty_Nat => true
  | Ty_Unit, Ty_Unit => true
  | Ty_Arrow T11 T12, Ty_Arrow T21 T22 =>
      (eqb_ty T11 T21) && (eqb_ty T12 T22)
  | Ty_Prod T11 T12, Ty_Prod T21 T22 =>
      (eqb_ty T11 T21) && (eqb_ty T12 T22)
  | Ty_Sum T11 T12, Ty_Sum T21 T22 =>
      (eqb_ty T11 T21) && (eqb_ty T12 T22)
  | Ty_List T11, Ty_List T21 =>
      eqb_ty T11 T21
  | _, _ => false

theorem eqb_ty_refl (T : ty) :
    eqb_ty T T = true := by
  induction T with
  | Ty_Nat => rfl
  | Ty_Unit => rfl
  | Ty_Arrow T1 T2 ih1 ih2 => simp [eqb_ty, ih1, ih2]
  | Ty_Prod T1 T2 ih1 ih2 => simp [eqb_ty, ih1, ih2]
  | Ty_Sum T1 T2 ih1 ih2 => simp [eqb_ty, ih1, ih2]
  | Ty_List T ih => simp [eqb_ty, ih]

theorem eqb_ty__eq (T1 T2 : ty) :
    eqb_ty T1 T2 = true → T1 = T2 := by
  induction T1 generalizing T2 with
  | Ty_Nat =>
      cases T2 with
      | Ty_Nat => intro _; rfl
      | _ => intro h; contradiction
  | Ty_Unit =>
      cases T2 with
      | Ty_Unit => intro _; rfl
      | _ => intro h; contradiction
  | Ty_Arrow T11 T12 ih1 ih2 =>
      cases T2 with
      | Ty_Arrow T21 T22 =>
          intro h
          simp [eqb_ty] at h
          rcases h with ⟨h1, h2⟩
          rw [ih1 _ h1, ih2 _ h2]
      | _ => intro h; contradiction
  | Ty_Sum T11 T12 ih1 ih2 =>
      cases T2 with
      | Ty_Sum T21 T22 =>
          intro h
          simp [eqb_ty] at h
          rcases h with ⟨h1, h2⟩
          rw [ih1 _ h1, ih2 _ h2]
      | _ => intro h; contradiction
  | Ty_List T1 ih =>
      cases T2 with
      | Ty_List T2 =>
          intro h
          simp [eqb_ty] at h
          rw [ih _ h]
      | _ => intro h; contradiction
  | Ty_Prod T11 T12 ih1 ih2 =>
      cases T2 with
      | Ty_Prod T21 T22 =>
          intro h
          simp [eqb_ty] at h
          rcases h with ⟨h1, h2⟩
          rw [ih1 _ h1, ih2 _ h2]
      | _ => intro h; contradiction

/--
**** 练习: 4 星, standard (type_check_defn)
扩展类型检查器以支持和类型、列表、单位、对偶、Let 与 Fix。
-/
def type_check (Gamma : context) (t : tm) : Option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | some T => some T
      | none   => none
  | tm_abs x1 T1 t2 => do
      let T2 ← type_check (x1 |-> T1 ; Gamma) t2
      return (Ty_Arrow T1 T2)
  | tm_app t1 t2 => do
      let T1 ← type_check Gamma t1
      let T2 ← type_check Gamma t2
      match T1 with
      | Ty_Arrow T11 T12 =>
          if eqb_ty T11 T2 then some T12 else none
      | _ => none
  | tm_const _ =>
      some Ty_Nat
  | tm_succ t1 => do
      let T1 ← type_check Gamma t1
      match T1 with
      | Ty_Nat => some Ty_Nat
      | _ => none
  | tm_pred t1 => do
      let T1 ← type_check Gamma t1
      match T1 with
      | Ty_Nat => some Ty_Nat
      | _ => none
  | tm_mult t1 t2 => do
      let T1 ← type_check Gamma t1
      let T2 ← type_check Gamma t2
      match T1, T2 with
      | Ty_Nat, Ty_Nat => some Ty_Nat
      | _, _ => none
  | tm_if0 guard t f => do
      let Tguard ← type_check Gamma guard
      let T1 ← type_check Gamma t
      let T2 ← type_check Gamma f
      match Tguard with
      | Ty_Nat => if eqb_ty T1 T2 then some T1 else none
      | _ => none
  | tm_lcase t0 t1 x21 x22 t2 => do
      let T0 ← type_check Gamma t0
      match T0 with
      | Ty_List T => do
          let T1 ← type_check Gamma t1
          let T2 ← type_check (x21 |-> T ; x22 |-> Ty_List T ; Gamma) t2
          if eqb_ty T1 T2 then some T1 else none
      | _ => none
  | _ => none

def manual_grade_for_type_check_defn : Option (Nat × String) := none

/--
**** 练习: 2 星, standard (ext_type_checking_sound)
扩展类型系统的类型检查器可靠性证明。
-/
theorem type_checking_sound (Gamma : context) (t : tm) (T : ty) :
    type_check Gamma t = some T →
    has_type Gamma t T := by
  sorry

/--
**** 练习: 2 星, standard (ext_type_checking_complete)
扩展类型系统的类型检查器完备性证明。
-/
theorem type_checking_complete (Gamma : context) (t : tm) (T : ty) :
    has_type Gamma t T →
    type_check Gamma t = some T := by
  sorry

end TypecheckerExtensions

/- ################################################################# -/
/-! ## 5. 小步求值函数及其性质 (StepFunction) -/
/- ################################################################# -/

namespace StepFunction

open PLF.MoreStlc.STLCExtended
open PLF.MoreStlc.STLCExtended.ty
open PLF.MoreStlc.STLCExtended.tm

/--
**** 练习: 2 星, standard, optional (valuef_defn)
值判断的可计算布尔函数。
-/
def valuef (t : tm) : Bool :=
  match t with
  | tm_var _ => false
  | tm_abs _ _ _ => true
  | tm_app _ _ => false
  | tm_const _ => true
  | tm_succ _ | tm_pred _ | tm_mult _ _ | tm_if0 _ _ _ => false
  | _ => false

def manual_grade_for_valuef_defn : Option (Nat × String) := none

/-- 条件断言辅助函数 -/
def assert (b : Bool) (a : Option tm) : Option tm :=
  if b then a else none

/--
**** 练习: 3 星, standard, optional (stepf_defn)
小步操作语义的可计算函数形式。
-/
def stepf (t : tm) : Option tm :=
  match t with
  | tm_var _ => none
  | tm_abs _ _ _ => none
  | tm_app t1 t2 =>
      match stepf t1, stepf t2, t1 with
      | some t1', _, _ => some (tm_app t1' t2)
      | none, some t2', _ => assert (valuef t1) (some (tm_app t1 t2'))
      | none, none, tm_abs x _ t11 =>
          assert (valuef t2) (some (subst x t2 t11))
      | _, _, _ => none
  | tm_const _ => none
  | tm_succ t1 =>
      match stepf t1, t1 with
      | some t1', _ => some (tm_succ t1')
      | none, tm_const n => some (tm_const (n + 1))
      | none, _ => none
  | tm_pred t1 =>
      match stepf t1, t1 with
      | some t1', _ => some (tm_pred t1')
      | none, tm_const n => some (tm_const (n - 1))
      | _, _ => none
  | tm_mult t1 t2 =>
      match stepf t1, stepf t2, t1, t2 with
      | some t1', _, _, _ => some (tm_mult t1' t2)
      | none, some t2', _, _ =>
          assert (valuef t1) (some (tm_mult t1 t2'))
      | none, none, tm_const n1, tm_const n2 => some (tm_const (n1 * n2))
      | _, _, _, _ => none
  | tm_if0 guard t f =>
      match stepf guard, guard with
      | some guard', _ => some (tm_if0 guard' t f)
      | none, tm_const 0 => some t
      | none, tm_const (_ + 1) => some f
      | _, _ => none
  | tm_lcase t0 t1 x21 x22 t2 =>
      match stepf t0, t0 with
      | some t0', _ => some (tm_lcase t0' t1 x21 x22 t2)
      | none, tm_nil _ => some t1
      | none, tm_cons vh vt =>
          assert (valuef vh) (assert (valuef vt)
            (some (subst x22 vt (subst x21 vh t2))))
      | none, _ => none
  | _ => none

def manual_grade_for_stepf_defn : Option (Nat × String) := none

/--
**** 练习: 2 星, standard, optional (sound_valuef)
`valuef` 关于归纳关系 `value` 的可靠性。
-/
theorem sound_valuef (t : tm) :
    valuef t = true → value t := by
  sorry

/--
**** 练习: 2 星, standard, optional (complete_valuef)
`valuef` 关于归纳关系 `value` 的完备性。
-/
theorem complete_valuef (t : tm) :
    value t → valuef t = true := by
  sorry

/--
**** 练习: 2 星, standard, optional (sound_stepf)
`stepf` 关于单步归约关系 `step` 的可靠性。
-/
theorem sound_stepf (t t' : tm) :
    stepf t = some t' → step t t' := by
  sorry

/--
**** 练习: 2 星, standard, optional (value_stepf_nf)
每一个值都是 `stepf` 的范式（无法再求值）。
-/
theorem value_stepf_nf (t : tm) :
    value t → stepf t = none := by
  sorry

/--
**** 练习: 2 星, standard, optional (complete_stepf)
`stepf` 关于单步归约关系 `step` 的完备性。
-/
theorem complete_stepf (t t' : tm) :
    step t t' → stepf t = some t' := by
  sorry

end StepFunction

/- ################################################################# -/
/-! ## 6. 完整解析与解释器驱动 (StlcImpl) -/
/- ################################################################# -/

/-!
**** 练习: 5 星, standard, optional (stlc_impl)
结合词法语法分析器与上述类型检查、小步求值函数，构造完整的端到端解释器。
-/
namespace StlcImpl

open StepFunction

end StlcImpl

end PLF.Typechecking
