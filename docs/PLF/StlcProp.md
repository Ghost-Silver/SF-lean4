---
title: "StlcProp: STLC 性质验证：规范形式、弱化引理与保型性"
---

```lean
import SFLean4.PLF.Maps
import SFLean4.PLF.Types
import SFLean4.PLF.Stlc
import SFLean4.PLF.Smallstep
```

# 软件基础 第二卷：程序语言基础 (PLF)

## 模块：STLC 的性质 (StlcProp: Properties of STLC)

在上一章中，我们建立了简单类型 Lambda 演算（STLC）的语法、操作语义与定型规则。
在本章中，我们将建立 STLC 的核心元理论，尤其是著名的**类型安全定理（Type Safety / Soundness）**。

与纯算术语言相比，STLC 引入了变量绑定与高阶函数代换，因此证明过程更为精密，需要建立一系列精巧的引理链：
1. **规范形式引理（Canonical Forms）**：刻画良类型值的语法形态；
2. **进益定理（Progress）**：良类型的闭项要么是值，要么能向前单步归约；
3. **弱化引理（Weakening）**：在上下文中添加不相干变量类型声明不影响已有定型；
4. **代换保型引理（Substitution Preserves Typing）**：用良类型的封闭项代换变量保持类型不变；
5. **保型性定理（Preservation / Subject Reduction）**：单步归约保持类型不变；
6. **类型健全性（Soundness）**：良类型项在多步归约中绝不会陷入卡住（Stuck）状态；
7. **类型唯一性（Uniqueness of Types）**与**上下文不变性（Context Invariance）**。

```lean
namespace PLF.StlcProp

open Maps
open PLF.Stlc.STLC
open PLF.Stlc.STLC.tm
open PLF.Stlc.STLC.ty

namespace STLCProp
```

## 1. 规范形式引理 (Canonical Forms)

规范形式引理表明：封闭且具有特定类型的良类型值，其外层语法构造子是完全确定的。
- 若闭值具有类型 `Bool`，则它必为 `true` 或 `false`；
- 若闭值具有函数类型 `T1 -> T2`，则它必为一个抽象项 `\x:T1, u`。

```lean
/-- 布尔类型的规范形式引理 -/
theorem canonical_forms_bool (t : tm) :
  has_type empty t Ty_Bool →
  value t →
  (t = tm_true) ∨ (t = tm_false) := by
  intro HT HVal
  cases HVal with
  | v_abs x T t1 =>
    cases HT
  | v_true => left; rfl
  | v_false => right; rfl

/-- 函数类型的规范形式引理 -/
theorem canonical_forms_fun (t : tm) (T1 T2 : ty) :
  has_type empty t (Ty_Arrow T1 T2) →
  value t →
  ∃ x u, t = tm_abs x T1 u := by
  intro HT HVal
  cases HVal with
  | v_abs x T t1 =>
    cases HT with
    | T_Abs _ _ T1' T2' _ _ =>
      exists x, t1
  | v_true => cases HT
  | v_false => cases HT
```

## 2. 进益定理 (Progress)

进益定理表明：任何在空上下文中良类型的项（闭项），要么已经是一个值，要么可以向前单步归约。
它断言良类型项绝不会在求值过程中“陷入未知停滞”。

```lean
theorem progress (t : tm) (T : ty) :
  has_type empty t T →
  value t ∨ ∃ t', step t t' := by
  sorry

/--
**** 练习: 3 星, advanced (progress_from_term_ind)
尝试对项 `t` 本身（而不是定型推导树）进行结构归纳来证明进益定理。
-/
theorem progress' (t : tm) (T : ty) :
  has_type empty t T →
  value t ∨ ∃ t', step t t' := by
  sorry
```

## 3. 弱化引理与代换引理 (Weakening & Substitution)

证明保型性定理（Preservation）的核心在于处理应用规则中的 $\beta$-归约：
`(\x:T, t12) v2 --> [x := v2] t12`。
我们需要证明代换操作保持类型不变。为此，首先需要建立弱化引理。

```lean
/-- 弱化引理：在更大的上下文 `Gamma'` 中，原有的定型判定依然成立。 -/
theorem weakening (Gamma Gamma' : context) (t : tm) (T : ty) :
  includedin Gamma Gamma' →
  has_type Gamma t T →
  has_type Gamma' t T := by
  sorry

/-- 弱化引理在空上下文下的特例推论 -/
theorem weakening_empty (Gamma : context) (t : tm) (T : ty) :
  has_type empty t T →
  has_type Gamma t T := by
  intro H
  apply weakening empty Gamma t T _ H
  intro x v Hx
  cases Hx

/-- 代换保型引理：用良类型的闭项 `v` 代换 `t` 中的自由变量 `x`，保持原类型 `T` 不变。 -/
theorem substitution_preserves_typing (Gamma : context) (x : String) (U : ty) (t v : tm) (T : ty) :
  has_type (x |-> U ; Gamma) t T →
  has_type empty v U →
  has_type Gamma (subst x v t) T := by
  sorry

/--
**** 练习: 3 星, advanced (substitution_preserves_typing_from_typing_ind)
尝试对定型推导树进行归纳来证明代换保型引理。
-/
theorem substitution_preserves_typing_from_typing_ind (Gamma : context) (x : String) (U : ty) (t v : tm) (T : ty) :
  has_type (x |-> U ; Gamma) t T →
  has_type empty v U →
  has_type Gamma (subst x v t) T := by
  sorry
```

## 4. 类型保型性定理 (Preservation)

类型保型性定理（也称主词归约定理，Subject Reduction）：
若闭项 `t` 具有类型 `T`，且 `t` 单步归约到 `t'`，则 `t'` 也必具有类型 `T`。

```lean
theorem preservation (t t' : tm) (T : ty) :
  has_type empty t T →
  step t t' →
  has_type empty t' T := by
  sorry

/--
**** 练习: 2 星, standard, especially useful (subject_expansion_stlc)
主词扩张反例：展示存在项 `t`，虽然它单步归约到良类型项 `t'`，但 `t` 本身不是良类型的
（要求反例不包含条件表达式）。
-/
theorem not_subject_expansion :
  ∃ t t' T, step t t' ∧ has_type empty t' T ∧ ¬ has_type empty t T := by
  sorry

/-- 手动评分标记：subject_expansion_stlc -/
def manual_grade_for_subject_expansion_stlc : Option (Nat × String) := none
```

## 5. 类型健全性 (Type Soundness)

结合进益定理与保型性定理，我们证明 STLC 的类型健全性：
从良类型的封闭项出发，无论进行多少步小步规约，都绝不会到达卡住（Stuck）状态。

```lean
/-- 卡住状态：既不可单步规约，又不是规范值。 -/
def stuck (t : tm) : Prop :=
  PLF.Smallstep.normal_form step t ∧ ¬ value t

/--
**** 练习: 2 星, standard, optional (type_soundness)
证明类型健全性定理。
-/
theorem type_soundness (t t' : tm) (T : ty) :
  has_type empty t T →
  multistep t t' →
  ¬ stuck t' := by
  sorry
```

## 6. 类型唯一性 (Uniqueness of Types)

```lean
/--
**** 练习: 3 星, standard (unique_types)
证明在给定上下文中，任何项至多只能拥有一个唯一的类型。
-/
theorem unique_types (Gamma : context) (e : tm) (T T' : ty) :
  has_type Gamma e T →
  has_type Gamma e T' →
  T = T' := by
  sorry
```

## 7. 上下文不变性 (Context Invariance)

为了形式化自由变量与闭项的严格概念，我们定义 `appears_free_in` 关系。

```lean
/-- 变量 `x` 自由出现在项 `t` 中 -/
inductive appears_free_in (x : String) : tm → Prop where
  | afi_var :
      appears_free_in x (tm_var x)
  | afi_app1 (t1 t2 : tm) :
      appears_free_in x t1 →
      appears_free_in x (tm_app t1 t2)
  | afi_app2 (t1 t2 : tm) :
      appears_free_in x t2 →
      appears_free_in x (tm_app t1 t2)
  | afi_abs (y : String) (T1 : ty) (t1 : tm) :
      y ≠ x →
      appears_free_in x t1 →
      appears_free_in x (tm_abs y T1 t1)
  | afi_if1 (t1 t2 t3 : tm) :
      appears_free_in x t1 →
      appears_free_in x (tm_if t1 t2 t3)
  | afi_if2 (t1 t2 t3 : tm) :
      appears_free_in x t2 →
      appears_free_in x (tm_if t1 t2 t3)
  | afi_if3 (t1 t2 t3 : tm) :
      appears_free_in x t3 →
      appears_free_in x (tm_if t1 t2 t3)

/-- 封闭项：不包含任何自由出现的变量。 -/
def closed (t : tm) : Prop :=
  ∀ x, ¬ appears_free_in x t

/--
**** 练习: 1 星, standard, optional (afi)
以推理规则形式阐述 `appears_free_in` 的非形式化定义。
-/
def manual_grade_for_afi : Option (Nat × String) := none

/--
**** 练习: 2 星, standard (free_in_context)
若变量 `x` 自由出现在良类型项 `t` 中，则上下文 `Gamma` 必给 `x` 分配了某个类型。
-/
theorem free_in_context (x : String) (t : tm) (T : ty) (Gamma : context) :
  appears_free_in x t →
  has_type Gamma t T →
  ∃ T', Gamma x = some T' := by
  sorry

/--
**** 练习: 2 星, standard, optional (typable_empty__closed)
在空上下文中良类型的项必然是封闭项。
-/
theorem typable_empty__closed (t : tm) (T : ty) :
  has_type empty t T →
  closed t := by
  sorry

/--
**** 练习: 3 星, standard, optional (context_invariance)
上下文不变性引理：若两个上下文在项的所有自由变量上给出的类型一致，则项在两上下文中的定型一致。
-/
theorem context_invariance (Gamma Gamma' : context) (t : tm) (T : ty) :
  has_type Gamma t T →
  (∀ x, appears_free_in x t → Gamma x = Gamma' x) →
  has_type Gamma' t T := by
  sorry

/--
**** 练习: 1 星, standard, optional (progress_preservation_statement)
纸笔练习：不看上文，独立写出进益性与保型性的形式命题。
-/
def manual_grade_for_progress_preservation_statement : Option (Nat × String) := none

/--
**** 练习: 2 星, standard (stlc_variation1)
变体讨论：加入归约规则 `t --> zap` 与定型规则 `Gamma |-- zap \in T` 对语义性质的影响。
-/
def manual_grade_for_stlc_variation1 : Option (Nat × String) := none

/--
**** 练习: 2 星, standard (stlc_variation2)
变体讨论：加入项 `foo` 与规约规则对语义性质的影响。
-/
def manual_grade_for_stlc_variation2 : Option (Nat × String) := none

/--
**** 练习: 2 星, standard (stlc_variation3)
变体讨论：移除 `ST_App1` 规则对语义性质的影响。
-/
def manual_grade_for_stlc_variation3 : Option (Nat × String) := none
```

**** 练习: 2 星, standard, optional (stlc_variation4)
变体讨论：加入规则 `if true then t1 else t2 --> true`。

**** 练习: 2 星, standard, optional (stlc_variation5)
变体讨论：加入规则 `Gamma |-- t1 \in Bool->Bool->Bool → Gamma |-- t2 \in Bool → Gamma |-- t1 t2 \in Bool`。

**** 练习: 2 星, standard, optional (stlc_variation6)
变体讨论：加入规则 `Gamma |-- t1 \in Bool → Gamma |-- t2 \in Bool → Gamma |-- t1 t2 \in Bool`。

**** 练习: 2 星, standard, optional (stlc_variation7)
变体讨论：加入规则 `|-- \x:Bool, t \in Bool`。

```lean
end STLCProp
```

## 8. 扩展练习：带算术的 STLC (STLC with Arithmetic)

**** 练习: STLC with Arithmetic

```lean
namespace STLCArith

/-- STLCArith 类型定义：包含函数类型与自然数类型 -/
inductive ty : Type where
  | Ty_Arrow : ty → ty → ty
  | Ty_Nat : ty
  deriving Repr, DecidableEq

/-- STLCArith 项定义：变量、应用、抽象、常量、后继、前驱、乘法与零分支 -/
inductive tm : Type where
  | tm_var : String → tm
  | tm_app : tm → tm → tm
  | tm_abs : String → ty → tm → tm
  | tm_const : Nat → tm
  | tm_succ : tm → tm
  | tm_pred : tm → tm
  | tm_mult : tm → tm → tm
  | tm_if0 : tm → tm → tm → tm
  deriving Repr, DecidableEq

/--
**** 练习: 5 星, standard (STLCArith.subst)
实现带有算术运算的变量代换函数。
-/
def subst (x : String) (s : tm) (t : tm) : tm :=
  match t with
  | tm.tm_var y => if x = y then s else tm.tm_var y
  | tm.tm_app t1 t2 => tm.tm_app (subst x s t1) (subst x s t2)
  | tm.tm_abs y T t1 => if x = y then tm.tm_abs y T t1 else tm.tm_abs y T (subst x s t1)
  | tm.tm_const n => tm.tm_const n
  | tm.tm_succ t1 => tm.tm_succ (subst x s t1)
  | tm.tm_pred t1 => tm.tm_pred (subst x s t1)
  | tm.tm_mult t1 t2 => tm.tm_mult (subst x s t1) (subst x s t2)
  | tm.tm_if0 t1 t2 t3 => tm.tm_if0 (subst x s t1) (subst x s t2) (subst x s t3)

/-- 值定义：抽象与自然数常量均为值 -/
inductive value : tm → Prop where
  | v_abs (x : String) (T : ty) (t : tm) : value (tm.tm_abs x T t)
  | v_nat (n : Nat) : value (tm.tm_const n)

/-- 单步规约关系 -/
inductive step : tm → tm → Prop where
  | ST_AppAbs (x : String) (T : ty) (t : tm) (v : tm) :
      value v → step (tm.tm_app (tm.tm_abs x T t) v) (subst x v t)
  | ST_App1 (t1 t1' t2 : tm) :
      step t1 t1' → step (tm.tm_app t1 t2) (tm.tm_app t1' t2)
  | ST_App2 (v1 t2 t2' : tm) :
      value v1 → step t2 t2' → step (tm.tm_app v1 t2) (tm.tm_app v1 t2')
  | ST_Succ (t1 t1' : tm) :
      step t1 t1' → step (tm.tm_succ t1) (tm.tm_succ t1')
  | ST_SuccNat (n : Nat) :
      step (tm.tm_succ (tm.tm_const n)) (tm.tm_const (n + 1))
  | ST_Pred (t1 t1' : tm) :
      step t1 t1' → step (tm.tm_pred t1) (tm.tm_pred t1')
  | ST_PredNat (n : Nat) :
      step (tm.tm_pred (tm.tm_const n)) (tm.tm_const (n - 1))
  | ST_Mult1 (t1 t1' t2 : tm) :
      step t1 t1' → step (tm.tm_mult t1 t2) (tm.tm_mult t1' t2)
  | ST_Mult2 (v1 t2 t2' : tm) :
      value v1 → step t2 t2' → step (tm.tm_mult v1 t2) (tm.tm_mult v1 t2')
  | ST_MultNat (n1 n2 : Nat) :
      step (tm.tm_mult (tm.tm_const n1) (tm.tm_const n2)) (tm.tm_const (n1 * n2))
  | ST_If0 (t1 t1' t2 t3 : tm) :
      step t1 t1' → step (tm.tm_if0 t1 t2 t3) (tm.tm_if0 t1' t2 t3)
  | ST_If0Zero (t2 t3 : tm) :
      step (tm.tm_if0 (tm.tm_const 0) t2 t3) t2
  | ST_If0NonZero (n : Nat) (t2 t3 : tm) :
      step (tm.tm_if0 (tm.tm_const (n + 1)) t2 t3) t3

def multistep : tm → tm → Prop := PLF.Smallstep.multi step

/-- 示例求值 -/
theorem Nat_step_example : ∃ t,
  multistep
    (tm.tm_app (tm.tm_app (tm.tm_abs "x" ty.Ty_Nat (tm.tm_abs "y" ty.Ty_Nat (tm.tm_mult (tm.tm_var "x") (tm.tm_var "y"))))
      (tm.tm_const 3)) (tm.tm_const 2))
    t := by
  sorry

def context : Type := partial_map ty

/-- STLCArith 定型规则 -/
inductive has_type : context → tm → ty → Prop where
  | T_Var (Gamma : context) (x : String) (T1 : ty) :
      Gamma x = some T1 → has_type Gamma (tm.tm_var x) T1
  | T_Abs (Gamma : context) (x : String) (T1 T2 : ty) (t1 : tm) :
      has_type (x |-> T2 ; Gamma) t1 T1 → has_type Gamma (tm.tm_abs x T2 t1) (ty.Ty_Arrow T2 T1)
  | T_App (T1 T2 : ty) (Gamma : context) (t1 t2 : tm) :
      has_type Gamma t1 (ty.Ty_Arrow T2 T1) → has_type Gamma t2 T2 → has_type Gamma (tm.tm_app t1 t2) T1
  | T_Nat (Gamma : context) (n : Nat) :
      has_type Gamma (tm.tm_const n) ty.Ty_Nat
  | T_Succ (Gamma : context) (t1 : tm) :
      has_type Gamma t1 ty.Ty_Nat → has_type Gamma (tm.tm_succ t1) ty.Ty_Nat
  | T_Pred (Gamma : context) (t1 : tm) :
      has_type Gamma t1 ty.Ty_Nat → has_type Gamma (tm.tm_pred t1) ty.Ty_Nat
  | T_Mult (Gamma : context) (t1 t2 : tm) :
      has_type Gamma t1 ty.Ty_Nat → has_type Gamma t2 ty.Ty_Nat → has_type Gamma (tm.tm_mult t1 t2) ty.Ty_Nat
  | T_If0 (t1 t2 t3 : tm) (T1 : ty) (Gamma : context) :
      has_type Gamma t1 ty.Ty_Nat → has_type Gamma t2 T1 → has_type Gamma t3 T1 → has_type Gamma (tm.tm_if0 t1 t2 t3) T1

/-- 示例定型 -/
theorem Nat_typing_example :
  has_type empty
    (tm.tm_app (tm.tm_app (tm.tm_abs "x" ty.Ty_Nat (tm.tm_abs "y" ty.Ty_Nat (tm.tm_mult (tm.tm_var "x") (tm.tm_var "y"))))
      (tm.tm_const 3)) (tm.tm_const 2))
    ty.Ty_Nat := by
  sorry

/--
**** 练习: 4 星, standard (STLCArith.weakening)
证明算术扩展版本的弱化引理。
-/
theorem weakening (Gamma Gamma' : context) (t : tm) (T : ty) :
  includedin Gamma Gamma' →
  has_type Gamma t T →
  has_type Gamma' t T := by
  sorry

/--
**** 练习: 4 星, standard (STLCArith.preservation)
证明算术扩展版本的保型性定理。
-/
theorem preservation (t t' : tm) (T : ty) :
  has_type empty t T →
  step t t' →
  has_type empty t' T := by
  sorry

/--
**** 练习: 4 星, standard (STLCArith.progress)
证明算术扩展版本的进益定理。
-/
theorem progress (t : tm) (T : ty) :
  has_type empty t T →
  value t ∨ ∃ t', step t t' := by
  sorry

end STLCArith

end PLF.StlcProp
```
