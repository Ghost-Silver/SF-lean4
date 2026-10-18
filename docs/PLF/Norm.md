---
title: "Norm: STLC 强规范化：Tait 逻辑关系与停机性证明"
---

```lean
import SFLean4.PLF.Maps
import SFLean4.PLF.Smallstep

open Maps

namespace PLF.Norm
```

# 规范化：简单类型 Lambda 演算的强规范化定理 (Norm: Normalization of STLC)

在前面的章节中，我们证明了 STLC 的类型安全性（Progress 和 Preservation）。
然而，STLC 还有一个更为深邃优美的基本理论性质：
**所有良类型的项都必然在有限步内停机归约到范式（值）**——即所谓的**规范化定理 (Normalization Theorem)**，
或称**强规范化 (Strong Normalization)**。

直接对项的结构或定型推导进行普通归纳无法完成该证明（因为函数应用的代换会复制子项并放大项的尺寸）。
为了突破这一本质困难，本章引入了证明论与类型论中最深刻的核心工具：
**逻辑关系 (Logical Relations)** / **可归约性候选 (Reducibility Candidates)**（由 Tait 提出，Girard 推广）。
我们对类型 `T` 归纳定义饱和谓词 `R T t`，并证明所有良类型项均属于 `R`，从而建立规范化定理。

**** 练习: 2 星, standard (norm_fail)
思考题：为什么直接对良类型项的尺寸进行直接归纳无法证明规范化？

```lean
def manual_grade_for_norm_fail : Option (Nat × String) := none
```

**** 练习: 5 星, standard, especially useful (norm)
补全逻辑关系法强规范化证明的核心引理与扩展。

```lean
def manual_grade_for_norm : Option (Nat × String) := none
```

## 1. 语言定义 (Language)

```lean
/-- 带有布尔值与对偶积类型的简单类型 -/
inductive ty : Type where
  | Ty_Bool : ty
  | Ty_Arrow : ty → ty → ty
  | Ty_Prod : ty → ty → ty
  deriving Repr, DecidableEq

open ty

/-- 带有布尔值、分支条件与对偶投影的项集合 -/
inductive tm : Type where
  | tm_var : String → tm
  | tm_app : tm → tm → tm
  | tm_abs : String → ty → tm → tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm → tm → tm → tm
  | tm_pair : tm → tm → tm
  | tm_fst : tm → tm
  | tm_snd : tm → tm
  deriving Repr, DecidableEq

open tm

/-- 变量代换函数 `[x := s] t` -/
def subst (x : String) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if x = y then s else t
  | tm_abs y T t1 =>
      if x = y then t else tm_abs y T (subst x s t1)
  | tm_app t1 t2 =>
      tm_app (subst x s t1) (subst x s t2)
  | tm_true =>
      tm_true
  | tm_false =>
      tm_false
  | tm_if t1 t2 t3 =>
      tm_if (subst x s t1) (subst x s t2) (subst x s t3)
  | tm_pair t1 t2 =>
      tm_pair (subst x s t1) (subst x s t2)
  | tm_fst t0 =>
      tm_fst (subst x s t0)
  | tm_snd t0 =>
      tm_snd (subst x s t0)

/-- 值断言：函数抽象、布尔常量与值对偶均为值 -/
inductive value : tm → Prop where
  | v_abs (x : String) (T2 : ty) (t1 : tm) : value (tm_abs x T2 t1)
  | v_true : value tm_true
  | v_false : value tm_false
  | v_pair (v1 v2 : tm) : value v1 → value v2 → value (tm_pair v1 v2)

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
  | ST_IfTrue (t1 t2 : tm) :
      step (tm_if tm_true t1 t2) t1
  | ST_IfFalse (t1 t2 : tm) :
      step (tm_if tm_false t1 t2) t2
  | ST_If (t1 t1' t2 t3 : tm) :
      step t1 t1' →
      step (tm_if t1 t2 t3) (tm_if t1' t2 t3)
  | ST_Pair1 (t1 t1' t2 : tm) :
      step t1 t1' →
      step (tm_pair t1 t2) (tm_pair t1' t2)
  | ST_Pair2 (v1 t2 t2' : tm) :
      value v1 →
      step t2 t2' →
      step (tm_pair v1 t2) (tm_pair v1 t2')
  | ST_Fst1 (t0 t0' : tm) :
      step t0 t0' →
      step (tm_fst t0) (tm_fst t0')
  | ST_FstPair (v1 v2 : tm) :
      value v1 →
      value v2 →
      step (tm_fst (tm_pair v1 v2)) v1
  | ST_Snd1 (t0 t0' : tm) :
      step t0 t0' →
      step (tm_snd t0) (tm_snd t0')
  | ST_SndPair (v1 v2 : tm) :
      value v1 →
      value v2 →
      step (tm_snd (tm_pair v1 v2)) v2

def multistep : tm → tm → Prop := PLF.Smallstep.multi step

def step_normal_form (t : tm) : Prop :=
  PLF.Smallstep.normal_form step t

theorem value__normal (t : tm) :
    value t → step_normal_form t := by
  sorry

def context := partial_map ty

/-- 定型关系 -/
inductive has_type : context → tm → ty → Prop where
  | T_Var (Gamma : context) (x : String) (T1 : ty) :
      Gamma x = some T1 →
      has_type Gamma (tm_var x) T1
  | T_Abs (Gamma : context) (x : String) (T1 T2 : ty) (t1 : tm) :
      has_type (x |-> T2 ; Gamma) t1 T1 →
      has_type Gamma (tm_abs x T2 t1) (Ty_Arrow T2 T1)
  | T_App (T1 T2 : ty) (Gamma : context) (t1 t2 : tm) :
      has_type Gamma t1 (Ty_Arrow T2 T1) →
      has_type Gamma t2 T2 →
      has_type Gamma (tm_app t1 t2) T1
  | T_True (Gamma : context) :
      has_type Gamma tm_true Ty_Bool
  | T_False (Gamma : context) :
      has_type Gamma tm_false Ty_Bool
  | T_If (t1 t2 t3 : tm) (T1 : ty) (Gamma : context) :
      has_type Gamma t1 Ty_Bool →
      has_type Gamma t2 T1 →
      has_type Gamma t3 T1 →
      has_type Gamma (tm_if t1 t2 t3) T1
  | T_Pair (Gamma : context) (t1 t2 : tm) (T1 T2 : ty) :
      has_type Gamma t1 T1 →
      has_type Gamma t2 T2 →
      has_type Gamma (tm_pair t1 t2) (Ty_Prod T1 T2)
  | T_Fst (Gamma : context) (t0 : tm) (T1 T2 : ty) :
      has_type Gamma t0 (Ty_Prod T1 T2) →
      has_type Gamma (tm_fst t0) T1
  | T_Snd (Gamma : context) (t0 : tm) (T1 T2 : ty) :
      has_type Gamma t0 (Ty_Prod T1 T2) →
      has_type Gamma (tm_snd t0) T2

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

theorem preservation (t t' : tm) (T : ty) :
    has_type empty t T →
    step t t' →
    has_type empty t' T := by
  sorry

/-- 自由变量出现谓词 -/
inductive appears_free_in : String → tm → Prop where
  | afi_var (x : String) :
      appears_free_in x (tm_var x)
  | afi_app1 (x : String) (t1 t2 : tm) :
      appears_free_in x t1 → appears_free_in x (tm_app t1 t2)
  | afi_app2 (x : String) (t1 t2 : tm) :
      appears_free_in x t2 → appears_free_in x (tm_app t1 t2)
  | afi_abs (x y : String) (T11 : ty) (t12 : tm) :
      y ≠ x →
      appears_free_in x t12 →
      appears_free_in x (tm_abs y T11 t12)
  | afi_test0 (x : String) (t0 t1 t2 : tm) :
      appears_free_in x t0 →
      appears_free_in x (tm_if t0 t1 t2)
  | afi_test1 (x : String) (t0 t1 t2 : tm) :
      appears_free_in x t1 →
      appears_free_in x (tm_if t0 t1 t2)
  | afi_test2 (x : String) (t0 t1 t2 : tm) :
      appears_free_in x t2 →
      appears_free_in x (tm_if t0 t1 t2)
  | afi_pair1 (x : String) (t1 t2 : tm) :
      appears_free_in x t1 →
      appears_free_in x (tm_pair t1 t2)
  | afi_pair2 (x : String) (t1 t2 : tm) :
      appears_free_in x t2 →
      appears_free_in x (tm_pair t1 t2)
  | afi_fst (x : String) (t : tm) :
      appears_free_in x t →
      appears_free_in x (tm_fst t)
  | afi_snd (x : String) (t : tm) :
      appears_free_in x t →
      appears_free_in x (tm_snd t)

def closed (t : tm) : Prop :=
  ∀ x, ¬ appears_free_in x t

theorem context_invariance (Gamma Gamma' : context) (t : tm) (S : ty) :
    has_type Gamma t S →
    (∀ x, appears_free_in x t → Gamma x = Gamma' x) →
    has_type Gamma' t S := by
  sorry

theorem false_eqb_string (x y : String) :
    x ≠ y → (x == y) = false := by
  intro h
  simp [h]

theorem free_in_context (x : String) (t : tm) (T : ty) (Gamma : context) :
    appears_free_in x t →
    has_type Gamma t T →
    ∃ T', Gamma x = some T' := by
  sorry

theorem typable_empty__closed (t : tm) (T : ty) :
    has_type empty t T →
    closed t := by
  sorry

theorem step_deterministic :
    PLF.Smallstep.deterministic step := by
  sorry
```

## 2. 规范化与 Tait 逻辑关系 (Normalization and Tait's Method)

```lean
/-- 停机断言：项能够在多步归约后抵达某个良构的值 -/
def halts (t : tm) : Prop :=
  ∃ t', multistep t t' ∧ value t'

theorem value_halts (v : tm) :
    value v → halts v := by
  intro hv
  exact ⟨v, PLF.Smallstep.multi.multi_refl v, hv⟩

/--
逻辑关系家族 `R T t`（饱和集 / 可归约性候选）：
对类型结构进行递归定义的谓词。
- 基础布尔类型：要求项闭合良定且停机；
- 箭头类型：自身停机，且将任何满足参数类型饱和条件的项映射到满足返回类型饱和条件的项；
- 积类型：自身停机，且其左右投影均落在饱和集内。
-/
def R (T : ty) (t : tm) : Prop :=
  has_type empty t T ∧ halts t ∧
  match T with
  | Ty_Bool => True
  | Ty_Arrow T1 T2 => ∀ s, R T1 s → R T2 (tm_app t s)
  | Ty_Prod T1 T2 => R T1 (tm_fst t) ∧ R T2 (tm_snd t)

theorem R_halts {T : ty} {t : tm} :
    R T t → halts t := by
  intro h
  cases T with
  | Ty_Bool => exact h.2.1
  | Ty_Arrow T1 T2 => exact h.2.1
  | Ty_Prod T1 T2 => exact h.2.1

theorem R_typable_empty {T : ty} {t : tm} :
    R T t → has_type empty t T := by
  intro h
  cases T with
  | Ty_Bool => exact h.1
  | Ty_Arrow T1 T2 => exact h.1
  | Ty_Prod T1 T2 => exact h.1

theorem step_preserves_halting (t t' : tm) :
    step t t' → (halts t ↔ halts t') := by
  sorry

theorem step_preserves_R (T : ty) (t t' : tm) :
    step t t' → R T t → R T t' := by
  sorry

theorem multistep_preserves_R (T : ty) (t t' : tm) :
    multistep t t' → R T t → R T t' := by
  sorry

theorem step_preserves_R' (T : ty) (t t' : tm) :
    has_type empty t T → step t t' → R T t' → R T t := by
  sorry

theorem multistep_preserves_R' (T : ty) (t t' : tm) :
    has_type empty t T → multistep t t' → R T t' → R T t := by
  sorry
```

## 3. 多重代换与代换环境 (Multisubstitutions)

```lean
abbrev env : Type := List (String × tm)

/-- 多重代换：从右至左依次执行环境列表中的变量代换 -/
def msubst (ss : env) (t : tm) : tm :=
  match ss with
  | [] => t
  | (x, s) :: ss' => msubst ss' (subst x s t)

abbrev tass : Type := List (String × ty)

/-- 多重上下文扩展 -/
def mupdate (Gamma : context) (xts : tass) : context :=
  match xts with
  | [] => Gamma
  | (x, v) :: xts' => (x |-> v ; mupdate Gamma xts')

def lookup {X : Type} (k : String) (l : List (String × X)) : Option X :=
  match l with
  | [] => none
  | (j, x) :: l' =>
      if j = k then some x else lookup k l'

def drop {X : Type} (n : String) (nxs : List (String × X)) : List (String × X) :=
  match nxs with
  | [] => []
  | (n', x) :: nxs' =>
      if n' = n then drop n nxs'
      else (n', x) :: drop n nxs'

/-- 实例化关系：类型赋值表与闭项环境表在结构上对齐，且各对应分量均满足饱和集关系 `R` -/
inductive instantiation : tass → env → Prop where
  | V_nil : instantiation [] []
  | V_cons (x : String) (T : ty) (v : tm) (c : tass) (e : env) :
      value v → R T v → instantiation c e → instantiation ((x, T) :: c) ((x, v) :: e)

theorem vacuous_substitution (t : tm) (x : String) :
    ¬ appears_free_in x t → ∀ t', subst x t' t = t := by
  sorry

theorem subst_closed (t : tm) :
    closed t → ∀ x t', subst x t' t = t := by
  sorry

theorem subst_not_afi (t : tm) (x : String) (v : tm) :
    closed v → ¬ appears_free_in x (subst x v t) := by
  sorry

theorem duplicate_subst (t' : tm) (x : String) (t v : tm) :
    closed v → subst x t (subst x v t') = subst x v t' := by
  sorry

theorem swap_subst (t : tm) (x x1 : String) (v v1 : tm) :
    x ≠ x1 → closed v → closed v1 →
    subst x1 v1 (subst x v t) = subst x v (subst x1 v1 t) := by
  sorry

theorem msubst_closed (t : tm) :
    closed t → ∀ ss, msubst ss t = t := by
  sorry

def closed_env (e : env) : Prop :=
  match e with
  | [] => True
  | (_, t) :: e' => closed t ∧ closed_env e'

theorem subst_msubst (e : env) (x : String) (v t : tm) :
    closed v → closed_env e →
    msubst e (subst x v t) = subst x v (msubst (drop x e) t) := by
  sorry

theorem msubst_var (ss : env) (x : String) :
    closed_env ss →
    msubst ss (tm_var x) =
      match lookup x ss with
      | some t => t
      | none => tm_var x := by
  sorry

theorem msubst_abs (ss : env) (x : String) (T : ty) (t : tm) :
    msubst ss (tm_abs x T t) = tm_abs x T (msubst (drop x ss) t) := by
  sorry

theorem msubst_app (ss : env) (t1 t2 : tm) :
    msubst ss (tm_app t1 t2) = tm_app (msubst ss t1) (msubst ss t2) := by
  sorry

theorem mupdate_lookup (c : tass) (x : String) :
    lookup x c = (mupdate empty c) x := by
  sorry

theorem mupdate_drop (c : tass) (Gamma : context) (x x' : String) :
    mupdate Gamma (drop x c) x' =
      if x = x' then Gamma x' else mupdate Gamma c x' := by
  sorry

theorem instantiation_domains_match {c : tass} {e : env} :
    instantiation c e → ∀ {x T}, lookup x c = some T → ∃ t, lookup x e = some t := by
  sorry

theorem instantiation_env_closed (c : tass) (e : env) :
    instantiation c e → closed_env e := by
  sorry

theorem instantiation_R (c : tass) (e : env) :
    instantiation c e → ∀ x t T, lookup x c = some T → lookup x e = some t → R T t := by
  sorry

theorem instantiation_drop (c : tass) (e : env) :
    instantiation c e → ∀ x, instantiation (drop x c) (drop x e) := by
  sorry

theorem multistep_App2 (v t t' : tm) :
    value v → multistep t t' → multistep (tm_app v t) (tm_app v t') := by
  sorry

theorem msubst_preserves_typing (c : tass) (e : env) :
    instantiation c e →
    ∀ Gamma t S, has_type (mupdate Gamma c) t S → has_type Gamma (msubst e t) S := by
  sorry

/--
逻辑关系基本引理 (The Fundamental Lemma of Logical Relations)：
任何良类型项在代换实例化后必然属于饱和集 `R`。
-/
theorem msubst_R (c : tass) (e : env) (t : tm) (T : ty) :
    has_type (mupdate empty c) t T →
    instantiation c e →
    R T (msubst e t) := by
  sorry
```

## 4. 强规范化定理 (The Normalization Theorem)

```lean
/--
强规范化定理 (Normalization Theorem)：
每一个在空上下文中良类型的项必然在有限步内停机（归约到某个值）。
-/
theorem normalization (t : tm) (T : ty) :
    has_type empty t T → halts t := by
  intro h
  have hr : R T (msubst [] t) := by
    apply msubst_R [] [] t T
    · exact h
    · exact instantiation.V_nil
  dsimp [msubst] at hr
  exact R_halts hr

end PLF.Norm
```
