---
title: "Records: 记录类型系统：字段投影与类型安全"
---

```lean
import SFLean4.PLF.Maps
import SFLean4.PLF.Smallstep
import SFLean4.PLF.Stlc

open Maps

namespace PLF.Records
```

# 记录类型：为简单类型 Lambda 演算添加记录 (Records: Adding Records to STLC)

在 `MoreStlc` 章节中，我们曾通过积类型的嵌套语法糖来非正式地引入记录类型。
然而，那种编码方式在语法分析和类型检查错误提示方面存在诸多局限。
本章将记录类型提升为语言中的**一等公民 (First-Class Citizens)**：
包含字段投影 `t.i`、字段记录值 `{i1=v1, ..., in=vn}` 以及记录类型 `{i1:T1, ..., in:Tn}`。

同时，为了在形式化系统中获得自然的结构归纳法则，我们将记录表示为类似列表的归纳构造：
由空记录 `RNil` 与字段追加构造子 `RCons` 组成，并建立良构性断言 `well_formed_ty`。

```lean
namespace STLCExtendedRecords

/- ################################################################# -/
```

## 1. 语法与操作语义 (Syntax and Operational Semantics)

```lean
/- ################################################################# -/

namespace FirstTry

/-- 关联列表别名 -/
def alist (X : Type) := List (String × X)

/-- 初步尝试：使用内建 List 定义记录类型（演示 Coq 与证明助手中的局限） -/
inductive ty : Type where
  | Base : String → ty
  | Arrow : ty → ty → ty
  | TRcd : List (String × ty) → ty

end FirstTry

/--
记录类型的归纳定义：
- `Ty_Base`: 基础类型
- `Ty_Arrow`: 函数箭头类型
- `Ty_RNil`: 空记录类型
- `Ty_RCons`: 头部字段类型追加
-/
inductive ty : Type where
  | Ty_Base : String → ty
  | Ty_Arrow : ty → ty → ty
  | Ty_RNil : ty
  | Ty_RCons : String → ty → ty → ty
  deriving Repr, DecidableEq

open ty

/--
记录项的归纳定义：
- 基础 STLC 项：变量、函数应用、抽象
- 记录专用项：字段投影 `tm_rproj`、空记录 `tm_rnil`、字段记录项 `tm_rcons`
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

def A : ty := Ty_Base "A"
def B : ty := Ty_Base "B"
```

### 良构性 (Well-Formedness)

```lean
/-- 非良构类型示例：尾部不是合法的记录类型 -/
def weird_type : ty := Ty_RCons "a" A B

/-- 判定一个类型在最外层是否具有记录构造形式 -/
inductive record_ty : ty → Prop where
  | RTnil : record_ty Ty_RNil
  | RTcons (i : String) (T1 T2 : ty) : record_ty (Ty_RCons i T1 T2)

/--
良构类型断言：
排除类似于 `weird_type` 的非法类型，确保记录尾部始终为合法记录。
-/
inductive well_formed_ty : ty → Prop where
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

theorem wf_ty_example :
    well_formed_ty (Ty_RCons "i1" (Ty_Arrow A A) (Ty_RCons "i2" (Ty_Arrow B B) Ty_RNil)) := by
  repeat constructor

/-- 判定项在最外层是否由空记录或字段追加构造 -/
inductive record_tm : tm → Prop where
  | rtnil : record_tm tm_rnil
  | rtcons (i : String) (t1 t2 : tm) : record_tm (tm_rcons i t1 t2)
```

### 变量代换 (Substitution)

```lean
/-- 拓展到记录语法的无捕获变量代换函数 `[x := s] t` -/
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
```

### 归约语义 (Reduction)

```lean
/-- 值断言：当且仅当所有字段项均为值时，记录项为值 -/
inductive value : tm → Prop where
  | v_abs (x : String) (T2 : ty) (t1 : tm) :
      value (tm_abs x T2 t1)
  | v_rnil : value tm_rnil
  | v_rcons (i : String) (v1 vr : tm) :
      value v1 →
      value vr →
      value (tm_rcons i v1 vr)

/-- 项级字段查找函数 -/
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

def multistep : tm → tm → Prop := PLF.Smallstep.multi step

/- ################################################################# -/
```

## 2. 定型规则 (Typing)

```lean
/- ################################################################# -/

/-- 类型级字段类型查找函数 -/
def Tlookup (i : String) (Tr : ty) : Option ty :=
  match Tr with
  | Ty_RCons i' T Tr' =>
      if i = i' then some T else Tlookup i Tr'
  | _ => none

def context := partial_map ty

/-- 带记录的简单类型系统定型关系 -/
inductive has_type : context → tm → ty → Prop where
  | T_Var (Gamma : context) (x : String) (T : ty) :
      Gamma x = some T →
      well_formed_ty T →
      has_type Gamma (tm_var x) T
  | T_Abs (Gamma : context) (x : String) (T11 T12 : ty) (t12 : tm) :
      well_formed_ty T11 →
      has_type (x |-> T11 ; Gamma) t12 T12 →
      has_type Gamma (tm_abs x T11 t12) (Ty_Arrow T11 T12)
  | T_App (Gamma : context) (T1 T2 : ty) (t1 t2 : tm) :
      has_type Gamma t1 (Ty_Arrow T1 T2) →
      has_type Gamma t2 T1 →
      has_type Gamma (tm_app t1 t2) T2
  | T_Proj (Gamma : context) (i : String) (t : tm) (Ti Tr : ty) :
      has_type Gamma t Tr →
      Tlookup i Tr = some Ti →
      has_type Gamma (tm_rproj t i) Ti
  | T_RNil (Gamma : context) :
      has_type Gamma tm_rnil Ty_RNil
  | T_RCons (Gamma : context) (i : String) (t : tm) (T : ty) (tr : tm) (Tr : ty) :
      has_type Gamma t T →
      has_type Gamma tr Tr →
      record_ty Tr →
      record_tm tr →
      has_type Gamma (tm_rcons i t tr) (Ty_RCons i T Tr)

/- ################################################################# -/
```

## 3. 示例与反例验证 (Examples)

```lean
/- ################################################################# -/
```

**** 练习: 2 星, standard (examples)
验证记录定型与投影求值规则的正面用例与非法反例。

```lean
theorem typing_example_2 :
    has_type empty
      (tm_app
        (tm_abs "a" (Ty_RCons "i1" (Ty_Arrow A A) (Ty_RCons "i2" (Ty_Arrow B B) Ty_RNil))
          (tm_rproj (tm_var "a") "i2"))
        (tm_rcons "i1" (tm_abs "a" A (tm_var "a"))
          (tm_rcons "i2" (tm_abs "a" B (tm_var "a")) tm_rnil)))
      (Ty_Arrow B B) := by
  sorry

theorem typing_nonexample :
    ¬ ∃ T, has_type ("a" |-> Ty_RCons "i2" (Ty_Arrow A A) Ty_RNil)
             (tm_rcons "i1" (tm_abs "a" B (tm_var "a")) (tm_var "a")) T := by
  sorry

theorem typing_nonexample_2 (y : String) :
    ¬ ∃ T, has_type (y |-> A)
             (tm_app
               (tm_abs "a" (Ty_RCons "i1" A Ty_RNil) (tm_rproj (tm_var "a") "i1"))
               (tm_rcons "i1" (tm_var y) (tm_rcons "i2" (tm_var y) tm_rnil))) T := by
  sorry

/- ################################################################# -/
```

## 4. 定型性质验证 (Properties of Typing)

```lean
/- ################################################################# -/

/-- 良构记录类型的字段查找必得良构类型 -/
theorem wf_rcd_lookup (i : String) (T Ti : ty) :
    well_formed_ty T →
    Tlookup i T = some Ti →
    well_formed_ty Ti := by
  sorry

/-- 单步归约保持项的记录结构形式 -/
theorem step_preserves_record_tm (tr tr' : tm) :
    record_tm tr →
    step tr tr' →
    record_tm tr' := by
  sorry

/-- 良类型项必然具有良构类型 -/
theorem has_type__wf (Gamma : context) (t : tm) (T : ty) :
    has_type Gamma t T → well_formed_ty T := by
  sorry

/-- 值字段提取引理 -/
theorem lookup_field_in_value (v : tm) (T : ty) (i : String) (Ti : ty) :
    value v →
    has_type empty v T →
    Tlookup i T = some Ti →
    ∃ ti, tlookup i v = some ti ∧ has_type empty ti Ti := by
  sorry

/-- 进益定理 (Progress) -/
theorem progress (t : tm) (T : ty) :
    has_type empty t T →
    value t ∨ ∃ t', step t t' := by
  sorry

/-- 弱化引理 (Weakening) -/
theorem weakening (Gamma Gamma' : context) (t : tm) (T : ty) :
    includedin Gamma Gamma' →
    has_type Gamma t T →
    has_type Gamma' t T := by
  sorry

theorem weakening_empty (Gamma : context) (t : tm) (T : ty) :
    has_type empty t T →
    has_type Gamma t T := by
  sorry

/-- 代换保型引理 (Substitution Preserves Typing) -/
theorem substitution_preserves_typing (Gamma : context) (x : String) (U : ty) (t v : tm) (T : ty) :
    has_type (x |-> U ; Gamma) t T →
    has_type empty v U →
    has_type Gamma (subst x v t) T := by
  sorry

/-- 保型性定理 (Preservation) -/
theorem preservation (t t' : tm) (T : ty) :
    has_type empty t T →
    step t t' →
    has_type empty t' T := by
  sorry

end STLCExtendedRecords

end PLF.Records
```
