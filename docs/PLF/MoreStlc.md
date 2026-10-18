---
title: "MoreStlc: STLC 扩充：自然数、Let、积、和与递归定点"
---

```lean
import SFLean4.PLF.Maps
import SFLean4.PLF.Types
import SFLean4.PLF.Smallstep
import SFLean4.PLF.Stlc
```

# 软件基础 第二卷：程序语言基础 (PLF)

## 模块：简单类型 Lambda 演算的扩展 (MoreStlc: More on the Simply Typed Lambda-Calculus)

纯粹的 STLC 结构优雅且性质优美，但作为一门编程语言，它还缺少实际编程中不可或缺的构造。
在本章中，我们为 STLC 引入一系列现实编程语言的标准特性，并在类型论层面给出严谨的形式化处理：

1. **自然数类型（Numbers）**：`Nat`、常量 `n`、后继 `succ`、前驱 `pred`、乘法与零分支判定 `if0`；
2. **局部变量绑定（Let Bindings）**：`let x = t1 in t2`；
3. **积类型与数据对（Product Types & Pairs）**：`T1 * T2`、数据对构造 `(t1, t2)` 与投影 `t.fst`、`t.snd`；
4. **单位类型（Unit Type）**：`Unit` 与平凡值 `unit`；
5. **和类型 / 标签联合（Sum Types / Coproducts）**：`T1 + T2`、注入构造 `inl`、`inr` 与模式匹配 `case`；
6. **列表类型（List Types）**：`List T`、空列表 `nil`、头插 `cons` 与解构 `lcase`；
7. **通用递归与定点组合子（General Recursion & Fixpoint Combinator）**：`fix` 组合子。

所有这些扩展统一整合在 `STLCExtended` 命名空间中，并建立完整的进益定理与保型性定理。

```lean
namespace PLF.MoreStlc

open Maps
open PLF.Smallstep
```

**** 练习: 1 星, standard, optional (halve_fix)
思考如何利用 `fix` 实现自然数除以 2 的函数。

**** 练习: 1 星, standard, optional (fact_steps)
跟踪阶乘函数 `fact` 在小步语义下的规约过程。

## 扩展的形式化实现 (Formalizing the Extensions)

**** 练习: Formalizing the Extensions

```lean
namespace STLCExtended
```

### 1. 语法 (Syntax)

```lean
/-- 丰富后的类型集合 -/
inductive ty : Type where
  | Ty_Arrow : ty → ty → ty
  | Ty_Nat : ty
  | Ty_Sum : ty → ty → ty
  | Ty_List : ty → ty
  | Ty_Unit : ty
  | Ty_Prod : ty → ty → ty
  deriving Repr, DecidableEq

open ty

/-- 丰富后的项集合 -/
inductive tm : Type where
  -- 基础 STLC
  | tm_var : String → tm
  | tm_app : tm → tm → tm
  | tm_abs : String → ty → tm → tm
  -- 自然数
  | tm_const : Nat → tm
  | tm_succ : tm → tm
  | tm_pred : tm → tm
  | tm_mult : tm → tm → tm
  | tm_if0 : tm → tm → tm → tm
  -- 和类型
  | tm_inl : ty → tm → tm
  | tm_inr : ty → tm → tm
  | tm_case : tm → String → tm → String → tm → tm
  -- 列表
  | tm_nil : ty → tm
  | tm_cons : tm → tm → tm
  | tm_lcase : tm → tm → String → String → tm → tm
  -- 单位类型
  | tm_unit : tm
  -- 积类型 (Pairs)
  | tm_pair : tm → tm → tm
  | tm_fst : tm → tm
  | tm_snd : tm → tm
  -- Let 绑定
  | tm_let : String → tm → tm → tm
  -- 定点组合子
  | tm_fix : tm → tm
  deriving Repr, DecidableEq

open tm

def w : String := "w"
def x : String := "x"
def y : String := "y"
def z : String := "z"
```

### 2. 变量代换 (Substitution)

```lean
/--
**** 练习: 3 星, standard (STLCExtended.subst)
实现覆盖所有扩展语言特性的变量代换函数 `[x := s] t`。
-/
def subst (x : String) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if x = y then s else tm_var y
  | tm_abs y T t1 =>
      if x = y then tm_abs y T t1 else tm_abs y T (subst x s t1)
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
  | tm_inl T2 t1 =>
      tm_inl T2 (subst x s t1)
  | tm_inr T1 t2 =>
      tm_inr T1 (subst x s t2)
  | tm_case t0 y1 t1 y2 t2 =>
      tm_case (subst x s t0)
        y1 (if x = y1 then t1 else subst x s t1)
        y2 (if x = y2 then t2 else subst x s t2)
  | tm_nil T =>
      tm_nil T
  | tm_cons t1 t2 =>
      tm_cons (subst x s t1) (subst x s t2)
  | tm_lcase t1 t2 y1 y2 t3 =>
      tm_lcase (subst x s t1) (subst x s t2)
        y1 y2 (if x = y1 ∨ x = y2 then t3 else subst x s t3)
  | tm_unit =>
      tm_unit
  | tm_pair t1 t2 =>
      tm_pair (subst x s t1) (subst x s t2)
  | tm_fst t1 =>
      tm_fst (subst x s t1)
  | tm_snd t1 =>
      tm_snd (subst x s t1)
  | tm_let y t1 t2 =>
      tm_let y (subst x s t1) (if x = y then t2 else subst x s t2)
  | tm_fix t1 =>
      tm_fix (subst x s t1)

/-- 代换验证示例 1 -/
theorem substeg1 :
  subst z (tm_const 0) (tm_let w (tm_var z) (tm_var z)) =
  tm_let w (tm_const 0) (tm_const 0) := by
  rfl

/-- 代换验证示例 2 -/
theorem substeg2 :
  subst z (tm_const 0) (tm_let w (tm_var z) (tm_var w)) =
  tm_let w (tm_const 0) (tm_var w) := by
  rfl

/-- 代换验证示例 3 -/
theorem substeg3 :
  subst z (tm_const 0) (tm_let y (tm_succ (tm_const 0)) (tm_var z)) =
  tm_let y (tm_succ (tm_const 0)) (tm_const 0) := by
  rfl
```

### 3. 操作语义 (Operational Semantics)

```lean
/-- 扩展系统的值谓词 -/
inductive value : tm → Prop where
  | v_abs (x : String) (T : ty) (t : tm) : value (tm_abs x T t)
  | v_nat (n : Nat) : value (tm_const n)
  | v_inl (v : tm) (T : ty) : value v → value (tm_inl T v)
  | v_inr (v : tm) (T : ty) : value v → value (tm_inr T v)
  | v_lnil (T : ty) : value (tm_nil T)
  | v_lcons (v1 v2 : tm) : value v1 → value v2 → value (tm_cons v1 v2)
  | v_unit : value tm_unit
  | v_pair (v1 v2 : tm) : value v1 → value v2 → value (tm_pair v1 v2)

/--
**** 练习: 3 星, standard (STLCExtended.step)
扩展小步单步规约关系。
-/
inductive step : tm → tm → Prop where
  -- 基础 STLC
  | ST_AppAbs (x : String) (T2 : ty) (t1 : tm) (v2 : tm) :
      value v2 → step (tm_app (tm_abs x T2 t1) v2) (subst x v2 t1)
  | ST_App1 (t1 t1' t2 : tm) :
      step t1 t1' → step (tm_app t1 t2) (tm_app t1' t2)
  | ST_App2 (v1 t2 t2' : tm) :
      value v1 → step t2 t2' → step (tm_app v1 t2) (tm_app v1 t2')
  -- 自然数
  | ST_Succ (t1 t1' : tm) :
      step t1 t1' → step (tm_succ t1) (tm_succ t1')
  | ST_SuccNat (n : Nat) :
      step (tm_succ (tm_const n)) (tm_const (n + 1))
  | ST_Pred (t1 t1' : tm) :
      step t1 t1' → step (tm_pred t1) (tm_pred t1')
  | ST_PredNat (n : Nat) :
      step (tm_pred (tm_const n)) (tm_const (n - 1))
  | ST_Mulconsts (n1 n2 : Nat) :
      step (tm_mult (tm_const n1) (tm_const n2)) (tm_const (n1 * n2))
  | ST_Mult1 (t1 t1' t2 : tm) :
      step t1 t1' → step (tm_mult t1 t2) (tm_mult t1' t2)
  | ST_Mult2 (v1 t2 t2' : tm) :
      value v1 → step t2 t2' → step (tm_mult v1 t2) (tm_mult v1 t2')
  | ST_If0 (t1 t1' t2 t3 : tm) :
      step t1 t1' → step (tm_if0 t1 t2 t3) (tm_if0 t1' t2 t3)
  | ST_If0_Zero (t2 t3 : tm) :
      step (tm_if0 (tm_const 0) t2 t3) t2
  | ST_If0_Nonzero (n : Nat) (t2 t3 : tm) :
      step (tm_if0 (tm_const (n + 1)) t2 t3) t3
  -- 和类型
  | ST_Inl (t1 t1' : tm) (T2 : ty) :
      step t1 t1' → step (tm_inl T2 t1) (tm_inl T2 t1')
  | ST_Inr (t2 t2' : tm) (T1 : ty) :
      step t2 t2' → step (tm_inr T1 t2) (tm_inr T1 t2')
  | ST_Case (t0 t0' : tm) (x1 : String) (t1 : tm) (x2 : String) (t2 : tm) :
      step t0 t0' → step (tm_case t0 x1 t1 x2 t2) (tm_case t0' x1 t1 x2 t2)
  | ST_CaseInl (v0 : tm) (x1 : String) (t1 : tm) (x2 : String) (t2 : tm) (T2 : ty) :
      value v0 → step (tm_case (tm_inl T2 v0) x1 t1 x2 t2) (subst x1 v0 t1)
  | ST_CaseInr (v0 : tm) (x1 : String) (t1 : tm) (x2 : String) (t2 : tm) (T1 : ty) :
      value v0 → step (tm_case (tm_inr T1 v0) x1 t1 x2 t2) (subst x2 v0 t2)
  -- 列表
  | ST_Cons1 (t1 t1' t2 : tm) :
      step t1 t1' → step (tm_cons t1 t2) (tm_cons t1' t2)
  | ST_Cons2 (v1 t2 t2' : tm) :
      value v1 → step t2 t2' → step (tm_cons v1 t2) (tm_cons v1 t2')
  | ST_Lcase1 (t1 t1' t2 : tm) (x1 x2 : String) (t3 : tm) :
      step t1 t1' → step (tm_lcase t1 t2 x1 x2 t3) (tm_lcase t1' t2 x1 x2 t3)
  | ST_LcaseNil (T1 : ty) (t2 : tm) (x1 x2 : String) (t3 : tm) :
      step (tm_lcase (tm_nil T1) t2 x1 x2 t3) t2
  | ST_LcaseCons (v1 vl t2 : tm) (x1 x2 : String) (t3 : tm) :
      value v1 → value vl →
      step (tm_lcase (tm_cons v1 vl) t2 x1 x2 t3) (subst x2 vl (subst x1 v1 t3))
  -- 积类型 (Pairs)
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
  -- Let
  | ST_Let1 (x : String) (t1 t1' t2 : tm) :
      step t1 t1' → step (tm_let x t1 t2) (tm_let x t1' t2)
  | ST_LetValue (x : String) (v1 t2 : tm) :
      value v1 → step (tm_let x v1 t2) (subst x v1 t2)
  -- Fix
  | ST_Fix1 (t1 t1' : tm) :
      step t1 t1' → step (tm_fix t1) (tm_fix t1')
  | ST_FixAbs (x : String) (T : ty) (t12 : tm) :
      step (tm_fix (tm_abs x T t12)) (subst x (tm_fix (tm_abs x T t12)) t12)

def multistep : tm → tm → Prop := PLF.Smallstep.multi step
```

### 4. 定型规则 (Typing Rules)

```lean
def context : Type := partial_map ty

/--
**** 练习: 3 stars, standard (STLCExtended.has_type)
扩展定型关系。
-/
inductive has_type : context → tm → ty → Prop where
  -- 基础 STLC
  | T_Var (Gamma : context) (x : String) (T1 : ty) :
      Gamma x = some T1 → has_type Gamma (tm_var x) T1
  | T_Abs (Gamma : context) (x : String) (T1 T2 : ty) (t1 : tm) :
      has_type (x |-> T2 ; Gamma) t1 T1 → has_type Gamma (tm_abs x T2 t1) (Ty_Arrow T2 T1)
  | T_App (T1 T2 : ty) (Gamma : context) (t1 t2 : tm) :
      has_type Gamma t1 (Ty_Arrow T2 T1) → has_type Gamma t2 T2 → has_type Gamma (tm_app t1 t2) T1
  -- 自然数
  | T_Nat (Gamma : context) (n : Nat) :
      has_type Gamma (tm_const n) Ty_Nat
  | T_Succ (Gamma : context) (t : tm) :
      has_type Gamma t Ty_Nat → has_type Gamma (tm_succ t) Ty_Nat
  | T_Pred (Gamma : context) (t : tm) :
      has_type Gamma t Ty_Nat → has_type Gamma (tm_pred t) Ty_Nat
  | T_Mult (Gamma : context) (t1 t2 : tm) :
      has_type Gamma t1 Ty_Nat → has_type Gamma t2 Ty_Nat → has_type Gamma (tm_mult t1 t2) Ty_Nat
  | T_If0 (Gamma : context) (t1 t2 t3 : tm) (T0 : ty) :
      has_type Gamma t1 Ty_Nat → has_type Gamma t2 T0 → has_type Gamma t3 T0 → has_type Gamma (tm_if0 t1 t2 t3) T0
  -- 和类型
  | T_Inl (Gamma : context) (t1 : tm) (T1 T2 : ty) :
      has_type Gamma t1 T1 → has_type Gamma (tm_inl T2 t1) (Ty_Sum T1 T2)
  | T_Inr (Gamma : context) (t2 : tm) (T1 T2 : ty) :
      has_type Gamma t2 T2 → has_type Gamma (tm_inr T1 t2) (Ty_Sum T1 T2)
  | T_Case (Gamma : context) (t0 : tm) (x1 : String) (t1 : tm) (x2 : String) (t2 : tm) (T1 T2 T3 : ty) :
      has_type Gamma t0 (Ty_Sum T1 T2) →
      has_type (x1 |-> T1 ; Gamma) t1 T3 →
      has_type (x2 |-> T2 ; Gamma) t2 T3 →
      has_type Gamma (tm_case t0 x1 t1 x2 t2) T3
  -- 列表
  | T_Nil (Gamma : context) (T1 : ty) :
      has_type Gamma (tm_nil T1) (Ty_List T1)
  | T_Cons (Gamma : context) (t1 t2 : tm) (T1 : ty) :
      has_type Gamma t1 T1 → has_type Gamma t2 (Ty_List T1) → has_type Gamma (tm_cons t1 t2) (Ty_List T1)
  | T_Lcase (Gamma : context) (t1 : tm) (T1 : ty) (t2 : tm) (x1 x2 : String) (t3 : tm) (T2 : ty) :
      has_type Gamma t1 (Ty_List T1) →
      has_type Gamma t2 T2 →
      has_type (x1 |-> T1 ; x2 |-> Ty_List T1 ; Gamma) t3 T2 →
      has_type Gamma (tm_lcase t1 t2 x1 x2 t3) T2
  -- 单位类型
  | T_Unit (Gamma : context) :
      has_type Gamma tm_unit Ty_Unit
  -- 积类型
  | T_Pair (Gamma : context) (t1 t2 : tm) (T1 T2 : ty) :
      has_type Gamma t1 T1 → has_type Gamma t2 T2 → has_type Gamma (tm_pair t1 t2) (Ty_Prod T1 T2)
  | T_Fst (Gamma : context) (t : tm) (T1 T2 : ty) :
      has_type Gamma t (Ty_Prod T1 T2) → has_type Gamma (tm_fst t) T1
  | T_Snd (Gamma : context) (t : tm) (T1 T2 : ty) :
      has_type Gamma t (Ty_Prod T1 T2) → has_type Gamma (tm_snd t) T2
  -- Let
  | T_Let (Gamma : context) (x : String) (t1 t2 : tm) (T1 T2 : ty) :
      has_type Gamma t1 T1 → has_type (x |-> T1 ; Gamma) t2 T2 → has_type Gamma (tm_let x t1 t2) T2
  -- Fix
  | T_Fix (Gamma : context) (t : tm) (T : ty) :
      has_type Gamma t (Ty_Arrow T T) → has_type Gamma (tm_fix t) T
```

### 5. 示例测试套件 (Examples)

**** 练习: 5 星, standard, optional (STLCExtended_examples)

```lean
namespace Examples

namespace Numtest
def tm_test : tm :=
  tm_if0 (tm_pred (tm_succ (tm_pred (tm_mult (tm_const 2) (tm_const 0))))) (tm_const 5) (tm_const 6)

theorem typechecks : has_type empty tm_test Ty_Nat := by sorry
theorem reduces : multistep tm_test (tm_const 5) := by sorry
end Numtest

namespace ProdTest
def tm_test : tm :=
  tm_snd (tm_fst (tm_pair (tm_pair (tm_const 5) (tm_const 6)) (tm_const 7)))

theorem typechecks : has_type empty tm_test Ty_Nat := by sorry
theorem reduces : multistep tm_test (tm_const 6) := by sorry
end ProdTest

namespace LetTest
def tm_test : tm :=
  tm_let "x" (tm_pred (tm_const 6)) (tm_succ (tm_var "x"))

theorem typechecks : has_type empty tm_test Ty_Nat := by sorry
theorem reduces : multistep tm_test (tm_const 6) := by sorry
end LetTest

namespace LetTest1
def tm_test : tm :=
  tm_let "z" (tm_pred (tm_const 6)) (tm_succ (tm_var "z"))

theorem typechecks : has_type empty tm_test Ty_Nat := by sorry
theorem reduces : multistep tm_test (tm_const 6) := by sorry
end LetTest1

namespace Sumtest1
def tm_test : tm :=
  tm_case (tm_inl Ty_Nat (tm_const 5)) "x" (tm_var "x") "y" (tm_var "y")

theorem typechecks : has_type empty tm_test Ty_Nat := by sorry
theorem reduces : multistep tm_test (tm_const 5) := by sorry
end Sumtest1

namespace Sumtest2
def tm_test : tm :=
  tm_let "processSum"
    (tm_abs "x" (Ty_Sum Ty_Nat Ty_Nat)
      (tm_case (tm_var "x") "n" (tm_var "n") "n" (tm_if0 (tm_var "n") (tm_const 1) (tm_const 0))))
    (tm_pair (tm_app (tm_var "processSum") (tm_inl Ty_Nat (tm_const 5)))
             (tm_app (tm_var "processSum") (tm_inr Ty_Nat (tm_const 5))))

theorem typechecks : has_type empty tm_test (Ty_Prod Ty_Nat Ty_Nat) := by sorry
theorem reduces : multistep tm_test (tm_pair (tm_const 5) (tm_const 0)) := by sorry
end Sumtest2

namespace ListTest
def tm_test : tm :=
  tm_let "l" (tm_cons (tm_const 5) (tm_cons (tm_const 6) (tm_nil Ty_Nat)))
    (tm_lcase (tm_var "l") (tm_const 0) "x" "y" (tm_mult (tm_var "x") (tm_var "x")))

theorem typechecks : has_type empty tm_test Ty_Nat := by sorry
theorem reduces : multistep tm_test (tm_const 25) := by sorry
end ListTest

namespace FixTest1
def fact : tm :=
  tm_fix
    (tm_abs "f" (Ty_Arrow Ty_Nat Ty_Nat)
      (tm_abs "a" Ty_Nat
        (tm_if0 (tm_var "a") (tm_const 1)
          (tm_mult (tm_var "a") (tm_app (tm_var "f") (tm_pred (tm_var "a")))))))

theorem typechecks : has_type empty fact (Ty_Arrow Ty_Nat Ty_Nat) := by sorry
theorem reduces : multistep (tm_app fact (tm_const 4)) (tm_const 24) := by sorry
end FixTest1

namespace FixTest2
def map : tm :=
  tm_abs "g" (Ty_Arrow Ty_Nat Ty_Nat)
    (tm_fix
      (tm_abs "f" (Ty_Arrow (Ty_List Ty_Nat) (Ty_List Ty_Nat))
        (tm_abs "l" (Ty_List Ty_Nat)
          (tm_lcase (tm_var "l") (tm_nil Ty_Nat) "x" "l"
            (tm_cons (tm_app (tm_var "g") (tm_var "x")) (tm_app (tm_var "f") (tm_var "l")))))))

theorem typechecks : has_type empty map (Ty_Arrow (Ty_Arrow Ty_Nat Ty_Nat) (Ty_Arrow (Ty_List Ty_Nat) (Ty_List Ty_Nat))) := by sorry
theorem reduces : multistep (tm_app (tm_app map (tm_abs "a" Ty_Nat (tm_succ (tm_var "a"))))
  (tm_cons (tm_const 1) (tm_cons (tm_const 2) (tm_nil Ty_Nat))))
  (tm_cons (tm_const 2) (tm_cons (tm_const 3) (tm_nil Ty_Nat))) := by sorry
end FixTest2

namespace FixTest3
def equal : tm :=
  tm_fix
    (tm_abs "eq" (Ty_Arrow Ty_Nat (Ty_Arrow Ty_Nat Ty_Nat))
      (tm_abs "m" Ty_Nat
        (tm_abs "n" Ty_Nat
          (tm_if0 (tm_var "m")
            (tm_if0 (tm_var "n") (tm_const 1) (tm_const 0))
            (tm_if0 (tm_var "n")
              (tm_const 0)
              (tm_app (tm_app (tm_var "eq") (tm_pred (tm_var "m"))) (tm_pred (tm_var "n"))))))))

theorem typechecks : has_type empty equal (Ty_Arrow Ty_Nat (Ty_Arrow Ty_Nat Ty_Nat)) := by sorry
theorem reduces : multistep (tm_app (tm_app equal (tm_const 4)) (tm_const 4)) (tm_const 1) := by sorry
theorem reduces2 : multistep (tm_app (tm_app equal (tm_const 4)) (tm_const 5)) (tm_const 0) := by sorry
end FixTest3

namespace FixTest4
def eotest : tm :=
  tm_let "evenodd"
    (tm_fix
      (tm_abs "eo" (Ty_Prod (Ty_Arrow Ty_Nat Ty_Nat) (Ty_Arrow Ty_Nat Ty_Nat))
        (tm_pair
          (tm_abs "n" Ty_Nat (tm_if0 (tm_var "n") (tm_const 1) (tm_app (tm_snd (tm_var "eo")) (tm_pred (tm_var "n")))))
          (tm_abs "n" Ty_Nat (tm_if0 (tm_var "n") (tm_const 0) (tm_app (tm_fst (tm_var "eo")) (tm_pred (tm_var "n"))))))))
    (tm_let "even" (tm_fst (tm_var "evenodd"))
      (tm_let "odd" (tm_snd (tm_var "evenodd"))
        (tm_pair (tm_app (tm_var "even") (tm_const 3)) (tm_app (tm_var "even") (tm_const 4)))))

theorem typechecks : has_type empty eotest (Ty_Prod Ty_Nat Ty_Nat) := by sorry
theorem reduces : multistep eotest (tm_pair (tm_const 0) (tm_const 1)) := by sorry
end FixTest4

end Examples
```

### 6. 元理论性质 (Metatheoretic Properties)

```lean
/--
**** 练习: 3 星, standard (STLCExtended.progress)
扩展系统的进益定理。
-/
theorem progress (t : tm) (T : ty) :
  has_type empty t T →
  value t ∨ ∃ t', step t t' := by
  sorry

/-- 弱化引理 -/
theorem weakening (Gamma Gamma' : context) (t : tm) (T : ty) :
  includedin Gamma Gamma' →
  has_type Gamma t T →
  has_type Gamma' t T := by
  sorry

/-- 弱化引理空上下文特例 -/
theorem weakening_empty (Gamma : context) (t : tm) (T : ty) :
  has_type empty t T →
  has_type Gamma t T := by
  intro H
  apply weakening empty Gamma t T _ H
  intro x v Hx
  cases Hx

/--
**** 练习: 2 星, standard (STLCExtended.substitution_preserves_typing)
扩展系统的代换保型引理。
-/
theorem substitution_preserves_typing (Gamma : context) (x : String) (U : ty) (t v : tm) (T : ty) :
  has_type (x |-> U ; Gamma) t T →
  has_type empty v U →
  has_type Gamma (subst x v t) T := by
  sorry

/--
**** 练习: 3 星, standard (STLCExtended.preservation)
扩展系统的保型性定理。
-/
theorem preservation (t t' : tm) (T : ty) :
  has_type empty t T →
  step t t' →
  has_type empty t' T := by
  sorry

end STLCExtended

end PLF.MoreStlc
```
