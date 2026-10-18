import SFLean4.PLF.Maps
import SFLean4.PLF.Smallstep

/-!
# 软件基础 第二卷：程序语言基础 (PLF)

## 模块：简单类型 Lambda 演算 (Stlc)

**简单类型 Lambda 演算（Simply Typed Lambda-Calculus, STLC）**是一个体现**函数抽象（Functional Abstraction）**
核心思想的微型演算。这一概念以各种形式（函数、过程、方法等）出现在几乎所有现代现实世界编程语言中。

STLC 位于著名的 **Lambda 立方体（Barendregt Cube）** 的左下前角：
- 从底向上：引入**多态类型（Polymorphism）**（如 System F）
- 从前向后：引入**类型构造子（Type Operators）**
- 从左向右：引入**依赖类型（Dependent Types）**（如 Lean 4 与 Rocq 所基于的构造演算 CoC）

本章我们将沿用上一章的经典模式形式化 STLC：
1. **语法（Syntax）**与项结构
2. **操作语义（Operational Semantics）**：值、变量代换（Substitution）与单步规约
3. **定型关系（Typing Relation）**：类型上下文（Contexts）与定型推导
-/

namespace PLF.Stlc

open Maps
open PLF.Smallstep

namespace STLC

/-!
## 1. 语法 (Syntax)

STLC 建立在一组基础类型之上。为保持精简，本章基础类型仅包含布尔类型 `Bool`。
由此扩展出两类构件：
- 基础布尔常量与条件分支
- 函数抽象（$\lambda$-抽象）、变量与函数应用（Application）
-/

/-- STLC 的类型：
- `Ty_Bool`: 布尔基础类型 `Bool`
- `Ty_Arrow S T`: 函数类型 `S -> T`
-/
inductive ty : Type where
  | Ty_Bool : ty
  | Ty_Arrow : ty → ty → ty
  deriving Repr, DecidableEq

open ty

/-- STLC 的项（Terms）：
- `tm_var x`: 变量 `x`
- `tm_app t1 t2`: 函数应用 `t1 t2`
- `tm_abs x T t`: 函数抽象 `\x:T, t`
- `tm_true`: 布尔真 `true`
- `tm_false`: 布尔假 `false`
- `tm_if t1 t2 t3`: 条件分支 `if t1 then t2 else t3`
-/
inductive tm : Type where
  | tm_var : String → tm
  | tm_app : tm → tm → tm
  | tm_abs : String → ty → tm → tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm → tm → tm → tm
  deriving Repr, DecidableEq

open tm

/-- 常用变量名常量定义 -/
def x : String := "x"
def y : String := "y"
def z : String := "z"

/--
常用组合子与函数项缩写：
- `idB`: 布尔恒等函数 `\x:Bool, x`
- `idBB`: 一阶布尔函数恒等函数 `\x:Bool->Bool, x`
- `idBBBB`: 高阶恒等函数
- `k`: 二元常量组合子 `\x:Bool, \y:Bool, x`
- `notB`: 布尔取反函数 `\x:Bool, if x then false else true`
-/
def idB : tm := tm_abs x Ty_Bool (tm_var x)
def idBB : tm := tm_abs x (Ty_Arrow Ty_Bool Ty_Bool) (tm_var x)
def idBBBB : tm :=
  tm_abs x (Ty_Arrow (Ty_Arrow Ty_Bool Ty_Bool) (Ty_Arrow Ty_Bool Ty_Bool)) (tm_var x)
def k : tm := tm_abs x Ty_Bool (tm_abs y Ty_Bool (tm_var x))
def notB : tm := tm_abs x Ty_Bool (tm_if (tm_var x) tm_false tm_true)

/-!
## 2. 操作语义 (Operational Semantics)

### 值 (Values)
在 STLC 中：
1. 布尔常量 `true` 和 `false` 是值；
2. 函数抽象 `\x:T, t` 是值（我们采用多数函数式语言的**传值调用（Call-by-Value）**策略，不进入抽象内部归约）；
3. 应用 `t1 t2` 和条件分支不是值。
-/

inductive value : tm → Prop where
  | v_abs (x : String) (T : ty) (t : tm) :
      value (tm_abs x T t)
  | v_true :
      value tm_true
  | v_false :
      value tm_false

/-!
### 变量代换 (Substitution)

代换操作 `[x := s] t`：将项 `t` 中所有自由出现的变量 `x` 替换为项 `s`。
注意：当遇到抽象 `\y:T, t1` 时：
- 若 `x = y`，由于局部绑定发生变量遮蔽（Shadowing），代换终止，保持 `\y:T, t1` 不变；
- 若 `x ≠ y`，则递归进入函数体代换。
-/

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

/--
代换关系（归纳谓词形式）：`substi s x t t'` 表示将项 `t` 中的自由变量 `x` 替换为 `s` 得到 `t'`。
-/
inductive substi (s : tm) (x : String) : tm → tm → Prop where
  | s_var1 :
      substi s x (tm_var x) s
  | s_var2 (y : String) :
      y ≠ x →
      substi s x (tm_var y) (tm_var y)
  | s_app (t1 t2 t1' t2' : tm) :
      substi s x t1 t1' →
      substi s x t2 t2' →
      substi s x (tm_app t1 t2) (tm_app t1' t2')
  | s_abs1 (T : ty) (t : tm) :
      substi s x (tm_abs x T t) (tm_abs x T t)
  | s_abs2 (y : String) (T : ty) (t t' : tm) :
      y ≠ x →
      substi s x t t' →
      substi s x (tm_abs y T t) (tm_abs y T t')
  | s_true :
      substi s x tm_true tm_true
  | s_false :
      substi s x tm_false tm_false
  | s_if (t t1 t2 t' t1' t2' : tm) :
      substi s x t t' →
      substi s x t1 t1' →
      substi s x t2 t2' →
      substi s x (tm_if t t1 t2) (tm_if t' t1' t2')

/--
**** 练习: 3 星, standard (substi_correct)
证明代换函数与代换归纳谓词完全等价。
-/
theorem substi_correct (s : tm) (x : String) (t t' : tm) :
  subst x s t = t' ↔ substi s x t t' := by
  sorry

/-!
### 小步单步归约 (Reduction)

STLC 传值单步求值规则：
```text
                               value v
                        -----------------------                      (ST_AppAbs)
                        (\x:T,t) v --> [x:=v]t

                               t1 --> t1'
                            ----------------                           (ST_App1)
                            t1 t2 --> t1' t2

                               value v1
                               t2 --> t2'
                            ----------------                           (ST_App2)
                            v1 t2 --> v1 t2'

                     --------------------------------               (ST_IfTrue)
                     (if true then t1 else t2) --> t1

                     ---------------------------------              (ST_IfFalse)
                     (if false then t1 else t2) --> t2

                              t1 --> t1'
       --------------------------------------------------------     (ST_If)
       (if t1 then t2 else t3) --> (if t1' then t2 else t3)
```
-/

inductive step : tm → tm → Prop where
  | ST_AppAbs (x : String) (T : ty) (t : tm) (v : tm) :
      value v →
      step (tm_app (tm_abs x T t) v) (subst x v t)
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

scoped notation:40 t " --> " t' => step t t'

def multistep : tm → tm → Prop := multi step
scoped notation:40 t1 " -->* " t2 => multistep t1 t2

/-!
### 归约示例
-/

theorem step_example1 :
  multistep (tm_app idBB idB) idB := by
  apply multi.multi_step _ (subst x idB (tm_var x))
  · apply step.ST_AppAbs
    exact value.v_abs x Ty_Bool (tm_var x)
  · exact multi.multi_refl _

theorem step_example2 :
  multistep (tm_app idBB (tm_app idBB idB)) idB := by
  apply multi.multi_step _ (tm_app idBB idB)
  · apply step.ST_App2
    · exact value.v_abs x (Ty_Arrow Ty_Bool Ty_Bool) (tm_var x)
    · apply step.ST_AppAbs
      exact value.v_abs x Ty_Bool (tm_var x)
  · apply multi.multi_step _ idB
    · apply step.ST_AppAbs
      exact value.v_abs x Ty_Bool (tm_var x)
    · apply multi.multi_refl

theorem step_example3 :
  multistep (tm_app (tm_app idBB notB) tm_true) tm_false := by
  apply multi.multi_step _ (tm_app notB tm_true)
  · apply step.ST_App1
    apply step.ST_AppAbs
    exact value.v_abs x Ty_Bool (tm_if (tm_var x) tm_false tm_true)
  · apply multi.multi_step _ (tm_if tm_true tm_false tm_true)
    · apply step.ST_AppAbs
      exact value.v_true
    · apply multi.multi_step _ tm_false
      · exact step.ST_IfTrue tm_false tm_true
      · apply multi.multi_refl

theorem step_example4 :
  multistep (tm_app idBB (tm_app notB tm_true)) tm_false := by
  apply multi.multi_step _ (tm_app idBB (tm_if tm_true tm_false tm_true))
  · apply step.ST_App2
    · exact value.v_abs x (Ty_Arrow Ty_Bool Ty_Bool) (tm_var x)
    · apply step.ST_AppAbs
      exact value.v_true
  · apply multi.multi_step _ (tm_app idBB tm_false)
    · apply step.ST_App2
      · exact value.v_abs x (Ty_Arrow Ty_Bool Ty_Bool) (tm_var x)
      · exact step.ST_IfTrue tm_false tm_true
    · apply multi.multi_step _ tm_false
      · apply step.ST_AppAbs
        exact value.v_false
      · apply multi.multi_refl

theorem step_example1' : multistep (tm_app idBB idB) idB := step_example1
theorem step_example2' : multistep (tm_app idBB (tm_app idBB idB)) idB := step_example2
theorem step_example3' : multistep (tm_app (tm_app idBB notB) tm_true) tm_false := step_example3
theorem step_example4' : multistep (tm_app idBB (tm_app notB tm_true)) tm_false := step_example4

/--
**** 练习: 2 星, standard (step_example5)
证明 `idBBBB idBB idB -->* idB`。
-/
theorem step_example5 :
  multistep (tm_app (tm_app idBBBB idBB) idB) idB := by
  sorry

theorem step_example5_with_normalize :
  multistep (tm_app (tm_app idBBBB idBB) idB) idB := by
  sorry

/-!
## 3. 定型关系 (Typing Relation)

定型上下文（Context）是变量到类型的偏映射：`context := partial_map ty`。
三元定型关系 `has_type Gamma t T` 表示在上下文 `Gamma` 下项 `t` 具有类型 `T`。
-/

def context : Type := partial_map ty

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

/-- 示例 1：布尔恒等函数定型 -/
theorem typing_example_1 :
  has_type empty (tm_abs x Ty_Bool (tm_var x)) (Ty_Arrow Ty_Bool Ty_Bool) := by
  apply has_type.T_Abs
  apply has_type.T_Var
  exact update_eq ty empty x Ty_Bool

theorem typing_example_1' :
  has_type empty (tm_abs x Ty_Bool (tm_var x)) (Ty_Arrow Ty_Bool Ty_Bool) :=
  typing_example_1

/-- 示例 2：高阶复合函数定型 -/
theorem typing_example_2 :
  has_type empty
    (tm_abs x Ty_Bool
      (tm_abs y (Ty_Arrow Ty_Bool Ty_Bool)
        (tm_app (tm_var y) (tm_app (tm_var y) (tm_var x)))))
    (Ty_Arrow Ty_Bool (Ty_Arrow (Ty_Arrow Ty_Bool Ty_Bool) Ty_Bool)) := by
  apply has_type.T_Abs
  apply has_type.T_Abs
  apply has_type.T_App Ty_Bool Ty_Bool
  · apply has_type.T_Var
    exact update_eq ty _ y (Ty_Arrow Ty_Bool Ty_Bool)
  · apply has_type.T_App Ty_Bool Ty_Bool
    · apply has_type.T_Var
      exact update_eq ty _ y (Ty_Arrow Ty_Bool Ty_Bool)
    · apply has_type.T_Var
      have Hneq : y ≠ x := by decide
      rw [update_neq ty (x |-> Ty_Bool ; empty) x y (Ty_Arrow Ty_Bool Ty_Bool) Hneq]
      exact update_eq ty empty x Ty_Bool

/--
**** 练习: 2 星, standard, optional (typing_example_2_full)
不依赖自动策略，显式单步构造 `typing_example_2` 的定型推导。
-/
theorem typing_example_2_full :
  has_type empty
    (tm_abs x Ty_Bool
      (tm_abs y (Ty_Arrow Ty_Bool Ty_Bool)
        (tm_app (tm_var y) (tm_app (tm_var y) (tm_var x)))))
    (Ty_Arrow Ty_Bool (Ty_Arrow (Ty_Arrow Ty_Bool Ty_Bool) Ty_Bool)) := by
  sorry

/--
**** 练习: 2 星, standard (typing_example_3)
证明存在某个类型 `T`，使得复合应用函数 `\x, \y, \z, y (x z)` 能够定型。
-/
theorem typing_example_3 :
  ∃ T,
    has_type empty
      (tm_abs x (Ty_Arrow Ty_Bool Ty_Bool)
        (tm_abs y (Ty_Arrow Ty_Bool Ty_Bool)
          (tm_abs z Ty_Bool
            (tm_app (tm_var y) (tm_app (tm_var x) (tm_var z))))))
      T := by
  sorry

/-- 非良构示例 1：无法定型应用 -/
theorem typing_nonexample_1 :
  ¬ ∃ T,
    has_type empty
      (tm_abs x Ty_Bool
        (tm_abs y Ty_Bool
          (tm_app (tm_var x) (tm_var y))))
      T := by
  rintro ⟨T, H⟩
  cases H with
  | T_Abs _ _ T1 T2 t1 H1 =>
    cases H1 with
    | T_Abs _ _ T3 T4 t2 H2 =>
      cases H2 with
      | T_App _ _ _ _ _ Hx Hy =>
        cases Hx with
        | T_Var _ _ _ Hx_eq =>
          have Hneq : y ≠ x := by decide
          rw [update_neq ty (x |-> Ty_Bool ; empty) x y Ty_Bool Hneq] at Hx_eq
          rw [update_eq ty empty x Ty_Bool] at Hx_eq
          injection Hx_eq with Hcontra
          nomatch Hcontra


/--
**** 练习: 3 星, standard, optional (typing_nonexample_3)
证明自身应用 `\x:S, x x` 无法定型（STLC 排除自我应用自指悖论）。
-/
theorem typing_nonexample_3 :
  ¬ ∃ S T,
    has_type empty
      (tm_abs x S (tm_app (tm_var x) (tm_var x)))
      T := by
  sorry

end STLC

end PLF.Stlc
