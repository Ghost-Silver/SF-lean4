---
title: "Smallstep: 小步操作语义：上下文归约、确定性与多步闭包"
---

```lean
import SFLean4.LF.Basics
import SFLean4.LF.Induction
import SFLean4.LF.Maps
import SFLean4.LF.Imp
import SFLean4.LF.Rel
import SFLean4.PLF.Equiv
import SFLean4.PLF.Hoare
import SFLean4.PLF.Hoare2
import SFLean4.PLF.HoareAsLogic

set_option linter.defProp false
set_option linter.ambiguousOpen false
set_option linter.unusedVariables false
```

# 《软件基础》(Software Foundations) 卷二：程序语言基础 (PLF)

## 第五章：小步操作语义 (Smallstep: Small-Step Operational Semantics)

在卷一《逻辑基础》(LF) 的 [Imp](file:///Users/ghostface/LuoJin/SF-lean4/SFLean4/LF/Imp.lean) 章节中，
我们定义了命令式语言 Imp 的**大步操作语义（Big-Step Operational Semantics，亦称自然语义 Natural Semantics）**：
求值关系形如 `st =[ c ]=> st'`，直接建立程序的初始状态到最终停机状态之间的映射。

大步语义非常直观，且在许多静态验证场景中十分方便。然而它存在深刻的理论局限：
1. **无法区分发散（Divergence）与卡住（Stuckness）**：若程序死循环（如 `WHILE true DO SKIP END`），大步求值树无限深，结论中不存在任何满足 `st =[ c ]=> st'` 的 `st'`，这与程序因语义错误“卡死”在形式上无法区分。
2. **难以建模并发与反应式系统（Concurrency and Reactivity）**：大步求值是原子的、整体的，无法细粒度刻画两个并发线程在共享内存上的交替执行（Interleaving）。

为此，戈登·普洛特金（Gordon Plotkin）于 1981 年提出了**结构化操作语义（Structural Operational Semantics, SOS）**，即**小步操作语义（Small-Step Operational Semantics）**：
- 它将计算建模为一个**抽象机器（Abstract Machine）**；
- 机器状态在一步（One Step）原子规约中发生转移：`t --> t'`；
- 计算过程表现为多步单步转移序列（`t -->* t'`）。

### 本章核心目标：
1. **玩具加法语言**：引入极小算术表达式，对比大步求值函数 `evalF`、大步关系 `eval` 与小步规约 `step`。
2. **抽象关系理论**：形式化单步规约的**确定性（Determinism）**。
3. **值与规范形式**：深入探讨**值（Values）**的句法语义与**规范形式（Normal Forms）**的语义概念，证明**强进益定理（Strong Progress）**。
4. **多步规约闭包**：归纳定义自反传递闭包 `multi`（`-->*`），证明规范形式唯一性与强规范化定理（Normalization）。
5. **大步与小步等价性**：完整形式化大步语义与小步语义的双向等价性定理（`eval t n ↔ t -->* C n`）。
6. **Imp 的小步操作语义**：将小步思想推广至完整 Imp 语言（算术 `astep`、布尔 `bstep`、命令 `cstep`）。
7. **并发 Imp (Concurrent Imp, CImp)**：为 Imp 引入并行操作符 `c1 || c2`，展示小步语义精确刻画并发非确定性交织的威力。
8. **栈机器编译器正确性**：用小步操作语义证明 AOT 编译器 `s_compile` 针对栈式虚拟机是完全正确的。

---

## 玩具语言 (A Toy Language)

```lean
namespace PLF.Smallstep

open Imp
open Maps
open aexp bexp com
open sinstr

/-- 占位断言（用于练习填空提示） -/
def FILL_IN_HERE : Nat := 0
```

### 1. 语法与大步求值
极简语言仅包含常量数值 `C n` 与加法复合 `P t1 t2`。

### 单步规约初探 (SimpleArith1)

## 二元关系与确定性 (Relations and Determinism)

## 值、强进益与规范形式 (Values, Progress and Normal Forms)

```lean
/-- 极简算术表达式类型 -/
inductive tm : Type where
  | C (n : Nat) : tm
  | P (t1 t2 : tm) : tm
deriving Repr, DecidableEq

/-- 递归大步求值函数 -/
def evalF (t : tm) : Nat :=
  match t with
  | tm.C n => n
  | tm.P t1 t2 => evalF t1 + evalF t2

/-- 关系式大步求值 -/
inductive eval : tm → Nat → Prop where
  | E_C (n : Nat) : eval (tm.C n) n
  | E_P (t1 t2 : tm) (n1 n2 : Nat) :
      eval t1 n1 → eval t2 n2 → eval (tm.P t1 t2) (n1 + n2)

scoped notation:50 t " ==> " n => eval t n


namespace SimpleArith1

/-- 初步单步规约关系 -/
inductive step : tm → tm → Prop where
  | ST_PCC (n1 n2 : Nat) : step (tm.P (tm.C n1) (tm.C n2)) (tm.C (n1 + n2))
  | ST_P1 (t1 t1' t2 : tm) : step t1 t1' → step (tm.P t1 t2) (tm.P t1' t2)
  | ST_P2 (n1 : Nat) (t2 t2' : tm) : step t2 t2' → step (tm.P (tm.C n1) t2) (tm.P (tm.C n1) t2')

scoped notation:40 t " --> " t' => step t t'

/-- 单步规约示例 1 -/
theorem test_step_1 :
  step (tm.P (tm.P (tm.C 1) (tm.C 3)) (tm.P (tm.C 2) (tm.C 4)))
       (tm.P (tm.C 4) (tm.P (tm.C 2) (tm.C 4))) := by
  apply step.ST_P1
  exact step.ST_PCC 1 3

/--
**** 练习: 1 星, standard (test_step_2)
-/
theorem test_step_2 :
  step (tm.P (tm.C 0) (tm.P (tm.C 2) (tm.P (tm.C 1) (tm.C 3))))
       (tm.P (tm.C 0) (tm.P (tm.C 2) (tm.C 4))) := by
  sorry

end SimpleArith1


/-- 抽象二元关系定义 -/
def relation (X : Type) := X → X → Prop

/-- 关系确定性：任意项至多规约到一个后继项 -/
def deterministic {X : Type} (R : relation X) : Prop :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2

namespace SimpleArith2

open SimpleArith1

/-- 单步规约确定性定理 -/
theorem step_deterministic :
  deterministic SimpleArith1.step := by
  intro x y1 y2 h1
  revert y2
  induction h1 with
  | ST_PCC n1 n2 =>
    intro y2 h2
    cases h2 with
    | ST_PCC => rfl
    | ST_P1 _ _ _ h => cases h
    | ST_P2 _ _ _ h => cases h
  | ST_P1 t1 t1' t2 h1 ih =>
    intro y2 h2
    cases h2 with
    | ST_PCC => cases h1
    | ST_P1 _ t1'' _ h2 =>
      have := ih t1'' h2
      rw [this]
    | ST_P2 n1 _ _ h2 => cases h1
  | ST_P2 n1 t2 t2' h1 ih =>
    intro y2 h2
    cases h2 with
    | ST_PCC => cases h1
    | ST_P1 _ _ _ h => cases h
    | ST_P2 _ _ t2'' h2 =>
      have := ih t2'' h2
      rw [this]

end SimpleArith2

namespace SimpleArith3

open SimpleArith1

/-- 确定性定理的简化呈现 -/
theorem step_deterministic_alt : deterministic SimpleArith1.step :=
  SimpleArith2.step_deterministic

end SimpleArith3
```

### 2. 基于值（Values）的单步规约

机器的停机状态称为**值（Values）**。对于加法语言，值恰好就是常数 `C n`。
利用谓词 `value`，我们可以更优雅地书写求值顺序规则 `ST_P2`。

### 值与规范形式的非等价变体 (Temp Modules)

## 多步规约闭包 (Multi-Step Reduction)

```lean
/-- 值谓词：判断项是否为计算结果 -/
inductive value : tm → Prop where
  | v_C (n : Nat) : value (tm.C n)

/-- 引入值概念后的正式单步规约关系 -/
inductive step : tm → tm → Prop where
  | ST_PCC (n1 n2 : Nat) : step (tm.P (tm.C n1) (tm.C n2)) (tm.C (n1 + n2))
  | ST_P1 (t1 t1' t2 : tm) : step t1 t1' → step (tm.P t1 t2) (tm.P t1' t2)
  | ST_P2 (v1 t2 t2' : tm) : value v1 → step t2 t2' → step (tm.P v1 t2) (tm.P v1 t2')

scoped notation:40 t " --> " t' => step t t'

/--
**** 练习: 3 星, standard, especially useful (redo_determinism)
重新验证确定性。
-/
theorem step_deterministic :
  deterministic step := by
  sorry

/-- 强进益定理：任意项要么已经是值，要么可以再走一步 -/
theorem strong_progress : ∀ t,
  value t ∨ (∃ t', step t t') := by
  intro t
  induction t with
  | C n => left; exact value.v_C n
  | P t1 t2 ih1 ih2 =>
    right
    rcases ih1 with (hv1 | ⟨t1', ht1'⟩)
    · rcases ih2 with (hv2 | ⟨t2', ht2'⟩)
      · cases hv1 with
        | v_C n1 =>
          cases hv2 with
          | v_C n2 =>
            exact ⟨tm.C (n1 + n2), step.ST_PCC n1 n2⟩
      · exact ⟨tm.P t1 t2', step.ST_P2 t1 t2 t2' hv1 ht2'⟩
    · exact ⟨tm.P t1' t2, step.ST_P1 t1 t1' t2 ht1'⟩

/-- 规范形式（不可再规约项） -/
def normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'

/-- 引理：值必定是规范形式 -/
theorem value_is_nf : ∀ v,
  value v → normal_form step v := by
  intro v hv ⟨t', ht'⟩
  cases hv with
  | v_C n => cases ht'

/-- 引理：规范形式必定是值 -/
theorem nf_is_value : ∀ t,
  normal_form step t → value t := by
  intro t hnf
  have hp := strong_progress t
  rcases hp with (hv | hstep)
  · exact hv
  · exact (hnf hstep).elim

/-- 规范形式与值等价性定理 -/
theorem nf_same_as_value : ∀ t,
  normal_form step t ↔ value t := by
  intro t
  constructor
  · exact nf_is_value t
  · exact value_is_nf t


namespace Temp1

/-- 错误变体 1：值中包含了尚未完全化简的复合表达式 -/
inductive value : tm → Prop where
  | v_C (n : Nat) : value (tm.C n)
  | v_funny (t1 : tm) (n : Nat) : value (tm.P t1 (tm.C n))

inductive step : tm → tm → Prop where
  | ST_PCC (n1 n2 : Nat) : step (tm.P (tm.C n1) (tm.C n2)) (tm.C (n1 + n2))
  | ST_P1 (t1 t1' t2 : tm) : step t1 t1' → step (tm.P t1 t2) (tm.P t1' t2)
  | ST_P2 (v1 t2 t2' : tm) : value v1 → step t2 t2' → step (tm.P v1 t2) (tm.P v1 t2')

/--
**** 练习: 3 星, standard, optional (value_not_same_as_normal_form1)
-/
theorem value_not_same_as_normal_form :
  ∃ v, value v ∧ ¬ normal_form step v := by
  sorry

end Temp1

namespace Temp2

inductive value : tm → Prop where
  | v_C (n : Nat) : value (tm.C n)

/-- 错误变体 2：规约规则允许将已经是值的内容进一步无休止展开 -/
inductive step : tm → tm → Prop where
  | ST_Funny (n : Nat) : step (tm.C n) (tm.P (tm.C n) (tm.C 0))
  | ST_PCC (n1 n2 : Nat) : step (tm.P (tm.C n1) (tm.C n2)) (tm.C (n1 + n2))
  | ST_P1 (t1 t1' t2 : tm) : step t1 t1' → step (tm.P t1 t2) (tm.P t1' t2)
  | ST_P2 (v1 t2 t2' : tm) : value v1 → step t2 t2' → step (tm.P v1 t2) (tm.P v1 t2')

/--
**** 练习: 2 星, standard, optional (value_not_same_as_normal_form2)
-/
theorem value_not_same_as_normal_form :
  ∃ v, value v ∧ ¬ normal_form step v := by
  sorry

end Temp2

namespace Temp3

inductive value : tm → Prop where
  | v_C (n : Nat) : value (tm.C n)

/-- 错误变体 3：遗漏了 ST_P2 导致未完全计算的项提前卡死 -/
inductive step : tm → tm → Prop where
  | ST_PCC (n1 n2 : Nat) : step (tm.P (tm.C n1) (tm.C n2)) (tm.C (n1 + n2))
  | ST_P1 (t1 t1' t2 : tm) : step t1 t1' → step (tm.P t1 t2) (tm.P t1' t2)

/--
**** 练习: 3 星, standard, optional (value_not_same_as_normal_form3)
-/
theorem value_not_same_as_normal_form :
  ∃ t, ¬ value t ∧ normal_form step t := by
  sorry

end Temp3

namespace Temp4

/-- 极简布尔表达式语言 -/
inductive tm : Type where
  | tru : tm
  | fls : tm
  | test : tm → tm → tm → tm
deriving Repr, DecidableEq

inductive value : tm → Prop where
  | v_tru : value tm.tru
  | v_fls : value tm.fls

inductive step : tm → tm → Prop where
  | ST_IfTrue (t1 t2 : tm) : step (tm.test tm.tru t1 t2) t1
  | ST_IfFalse (t1 t2 : tm) : step (tm.test tm.fls t1 t2) t2
  | ST_If (t1 t1' t2 t3 : tm) : step t1 t1' → step (tm.test t1 t2 t3) (tm.test t1' t2 t3)

/--
**** 练习: 1 星, standard, optional (smallstep_bools)
-/
def bool_step_prop1 : Prop := step tm.fls tm.fls

theorem bool_step_prop1_false : ¬ bool_step_prop1 := by
  intro h; cases h

def bool_step_prop2 : Prop :=
  step (tm.test tm.tru (tm.test tm.tru tm.tru tm.tru) (tm.test tm.fls tm.fls tm.fls)) tm.tru

theorem bool_step_prop2_false : ¬ bool_step_prop2 := by
  intro h; cases h

def bool_step_prop3 : Prop :=
  step (tm.test (tm.test tm.tru tm.tru tm.tru) (tm.test tm.tru tm.tru tm.tru) tm.fls)
       (tm.test tm.tru (tm.test tm.tru tm.tru tm.tru) tm.fls)

theorem bool_step_prop3_false : bool_step_prop3 := by
  apply step.ST_If
  exact step.ST_IfTrue tm.tru tm.tru

def manual_grade_for_smallstep_bools : Option (Nat × String) := none

/--
**** 练习: 3 星, standard, optional (strong_progress_bool)
-/
theorem strong_progress_bool : ∀ t,
  value t ∨ (∃ t', step t t') := by
  sorry

/--
**** 练习: 2 星, standard, optional (step_deterministic)
-/
theorem step_deterministic : deterministic step := by
  sorry

namespace Temp5

/-- 扩展了短路规则的布尔小步规约 -/
inductive step : tm → tm → Prop where
  | ST_IfTrue (t1 t2 : tm) : step (tm.test tm.tru t1 t2) t1
  | ST_IfFalse (t1 t2 : tm) : step (tm.test tm.fls t1 t2) t2
  | ST_If (t1 t1' t2 t3 : tm) : step t1 t1' → step (tm.test t1 t2 t3) (tm.test t1' t2 t3)
  | ST_ShortCircuit (t t' : tm) : value t' → step (tm.test t t' t') t'

/--
**** 练习: 2 星, standard (smallstep_bool_shortcut)
-/
def bool_step_prop4 : Prop :=
  step (tm.test (tm.test tm.tru tm.tru tm.tru) tm.fls tm.fls) tm.fls

theorem bool_step_prop4_holds : bool_step_prop4 := by
  apply step.ST_ShortCircuit
  exact value.v_fls

/--
**** 练习: 3 星, standard, optional (properties_of_altered_step)
证明添加短路规则破坏了单步规约的确定性。
-/
theorem step_non_deterministic :
  ¬ deterministic step := by
  sorry

def manual_grade_for_properties_of_altered_step : Option (Nat × String) := none

end Temp5
end Temp4
```

### 3. 多步规约关系 `multi`

`multi R` 是单步关系 `R` 的自反传递闭包（在逻辑基础 `Rel` 章节中称为 `clos_refl_trans_1n`）。
记作 `t -->* t'`。

### 大步语义与小步语义等价性 (Equivalence)

## 复合语言示例 (Combined Language)

## Imp 语言的小步操作语义 (Small-Step Imp)

```lean
/-- 二元关系自反传递闭包 -/
inductive multi {X : Type} (R : relation X) : relation X where
  | multi_refl (x : X) : multi R x x
  | multi_step (x y z : X) : R x y → multi R y z → multi R x z

scoped notation:40 t " -->* " t' => multi step t t'

/-- 单步蕴含在多步闭包中 -/
theorem multi_R : ∀ (X : Type) (R : relation X) (x y : X),
    R x y → (multi R) x y := by
  intro X R x y h
  exact multi.multi_step x y y h (multi.multi_refl y)

/-- 多步规约的传递性定理 -/
theorem multi_trans : ∀ (X : Type) (R : relation X) (x y z : X),
    multi R x y → multi R y z → multi R x z := by
  intro X R x y z g h
  induction g with
  | multi_refl _ => exact h
  | multi_step x w y hr hmulti ih =>
    exact multi.multi_step x w z hr (ih h)

/-- 多步规约实例 1 -/
theorem test_multistep_1 :
  multi step (tm.P (tm.P (tm.C 0) (tm.C 3)) (tm.P (tm.C 2) (tm.C 4)))
             (tm.C ((0 + 3) + (2 + 4))) := by
  apply multi.multi_step (y := tm.P (tm.C (0 + 3)) (tm.P (tm.C 2) (tm.C 4)))
  · exact step.ST_P1 _ _ _ (step.ST_PCC 0 3)
  · apply multi.multi_step (y := tm.P (tm.C (0 + 3)) (tm.C (2 + 4)))
    · exact step.ST_P2 (tm.C (0 + 3)) _ _ (value.v_C (0 + 3)) (step.ST_PCC 2 4)
    · apply multi_R
      exact step.ST_PCC (0 + 3) (2 + 4)

theorem test_multistep_1' :
  multi step (tm.P (tm.P (tm.C 0) (tm.C 3)) (tm.P (tm.C 2) (tm.C 4)))
             (tm.C ((0 + 3) + (2 + 4))) := test_multistep_1

/--
**** 练习: 1 星, standard, optional (test_multistep_2)
-/
theorem test_multistep_2 :
  multi step (tm.C 3) (tm.C 3) := by
  sorry

/--
**** 练习: 1 星, standard, optional (test_multistep_3)
-/
theorem test_multistep_3 :
  multi step (tm.P (tm.C 0) (tm.C 3)) (tm.P (tm.C 0) (tm.C 3)) := by
  sorry

/--
**** 练习: 2 星, standard (test_multistep_4)
-/
theorem test_multistep_4 :
  multi step (tm.P (tm.C 0) (tm.P (tm.C 2) (tm.P (tm.C 0) (tm.C 3))))
             (tm.P (tm.C 0) (tm.C (2 + (0 + 3)))) := by
  sorry

/-- t' 是 t 的规范形式 -/
def normal_form_of {X : Type} (R : relation X) (t t' : X) : Prop :=
  multi R t t' ∧ normal_form R t'

/--
**** 练习: 3 星, standard, optional (normal_forms_unique)
证明对于确定性小步系统，规范形式是唯一的。
-/
theorem normal_forms_unique :
  deterministic (normal_form_of step) := by
  sorry

/-- 强规范化性质：任意项均能在有限步内达到规范形式 -/
def normalizing {X : Type} (R : relation X) : Prop :=
  ∀ t, ∃ t', normal_form_of R t t'

/-- 加法同余引理 1：左操作数多步规约 -/
theorem multistep_congr_1 : ∀ t1 t1' t2,
  multi step t1 t1' →
  multi step (tm.P t1 t2) (tm.P t1' t2) := by
  intro t1 t1' t2 h
  induction h with
  | multi_refl _ => exact multi.multi_refl _
  | multi_step x y z hstep hmulti ih =>
    exact multi.multi_step (tm.P x t2) (tm.P y t2) (tm.P z t2) (step.ST_P1 x y t2 hstep) ih

/--
**** 练习: 2 星, standard (multistep_congr_2)
加法同余引理 2：左操作数为值时，右操作数多步规约。
-/
theorem multistep_congr_2 : ∀ v1 t2 t2',
  value v1 →
  multi step t2 t2' →
  multi step (tm.P v1 t2) (tm.P v1 t2') := by
  sorry

/-- 规范化定理：玩具加法语言的单步规约是强规范化的 -/
theorem step_normalizing :
  normalizing step := by
  intro t
  induction t with
  | C n =>
    exact ⟨tm.C n, multi.multi_refl _, (nf_same_as_value (tm.C n)).mpr (value.v_C n)⟩
  | P t1 t2 ih1 ih2 =>
    rcases ih1 with ⟨t1', hsteps1, hnorm1⟩
    rcases ih2 with ⟨t2', hsteps2, hnorm2⟩
    have hv1 := (nf_same_as_value t1').mp hnorm1
    have hv2 := (nf_same_as_value t2').mp hnorm2
    cases hv1 with
    | v_C n1 =>
      cases hv2 with
      | v_C n2 =>
        refine ⟨tm.C (n1 + n2), ?_, (nf_same_as_value (tm.C (n1 + n2))).mpr (value.v_C (n1 + n2))⟩
        apply multi_trans (y := tm.P (tm.C n1) t2)
        · exact multistep_congr_1 t1 (tm.C n1) t2 hsteps1
        · apply multi_trans (y := tm.P (tm.C n1) (tm.C n2))
          · exact multistep_congr_2 (tm.C n1) t2 (tm.C n2) (value.v_C n1) hsteps2
          · exact multi_R _ _ _ _ (step.ST_PCC n1 n2)


/--
**** 练习: 3 星, standard (eval__multistep)
证明大步求值必定蕴含多步小步规约到对应值。
-/
theorem eval__multistep : ∀ t n,
  eval t n → multi step t (tm.C n) := by
  sorry

def manual_grade_for_eval__multistep_inf : Option (Nat × String) := none

/--
**** 练习: 3 星, standard (step__eval)
证明单步规约与大步求值向后兼容。
-/
theorem step__eval : ∀ t t' n,
  step t t' →
  eval t' n →
  eval t n := by
  sorry

/--
**** 练习: 3 星, standard (multistep__eval)
证明多步规约到规范形式必定蕴含大步求值成立。
-/
theorem multistep__eval : ∀ t t',
  normal_form_of step t t' → ∃ n, t' = tm.C n ∧ eval t n := by
  sorry

/--
**** 练习: 3 星, standard, optional (interp_tm)
证明函数式大步求值与关系式大步求值完全等价。
-/
theorem evalF_eval : ∀ t n,
  evalF t = n ↔ eval t n := by
  sorry


namespace Combined

inductive tm : Type where
  | C (n : Nat) : tm
  | P (t1 t2 : tm) : tm
  | tru : tm
  | fls : tm
  | test : tm → tm → tm → tm
deriving Repr, DecidableEq

inductive value : tm → Prop where
  | v_C (n : Nat) : value (tm.C n)
  | v_tru : value tm.tru
  | v_fls : value tm.fls

inductive step : tm → tm → Prop where
  | ST_PCC (n1 n2 : Nat) : step (tm.P (tm.C n1) (tm.C n2)) (tm.C (n1 + n2))
  | ST_P1 (t1 t1' t2 : tm) : step t1 t1' → step (tm.P t1 t2) (tm.P t1' t2)
  | ST_P2 (v1 t2 t2' : tm) : value v1 → step t2 t2' → step (tm.P v1 t2) (tm.P v1 t2')
  | ST_IfTrue (t1 t2 : tm) : step (tm.test tm.tru t1 t2) t1
  | ST_IfFalse (t1 t2 : tm) : step (tm.test tm.fls t1 t2) t2
  | ST_If (t1 t1' t2 t3 : tm) : step t1 t1' → step (tm.test t1 t2 t3) (tm.test t1' t2 t3)

/--
**** 练习: 3 星, standard (combined_step_deterministic)
-/
theorem combined_step_deterministic : (deterministic step) ∨ ¬ (deterministic step) := by
  sorry

/--
**** 练习: 3 星, standard (combined_strong_progress)
-/
theorem combined_strong_progress :
  (∀ t, value t ∨ (∃ t', step t t')) ∨ ¬ (∀ t, value t ∨ (∃ t', step t t')) := by
  sorry

end Combined
```

### 4. 算术、布尔与命令的小步规约

为 Imp 建立小步操作语义：
- 算术表达式小步单步转移：`a / st -->a a'`
- 布尔表达式小步单步转移：`b / st -->b b'`
- 命令在环境中的转移：`(c, st) --> (c', st')`

## 并发 Imp 语言 (Concurrent Imp - CImp)

```lean
/-- 算术值谓词 -/
inductive aval : aexp → Prop where
  | av_num (n : Nat) : aval (ANum n)

/-- 算术表达式单步求值关系 -/
inductive astep (st : state) : aexp → aexp → Prop where
  | AS_Id (i : String) :
      astep st (AId i) (ANum (st i))
  | AS_P1 (a1 a1' a2 : aexp) :
      astep st a1 a1' →
      astep st (APlus a1 a2) (APlus a1' a2)
  | AS_P2 (v1 a2 a2' : aexp) :
      aval v1 →
      astep st a2 a2' →
      astep st (APlus v1 a2) (APlus v1 a2')
  | AS_P (v1 v2 : Nat) :
      astep st (APlus (ANum v1) (ANum v2)) (ANum (v1 + v2))
  | AS_Minus1 (a1 a1' a2 : aexp) :
      astep st a1 a1' →
      astep st (AMinus a1 a2) (AMinus a1' a2)
  | AS_Minus2 (v1 a2 a2' : aexp) :
      aval v1 →
      astep st a2 a2' →
      astep st (AMinus v1 a2) (AMinus v1 a2')
  | AS_Minus (v1 v2 : Nat) :
      astep st (AMinus (ANum v1) (ANum v2)) (ANum (v1 - v2))
  | AS_Mult1 (a1 a1' a2 : aexp) :
      astep st a1 a1' →
      astep st (AMult a1 a2) (AMult a1' a2)
  | AS_Mult2 (v1 a2 a2' : aexp) :
      aval v1 →
      astep st a2 a2' →
      astep st (AMult v1 a2) (AMult v1 a2')
  | AS_Mult (v1 v2 : Nat) :
      astep st (AMult (ANum v1) (ANum v2)) (ANum (v1 * v2))

/-- 布尔表达式单步求值关系 -/
inductive bstep (st : state) : bexp → bexp → Prop where
  | BS_Eq1 (a1 a1' a2 : aexp) :
      astep st a1 a1' →
      bstep st (BEq a1 a2) (BEq a1' a2)
  | BS_Eq2 (v1 a2 a2' : aexp) :
      aval v1 →
      astep st a2 a2' →
      bstep st (BEq v1 a2) (BEq v1 a2')
  | BS_Eq (v1 v2 : Nat) :
      bstep st (BEq (ANum v1) (ANum v2)) (if v1 == v2 then BTrue else BFalse)
  | BS_LtEq1 (a1 a1' a2 : aexp) :
      astep st a1 a1' →
      bstep st (BLe a1 a2) (BLe a1' a2)
  | BS_LtEq2 (v1 a2 a2' : aexp) :
      aval v1 →
      astep st a2 a2' →
      bstep st (BLe v1 a2) (BLe v1 a2')
  | BS_LtEq (v1 v2 : Nat) :
      bstep st (BLe (ANum v1) (ANum v2)) (if v1 ≤ v2 then BTrue else BFalse)
  | BS_NotStep (b1 b1' : bexp) :
      bstep st b1 b1' →
      bstep st (BNot b1) (BNot b1')
  | BS_NotTrue : bstep st (BNot BTrue) BFalse
  | BS_NotFalse : bstep st (BNot BFalse) BTrue
  | BS_AndStep (b1 b1' b2 : bexp) :
      bstep st b1 b1' →
      bstep st (BAnd b1 b2) (BAnd b1' b2)
  | BS_AndTrueStep (b2 b2' : bexp) :
      bstep st b2 b2' →
      bstep st (BAnd BTrue b2) (BAnd BTrue b2')
  | BS_AndFalse (b2 : bexp) :
      bstep st (BAnd BFalse b2) BFalse
  | BS_AndTrueTrue : bstep st (BAnd BTrue BTrue) BTrue
  | BS_AndTrueFalse : bstep st (BAnd BTrue BFalse) BFalse

/-- 命令小步转移关系：输入为命令与状态对 -/
inductive cstep : (com × state) → (com × state) → Prop where
  | CS_AsgnStep (st : state) (i : String) (a1 a1' : aexp) :
      astep st a1 a1' →
      cstep (com.CAsgn i a1, st) (com.CAsgn i a1', st)
  | CS_Asgn (st : state) (i : String) (n : Nat) :
      cstep (com.CAsgn i (ANum n), st) (com.CSkip, t_update st i n)
  | CS_SeqStep (st : state) (c1 c1' : com) (st' : state) (c2 : com) :
      cstep (c1, st) (c1', st') →
      cstep (com.CSeq c1 c2, st) (com.CSeq c1' c2, st')
  | CS_SeqFinish (st : state) (c2 : com) :
      cstep (com.CSeq com.CSkip c2, st) (c2, st)
  | CS_IfStep (st : state) (b1 b1' : bexp) (c1 c2 : com) :
      bstep st b1 b1' →
      cstep (com.CIf b1 c1 c2, st) (com.CIf b1' c1 c2, st)
  | CS_IfTrue (st : state) (c1 c2 : com) :
      cstep (com.CIf BTrue c1 c2, st) (c1, st)
  | CS_IfFalse (st : state) (c1 c2 : com) :
      cstep (com.CIf BFalse c1 c2, st) (c2, st)
  | CS_While (st : state) (b1 : bexp) (c1 : com) :
      cstep (com.CWhile b1 c1, st)
            (com.CIf b1 (com.CSeq c1 (com.CWhile b1 c1)) com.CSkip, st)
```

### 5. 并发小步语义与非确定性交织

扩展命令语法，增加并行算子 `c1 || c2`：
只要任一线程能走一步，整体即可选择该线程执行单步规约，从而产生丰富的交织行为。

## 栈式虚拟机小步语义与编译器正确性 (A Small-Step Stack Machine)

```lean
namespace CImp

/-- 支持并发并行的命令扩展 -/
inductive com : Type where
  | CSkip : com
  | CAsgn : String → aexp → com
  | CSeq : com → com → com
  | CIf : bexp → com → com → com
  | CWhile : bexp → com → com
  | CPar : com → com → com
deriving Repr, DecidableEq

/-- 并发 Imp 命令小步转移 -/
inductive cstep : (com × state) → (com × state) → Prop where
  | CS_AsgnStep (st : state) (i : String) (a1 a1' : aexp) :
      astep st a1 a1' →
      cstep (com.CAsgn i a1, st) (com.CAsgn i a1', st)
  | CS_Asgn (st : state) (i : String) (n : Nat) :
      cstep (com.CAsgn i (ANum n), st) (com.CSkip, t_update st i n)
  | CS_SeqStep (st : state) (c1 c1' : com) (st' : state) (c2 : com) :
      cstep (c1, st) (c1', st') →
      cstep (com.CSeq c1 c2, st) (com.CSeq c1' c2, st')
  | CS_SeqFinish (st : state) (c2 : com) :
      cstep (com.CSeq com.CSkip c2, st) (c2, st)
  | CS_IfStep (st : state) (b1 b1' : bexp) (c1 c2 : com) :
      bstep st b1 b1' →
      cstep (com.CIf b1 c1 c2, st) (com.CIf b1' c1 c2, st)
  | CS_IfTrue (st : state) (c1 c2 : com) :
      cstep (com.CIf BTrue c1 c2, st) (c1, st)
  | CS_IfFalse (st : state) (c1 c2 : com) :
      cstep (com.CIf BFalse c1 c2, st) (c2, st)
  | CS_While (st : state) (b1 : bexp) (c1 : com) :
      cstep (com.CWhile b1 c1, st)
            (com.CIf b1 (com.CSeq c1 (com.CWhile b1 c1)) com.CSkip, st)
  | CS_Par1 (st : state) (c1 c1' c2 : com) (st' : state) :
      cstep (c1, st) (c1', st') →
      cstep (com.CPar c1 c2, st) (com.CPar c1' c2, st')
  | CS_Par2 (st : state) (c1 c2 c2' : com) (st' : state) :
      cstep (c2, st) (c2', st') →
      cstep (com.CPar c1 c2, st) (com.CPar c1 c2', st')
  | CS_ParDone (st : state) :
      cstep (com.CPar com.CSkip com.CSkip, st) (com.CSkip, st)

/-- 经典并发竞争循环程序 -/
def par_loop : com :=
  com.CPar
    (com.CAsgn Y (ANum 1))
    (com.CWhile (BEq (AId Y) (ANum 0)) (com.CAsgn X (APlus (AId X) (ANum 1))))

/-- 示例：并发循环可以终止于 X = 0 -/
theorem par_loop_example_0 :
  ∃ st', multi cstep (par_loop, empty_st) (com.CSkip, st') ∧ st' X = 0 := by
  sorry

/-- 示例：并发循环可以终止于 X = 2 -/
theorem par_loop_example_2 :
  ∃ st', multi cstep (par_loop, empty_st) (com.CSkip, st') ∧ st' X = 2 := by
  sorry

/--
**** 练习: 3 星, standard, optional (par_body_n__Sn)
-/
theorem par_body_n__Sn : ∀ n st,
  st X = n ∧ st Y = 0 →
  ∃ st',
    multi cstep (com.CWhile (BEq (AId Y) (ANum 0)) (com.CAsgn X (APlus (AId X) (ANum 1))), st)
                (com.CWhile (BEq (AId Y) (ANum 0)) (com.CAsgn X (APlus (AId X) (ANum 1))), st') ∧
    st' X = n + 1 ∧ st' Y = 0 := by
  sorry

/--
**** 练习: 3 星, standard, optional (par_body_n)
-/
theorem par_body_n : ∀ n st,
  st X = 0 ∧ st Y = 0 →
  ∃ st',
    multi cstep (com.CWhile (BEq (AId Y) (ANum 0)) (com.CAsgn X (APlus (AId X) (ANum 1))), st)
                (com.CWhile (BEq (AId Y) (ANum 0)) (com.CAsgn X (APlus (AId X) (ANum 1))), st') ∧
    st' X = n ∧ st' Y = 0 := by
  sorry

/-- 定理：并发循环可以终止于任意自然数 X = n -/
theorem par_loop_any_X : ∀ n,
  ∃ st', multi cstep (par_loop, empty_st) (com.CSkip, st') ∧ st' X = n := by
  sorry

end CImp
```

### 6. 基于小步规约的编译器正确性证明

## 规约自动化与求值规范化示例 (Normalization Examples)

```lean
/-- 虚拟机执行栈 -/
abbrev stack := List Nat

/-- 虚拟机指令程序 -/
abbrev prog := List sinstr

/-- 栈机器单步规约转移关系 -/
inductive stack_step (st : state) : prog × stack → prog × stack → Prop where
  | SS_Push (stk : stack) (n : Nat) (p : prog) :
      stack_step st (SPush n :: p, stk) (p, n :: stk)
  | SS_Load (stk : stack) (i : String) (p : prog) :
      stack_step st (SLoad i :: p, stk) (p, st i :: stk)
  | SS_P (stk : stack) (n m : Nat) (p : prog) :
      stack_step st (SPlus :: p, n :: m :: stk) (p, (m + n) :: stk)
  | SS_Minus (stk : stack) (n m : Nat) (p : prog) :
      stack_step st (SMinus :: p, n :: m :: stk) (p, (m - n) :: stk)
  | SS_Mult (stk : stack) (n m : Nat) (p : prog) :
      stack_step st (SMult :: p, n :: m :: stk) (p, (m * n) :: stk)

/-- 栈机器单步规约是完全确定的 -/
theorem stack_step_deterministic : ∀ st,
  deterministic (stack_step st) := by
  intro st x y1 y2 h1 h2
  cases h1 <;> cases h2 <;> rfl

/-- 栈机器多步执行闭包 -/
def stack_multistep (st : state) := multi (stack_step st)

/-- 算术表达式编译函数 -/
def s_compile (e : aexp) : List sinstr :=
  match e with
  | aexp.ANum n => sinstr.SPush n :: []
  | aexp.AId x => sinstr.SLoad x :: []
  | aexp.APlus a1 a2 => s_compile a1 ++ s_compile a2 ++ (sinstr.SPlus :: [])
  | aexp.AMinus a1 a2 => s_compile a1 ++ s_compile a2 ++ (sinstr.SMinus :: [])
  | aexp.AMult a1 a2 => s_compile a1 ++ s_compile a2 ++ (sinstr.SMult :: [])

/-- 编译器正确性命题 -/
def compiler_is_correct_statement : Prop :=
  ∀ (st : state) (e : aexp),
    stack_multistep st (s_compile e, []) ([], [ aeval st e ])

/-- 编译器正确性泛化辅助引理 -/
theorem compiler_is_correct_aux :
  ∀ (st : state) (e : aexp) (stk : stack) (p : prog),
    stack_multistep st (s_compile e ++ p, stk) (p, aeval st e :: stk) := by
  intro st e
  induction e with
  | ANum n =>
    intro stk p
    dsimp [s_compile, aeval]
    apply multi.multi_step _ (p, n :: stk) _ (stack_step.SS_Push stk n p)
    exact multi.multi_refl _
  | AId x =>
    intro stk p
    dsimp [s_compile, aeval]
    apply multi.multi_step _ (p, st x :: stk) _ (stack_step.SS_Load stk x p)
    exact multi.multi_refl _
  | APlus a1 a2 ih1 ih2 =>
    intro stk p
    dsimp [s_compile, aeval]
    repeat rw [List.append_assoc]
    apply multi_trans _ _ _ (s_compile a2 ++ (sinstr.SPlus :: p), aeval st a1 :: stk)
    · exact ih1 stk (s_compile a2 ++ (sinstr.SPlus :: p))
    · apply multi_trans _ _ _ (sinstr.SPlus :: p, aeval st a2 :: aeval st a1 :: stk)
      · exact ih2 (aeval st a1 :: stk) (sinstr.SPlus :: p)
      · apply multi.multi_step _ (p, (aeval st a1 + aeval st a2) :: stk) _ (stack_step.SS_P stk (aeval st a2) (aeval st a1) p)
        exact multi.multi_refl _
  | AMinus a1 a2 ih1 ih2 =>
    intro stk p
    dsimp [s_compile, aeval]
    repeat rw [List.append_assoc]
    apply multi_trans _ _ _ (s_compile a2 ++ (sinstr.SMinus :: p), aeval st a1 :: stk)
    · exact ih1 stk (s_compile a2 ++ (sinstr.SMinus :: p))
    · apply multi_trans _ _ _ (sinstr.SMinus :: p, aeval st a2 :: aeval st a1 :: stk)
      · exact ih2 (aeval st a1 :: stk) (sinstr.SMinus :: p)
      · apply multi.multi_step _ (p, (aeval st a1 - aeval st a2) :: stk) _ (stack_step.SS_Minus stk (aeval st a2) (aeval st a1) p)
        exact multi.multi_refl _
  | AMult a1 a2 ih1 ih2 =>
    intro stk p
    dsimp [s_compile, aeval]
    repeat rw [List.append_assoc]
    apply multi_trans _ _ _ (s_compile a2 ++ (sinstr.SMult :: p), aeval st a1 :: stk)
    · exact ih1 stk (s_compile a2 ++ (sinstr.SMult :: p))
    · apply multi_trans _ _ _ (sinstr.SMult :: p, aeval st a2 :: aeval st a1 :: stk)
      · exact ih2 (aeval st a1 :: stk) (sinstr.SMult :: p)
      · apply multi.multi_step _ (p, (aeval st a1 * aeval st a2) :: stk) _ (stack_step.SS_Mult stk (aeval st a2) (aeval st a1) p)
        exact multi.multi_refl _

/--
**** 练习: 3 星, advanced (compiler_is_correct)
-/
theorem compiler_is_correct : compiler_is_correct_statement := by
  sorry


theorem step_example1 :
  multi step (tm.P (tm.C 3) (tm.P (tm.C 3) (tm.C 4))) (tm.C 10) := by
  apply multi.multi_step (y := tm.P (tm.C 3) (tm.C 7))
  · exact step.ST_P2 (tm.C 3) _ _ (value.v_C 3) (step.ST_PCC 3 4)
  · apply multi.multi_step (y := tm.C 10)
    · exact step.ST_PCC 3 7
    · exact multi.multi_refl _

theorem step_example1' :
  multi step (tm.P (tm.C 3) (tm.P (tm.C 3) (tm.C 4))) (tm.C 10) := step_example1

theorem step_example1'' :
  multi step (tm.P (tm.C 3) (tm.P (tm.C 3) (tm.C 4))) (tm.C 10) := step_example1

theorem step_example1''' :
  ∃ e', multi step (tm.P (tm.C 3) (tm.P (tm.C 3) (tm.C 4))) e' := by
  exact ⟨tm.C 10, step_example1⟩

/--
**** 练习: 1 星, standard (normalize_ex)
-/
theorem normalize_ex : ∃ e',
  multi step (tm.P (tm.C 3) (tm.P (tm.C 2) (tm.C 1))) e' ∧ value e' := by
  sorry

/--
**** 练习: 1 星, standard, optional (normalize_ex')
-/
theorem normalize_ex' : ∃ e',
  multi step (tm.P (tm.C 3) (tm.P (tm.C 2) (tm.C 1))) e' ∧ value e' := by
  sorry

end PLF.Smallstep
```
