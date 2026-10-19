import SFLean4.LF.Maps
import SFLean4.LF.Imp

set_option linter.defProp false
set_option linter.ambiguousOpen false
set_option linter.unusedVariables false

/-!
# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)

## 第十四章：Imp 的计算式求值函数 (ImpCEvalFun: An Evaluation Function for Imp)

在 [Imp](/LF/Imp) 一章中，我们看到直接用函数来对 Imp 语言编写求值器会遭遇根本性的困难：
由于包含可能不终止的 `while` 循环，Imp 命令的执行是一个**偏函数（Partial Function）**。
在先前的章节里，我们通过将求值转定义为归纳命题关系（即大步操作语义 `st =[ c ]=> st'`）巧妙地绕过了停机问题。

在本章中，我们将探讨另一种经典的解决方案：**步数索引求值（Step-Indexed Evaluation）**。
通过向求值函数传入一个额外的“油量/步数预算（Gas / Fuel）”参数，我们可以：
1. 保证递归函数在证明助理中能够严格满足结构停机检查；
2. 构造出能够在有限步内直接计算运行的解释器函数；
3. 证明步数索引求值函数与大步操作语义关系之间的**完全等价性**；
4. 借助求值函数的确定性，给出命令大步操作语义确定性定理的一行优雅替代证明！
-/

namespace ImpCEvalFun

open Maps
open Imp
open Imp.com
open Imp.aexp
open Imp.bexp
open ceval

-- #################################################################
-- * 失败的尝试：无步数限制的求值器
-- #################################################################

/-!
### 1. 为什么全函数不能直接解释包含循环的语言？

我们首先尝试直接对命令编写结构递归求值函数。
对于 `skip`、赋值、分号顺序连接和条件分支，一切都运作良好。
然而，当遇到 `while` 循环时，全函数要求每次递归调用的参数结构严格变小。
对于死循环（例如 `while true do skip end`），参数根本不会缩减。
若逻辑系统允许定义不终止的递归函数，将直接导致逻辑不一致（如可以构造出类型为 `False` 的不动点项），彻底破坏证明助理的稳健性。
-/

/-- 第一版尝试：省略 `while` 的不完整求值器（`while` 处仅能伪造返回原状态） -/
def ceval_step1 (st : state) (c : com) : state :=
  match c with
  | CSkip => st
  | CAsgn l a1 => (l !-> aeval st a1; st)
  | CSeq c1 c2 =>
      let st' := ceval_step1 st c1
      ceval_step1 st' c2
  | CIf b c1 c2 =>
      if beval st b then ceval_step1 st c1 else ceval_step1 st c2
  | CWhile _ _ => st  -- 伪造实现，无法真正执行循环

-- #################################################################
-- * 步数索引求值器 (Step-Indexed Evaluator)
-- #################################################################

/-!
### 2. 步数索引（燃料机制）的引入

为了使递归函数良定义，我们向求值器传入一个额外的自然数参数 `i : Nat`，代表允许执行的最大步数预算（Gas / Fuel）：
- 每深入一层求值，步数递减 `1`；
- 当步数耗尽（`0`）时，立即中止求值；
- 此时由于递归参数在 `i` 上严格单调递减，Lean 4 的停机检查器能够瞬间确认函数的全函数性。
-/

/-- 第二版求值器：步数耗尽时返回空状态 `empty_st` -/
def ceval_step2 (st : state) (c : com) (i : Nat) : state :=
  match i with
  | 0 => empty_st
  | i' + 1 =>
    match c with
    | CSkip => st
    | CAsgn l a1 => (l !-> aeval st a1; st)
    | CSeq c1 c2 =>
        let st' := ceval_step2 st c1 i'
        ceval_step2 st' c2 i'
    | CIf b c1 c2 =>
        if beval st b then ceval_step2 st c1 i' else ceval_step2 st c2 i'
    | CWhile b1 c1 =>
        if beval st b1 then
          let st' := ceval_step2 st c1 i'
          ceval_step2 st' c i'
        else st

/-!
### 3. 使用 `Option` 区分正常终止与耗尽终止

`ceval_step2` 的缺陷在于：当结果为 `empty_st` 时，外部无法区分程序是真正计算出了空状态，还是因为步数耗尽异常中止。
为此，我们将返回值提升为 `Option state`：
- `some st'`: 程序在预算步数内正常执行完毕，最终状态为 `st'`；
- `none`: 预算耗尽，程序未能终止。
-/

/-- 第三版求值器：返回 `Option state` 以区分异常耗尽与正常终止 -/
def ceval_step3 (st : state) (c : com) (i : Nat) : Option state :=
  match i with
  | 0 => none
  | i' + 1 =>
    match c with
    | CSkip => some st
    | CAsgn l a1 => some (l !-> aeval st a1; st)
    | CSeq c1 c2 =>
        match ceval_step3 st c1 i' with
        | some st' => ceval_step3 st' c2 i'
        | none => none
    | CIf b c1 c2 =>
        if beval st b then ceval_step3 st c1 i' else ceval_step3 st c2 i'
    | CWhile b1 c1 =>
        if beval st b1 then
          match ceval_step3 st c1 i' with
          | some st' => ceval_step3 st' c i'
          | none => none
        else some st

/-- 标准步数索引求值器 `ceval_step` -/
def ceval_step (st : state) (c : com) (i : Nat) : Option state :=
  match i with
  | 0 => none
  | i' + 1 =>
    match c with
    | CSkip => some st
    | CAsgn l a1 => some (l !-> aeval st a1; st)
    | CSeq c1 c2 =>
        match ceval_step st c1 i' with
        | some st' => ceval_step st' c2 i'
        | none => none
    | CIf b c1 c2 =>
        if beval st b then ceval_step st c1 i' else ceval_step st c2 i'
    | CWhile b1 c1 =>
        if beval st b1 then
          match ceval_step st c1 i' with
          | some st' => ceval_step st' c i'
          | none => none
        else some st

/-!
### 4. 交互式测试求值工具
-/

/-- 设定 500 步运行预算，并在终止后提取 X, Y, Z 三个关键变量的值 -/
def test_ceval (st : state) (c : com) : Option (Nat × Nat × Nat) :=
  match ceval_step st c 500 with
  | none => none
  | some st' => some (st' X, st' Y, st' Z)

/-- 测试示例：顺序赋值与条件分支程序求值 -/
theorem example_test_ceval :
    test_ceval empty_st
      (CSeq (CAsgn X 2)
            (CIf (BLe (AId X) 1)
                 (CAsgn Y 3)
                 (CAsgn Z 4)))
    = some (2, 0, 4) := by
  rfl

/-!
#### 练习：1 星, standard, optional (pup_to_n)

编写一个 Imp 程序，计算从 1 累加到 X 的总和（即 `1 + 2 + ... + X`），并将结果存入变量 Y。
确保你的实现能够通过测试用例 `pup_to_n_1`。
-/

/-- 从 1 累加到 X 的程序实现 -/
def pup_to_n : com :=
  CSeq (CAsgn Y 0)
       (CWhile (BGt (AId X) 0)
               (CSeq (CAsgn Y (APlus (AId Y) (AId X)))
                     (CAsgn X (AMinus (AId X) 1))))

/-- 累加求和测试用例：计算 1 加到 5 等于 15 -/
theorem pup_to_n_1 :
    test_ceval (X !-> 5) pup_to_n
    = some (0, 15, 0) := by
  sorry

/-!
#### 练习：2 星, standard, optional (peven)

编写一个 Imp 程序，若 X 是偶数则将 Z 置为 0，否则将 Z 置为 1。
使用随后的 `peven0` 至 `peven4` 测试用例来验证你的程序。
-/

/-- 奇偶判断程序实现 -/
def peven : com :=
  CSeq (CAsgn Z 0)
       (CWhile (BGt (AId X) 0)
               (CSeq (CIf (BEq (AId Z) 0)
                          (CAsgn Z 1)
                          (CAsgn Z 0))
                     (CAsgn X (AMinus (AId X) 1))))

theorem peven0 : test_ceval (X !-> 0) peven = some (0, 0, 0) := by sorry
theorem peven1 : test_ceval (X !-> 1) peven = some (0, 0, 1) := by sorry
theorem peven2 : test_ceval (X !-> 2) peven = some (0, 0, 0) := by sorry
theorem peven3 : test_ceval (X !-> 3) peven = some (0, 0, 1) := by sorry
theorem peven4 : test_ceval (X !-> 4) peven = some (0, 0, 0) := by sorry

-- #################################################################
-- * 关系语义与步数索引语义的等价性 (Relational vs. Step-Indexed Evaluation)
-- #################################################################

/-!
### 5. 步数索引语义可靠性：步数求值推导关系大步语义

如果存在某个有限步数 `i` 使得 `ceval_step st c i = some st'`，
那么在关系大步语义中必有 `st =[ c ]=> st'`。
-/

/-- 步数索引求值函数的可靠性定理：只要在某步数下终止，则大步语义关系必成立 -/
theorem ceval_step__ceval (c : com) (st st' : state) :
    (∃ i, ceval_step st c i = some st') → st =[ c ]=> st' := by
  intro ⟨i, H⟩
  induction i generalizing c st st' with
  | zero => contradiction
  | succ i' ih =>
    cases c with
    | CSkip =>
      dsimp [ceval_step] at H
      injection H with h
      rw [← h]
      exact E_Skip st
    | CAsgn l a1 =>
      dsimp [ceval_step] at H
      injection H with h
      rw [← h]
      exact E_Asgn st a1 (aeval st a1) l rfl
    | CSeq c1 c2 =>
      dsimp [ceval_step] at H
      cases h1 : ceval_step st c1 i' with
      | none =>
        rw [h1] at H
        contradiction
      | some s =>
        rw [h1] at H
        have h_c1 := ih c1 st s h1
        have h_c2 := ih c2 s st' H
        exact E_Seq c1 c2 st s st' h_c1 h_c2
    | CIf b c1 c2 =>
      dsimp [ceval_step] at H
      split at H
      · rename_i hb
        have h_c1 := ih c1 st st' H
        exact E_IfTrue st st' b c1 c2 hb h_c1
      · rename_i hb
        have h_c2 := ih c2 st st' H
        have hb' : beval st b = false := by
          cases h : beval st b
          · rfl
          · contradiction
        exact E_IfFalse st st' b c1 c2 hb' h_c2
    | CWhile b1 c1 =>
      dsimp [ceval_step] at H
      split at H
      · rename_i hb
        cases h1 : ceval_step st c1 i' with
        | none =>
          rw [h1] at H
          contradiction
        | some s =>
          rw [h1] at H
          have h_c1 := ih c1 st s h1
          have h_cw := ih (CWhile b1 c1) s st' H
          exact E_WhileTrue st s st' b1 c1 hb h_c1 h_cw
      · rename_i hb
        injection H with h
        rw [← h]
        have hb' : beval st b1 = false := by
          cases h : beval st b1
          · rfl
          · contradiction
        exact E_WhileFalse b1 st c1 hb'

/-!
#### 练习：4 星, advanced (ceval_step__ceval_inf)

撰写 `ceval_step__ceval` 定理的非形式化（数学纸笔）证明叙述：
- 对步数 `i` 进行自然数归纳；
- 阐明为什么当 `i = 0` 时矛盾产生；
- 在归纳步中对命令 `c` 进行全情况分析，展示中间状态的构造与归纳假设的应用。
-/

def manual_grade_for_ceval_step__ceval_inf : Option (Nat × String) := none

/-!
### 6. 步数单调性引理

给予求值器更多的计算步数预算，其终止结果保持完全不变（不会改变正常终止的最终状态）。
-/

/-- 步数单调性定理：预算步数增加不影响已求得的正常终止结果 -/
theorem ceval_step_more (i1 i2 : Nat) (st st' : state) (c : com) :
    i1 ≤ i2 →
    ceval_step st c i1 = some st' →
    ceval_step st c i2 = some st' := by
  intro Hle Hceval
  induction i1 generalizing i2 st st' c with
  | zero =>
    dsimp [ceval_step] at Hceval
    contradiction
  | succ i1' ih =>
    cases i2 with
    | zero =>
      omega
    | succ i2' =>
      have Hle' : i1' ≤ i2' := by omega
      cases c with
      | CSkip =>
        dsimp [ceval_step] at Hceval ⊢
        exact Hceval
      | CAsgn l a1 =>
        dsimp [ceval_step] at Hceval ⊢
        exact Hceval
      | CSeq c1 c2 =>
        dsimp [ceval_step] at Hceval ⊢
        cases h1 : ceval_step st c1 i1' with
        | none =>
          rw [h1] at Hceval
          contradiction
        | some s =>
          rw [h1] at Hceval
          have h1' := ih i2' st s c1 Hle' h1
          rw [h1']
          exact ih i2' s st' c2 Hle' Hceval
      | CIf b c1 c2 =>
        dsimp [ceval_step] at Hceval ⊢
        by_cases hb : beval st b = true
        · simp [hb] at Hceval ⊢
          exact ih i2' st st' c1 Hle' Hceval
        · simp [hb] at Hceval ⊢
          exact ih i2' st st' c2 Hle' Hceval
      | CWhile b1 c1 =>
        dsimp [ceval_step] at Hceval ⊢
        by_cases hb : beval st b1 = true
        · simp [hb] at Hceval ⊢
          cases h1 : ceval_step st c1 i1' with
          | none =>
            rw [h1] at Hceval
            contradiction
          | some s =>
            rw [h1] at Hceval
            have h1' := ih i2' st s c1 Hle' h1
            rw [h1']
            exact ih i2' s st' (CWhile b1 c1) Hle' Hceval
        · simp [hb] at Hceval ⊢
          exact Hceval

/-!
#### 练习：3 星, standard, especially useful (ceval__ceval_step)

完成以下完备性定理证明：如果大步语义成立 `st =[ c ]=> st'`，
则必存在足够大的步数预算 `i`，使得 `ceval_step st c i = some st'`。
提示：对大步语义推导证据 `Hce : st =[ c ]=> st'` 进行归纳，在顺序执行和循环场景下结合 `ceval_step_more`。
-/

/-- 步数索引求值函数的完备性定理：只要大步语义能推导出终止，必存在足够步数予以验证 -/
theorem ceval__ceval_step (c : com) (st st' : state) :
    st =[ c ]=> st' →
    ∃ i, ceval_step st c i = some st' := by
  sorry

/-- 大步语义关系与步数索引函数求值的完全等价性 -/
theorem ceval_and_ceval_step_coincide (c : com) (st st' : state) :
    st =[ c ]=> st' ↔ ∃ i, ceval_step st c i = some st' := by
  constructor
  · apply ceval__ceval_step
  · apply ceval_step__ceval

-- #################################################################
-- * 大步语义确定性的又一证明 (Determinism of Evaluation Again)
-- #################################################################

/-!
### 7. 借助函数语义重新证明大步语义的确定性

在 [Imp](/LF/Imp) 中，大步语义的确定性证明 `ceval_deterministic`
需要对复杂的归纳推导结构进行繁重的情况讨论与反演。
现在，借助步数索引求值器的函数性质（函数输出天然是唯一的），结合等价性定理与步数单调性引理，
我们可以给出极其简短优雅的确定性证明！
-/

/-- 大步操作语义的确定性定理（函数化求值替代证明） -/
theorem ceval_deterministic' (c : com) (st st1 st2 : state) :
    st =[ c ]=> st1 →
    st =[ c ]=> st2 →
    st1 = st2 := by
  intro He1 He2
  have ⟨i1, E1⟩ := ceval__ceval_step c st st1 He1
  have ⟨i2, E2⟩ := ceval__ceval_step c st st2 He2
  have E1' := ceval_step_more i1 (i1 + i2) st st1 c (by omega) E1
  have E2' := ceval_step_more i2 (i1 + i2) st st2 c (by omega) E2
  rw [E1'] at E2'
  injection E2'

end ImpCEvalFun
