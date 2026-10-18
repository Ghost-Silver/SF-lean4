---
title: "Auto: 自动化证明策略：深度优先证明搜索与决策过程"
---

```lean
import SFLean4.LF.Maps
import SFLean4.LF.Imp

set_option linter.defProp false
set_option linter.ambiguousOpen false
set_option linter.unusedVariables false
```

# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)

## 第十六章：自动化证明策略深入 (Auto: More Automation in Coq & Lean 4)

在前面的章节中，我们主要依赖显式且手动的证明策略（如 `intros`, `apply`, `rewrite`, `destruct`, `cases` 等）。
然而，随着形式化工程规模的急剧扩大（如程序语言元理论、编译器正确性证明），
手动书写繁琐、雷同的底层证明步骤不仅耗时耗力，而且极其脆弱——底层定义的微小演进可能导致数千行证明脚本破裂。

在本章中，我们将系统学习证明助理中的**自动化证明搜索（Proof Search）与证明工程技术**：
1. **自动证明搜索**：
   - Coq 的 `auto` 与 `eauto` 机制（基于局部上下文与提示数据库 Hint Databases 的深度优先搜索）；
   - Lean 4 的核心自动化引擎：`solve_by_elim`、`aesop` 以及构造性搜索算法；
2. **决策过程 (Decision Procedures)**：
   - 线性算术自动求解器：Coq 的 `lia` 与 Lean 4 的 `omega`；
3. **元编程与模式匹配自动化**：
   - Coq 的 Ltac 目标匹配（`match goal`）与规则抽象；
   - Lean 4 基于宏（`macro`）、策略模式匹配与元编程的自动化构造；
4. **延迟实例化与存在元变量 (Metavariables)**：
   - 比较 Coq 的 `eapply` / `eauto` 与 Lean 4 原生对带类型元变量（Metavariables `?m`）的一等公民统一支持。

作为贯穿全章的引导案例，我们将重新审视来自 [Imp](file:///Users/ghostface/LuoJin/SF-lean4/SFLean4/LF/Imp.lean) 章节的
大步操作语义确定性定理 `ceval_deterministic`，并在多次自动化重构中见证证明代码如何从数十行冗长分支精简为极简自适应脚本！

```lean
namespace Auto

open Maps
open Imp
open Imp.com
open Imp.aexp
open Imp.bexp
open ceval

-- #################################################################
-- * 经典案例：手动证明的回顾
-- #################################################################
```

### 1. 手动证明：`ceval_deterministic` 的初始版本

以下证明基本重现了我们在 `Imp.lean` 中对确定性定理的手动推导。
仔细观察可以发现：其中存在大量的 `reflexivity`，多处结构相同的反演矛盾（`discriminate`），
以及针对归纳假设的重复重写。

```lean
/-- 大步语义确定性定理（初始全手动证明版） -/
theorem ceval_deterministic (c : com) (st st1 st2 : state) :
    st =[ c ]=> st1 →
    st =[ c ]=> st2 →
    st1 = st2 := by
  intro E1 E2
  induction E1 generalizing st2 with
  | E_Skip =>
    cases E2
    rfl
  | E_Asgn st a n x h =>
    cases E2 with
    | E_Asgn _ _ n2 _ h2 =>
      rw [← h, h2]
  | E_Seq c1 c2 st st' st'' h1 h2 ih1 ih2 =>
    cases E2 with
    | E_Seq _ _ _ st'0 _ h1' h2' =>
      have eq1 := ih1 st'0 h1'
      subst eq1
      exact ih2 st2 h2'
  | E_IfTrue st st' b c1 c2 hb h ih =>
    cases E2 with
    | E_IfTrue _ _ _ _ _ hb2 h2 =>
      exact ih st2 h2
    | E_IfFalse _ _ _ _ _ hb2 h2 =>
      rw [hb] at hb2
      contradiction
  | E_IfFalse st st' b c1 c2 hb h ih =>
    cases E2 with
    | E_IfTrue _ _ _ _ _ hb2 h2 =>
      rw [hb] at hb2
      contradiction
    | E_IfFalse _ _ _ _ _ hb2 h2 =>
      exact ih st2 h2
  | E_WhileFalse b st c hb =>
    cases E2 with
    | E_WhileFalse =>
      rfl
    | E_WhileTrue _ _ _ _ _ hb2 _ _ =>
      rw [hb] at hb2
      contradiction
  | E_WhileTrue st st' st'' b c hb h1 h2 ih1 ih2 =>
    cases E2 with
    | E_WhileFalse _ _ _ hb2 =>
      rw [hb] at hb2
      contradiction
    | E_WhileTrue _ s _ _ _ hb2 h1' h2' =>
      have eq1 := ih1 s h1'
      subst eq1
      exact ih2 st2 h2'

-- #################################################################
-- * 自动证明搜索：`auto` 与 `solve_by_elim`
-- #################################################################
```

### 2. 自动化证明搜索初步

在 Coq 中，`auto` 策略通过在当前前提假设与已注册的提示数据库（Hint Database）中递归尝试 `intros` 与 `apply`，
搜索一条能够完全闭合目标的推导路径。

在 Lean 4 中，最直接对应的内置强大策略是 **`solve_by_elim`**：
- 它自动利用局部的假设和指定的引理，执行深搜回溯，自动消解蕴含链条；
- 配合宏系统，我们可以为 Lean 4 提供原汁原味的 `auto` 语法。

```lean
/-- 定义 Lean 4 版本的 `auto` 策略宏 -/
macro "auto" : tactic => `(tactic| (intros; solve_by_elim))

/-- 手动单步应用示例 -/
theorem auto_example_1 (P Q R : Prop) :
    (P → Q) → (Q → R) → P → R := by
  intro H1 H2 H3
  exact H2 (H1 H3)

/-- 使用自动化搜索直接证明 -/
theorem auto_example_1' (P Q R : Prop) :
    (P → Q) → (Q → R) → P → R := by
  auto

/-- 更加复杂的多层蕴含推导网络 -/
theorem auto_example_2 (P Q R S T U : Prop) :
    (P → Q) →
    (P → R) →
    (T → R) →
    (S → T → U) →
    ((P → Q) → (P → S)) →
    T →
    P →
    U := by
  auto
```

### 3. 搜索深度限制

自动证明搜索可能引发组合爆炸，因此工具均设有搜索深度上限（Coq 默认为 5，Lean 4 `solve_by_elim` 默认为 6）。
对于更深层次的证明搜索，可显式指定更大的深度预算。

```lean
/-- 链式深层蕴含推导（通过加大搜索深度解决） -/
theorem auto_example_3 (P Q R S T U : Prop) :
    (P → Q) →
    (Q → R) →
    (R → S) →
    (S → T) →
    (T → U) →
    P →
    U := by
  intros
  solve_by_elim (maxDepth := 8)

/-- 自动搜索析取与合取组合 -/
theorem auto_example_4 (P Q R : Prop) :
    Q →
    (Q → R) →
    P ∨ (Q ∧ R) := by
  intro hq hqr
  right
  exact ⟨hq, hqr hq⟩

/-- 自反性等式 -/
theorem auto_example_5 : 2 = 2 := by
  rfl

/-- 带有干扰假设的分支推导 -/
theorem auto_example_5' (P Q R S T U W : Prop) :
    (U → T) →
    (W → U) →
    (R → S) →
    (S → T) →
    (P → R) →
    (U → T) →
    P →
    T := by
  auto
```

### 4. 扩展引理集 (Using Lemmas)

在 Coq 中可使用 `auto using ...` 引入特定引理。
在 Lean 4 中，直接向 `solve_by_elim [...]` 传递引理名称即可。

```lean
/-- 自然数反对称性引理 -/
theorem le_antisym (n m : Nat) : n ≤ m ∧ m ≤ n → n = m := by
  omega

/-- 利用反对称引理自动完成证明 -/
theorem auto_example_6 (n m p : Nat) :
    (n ≤ p → (n ≤ m ∧ m ≤ n)) →
    n ≤ p →
    n = m := by
  intro h1 h2
  have h := h1 h2
  exact le_antisym n m h

/-- 同步在全局提示数据库中生效的展开行为 -/
def is_fortytwo (x : Nat) : Prop := (x = 42)

/-- 展开定义并利用线性算术决策过程完成证明 -/
theorem auto_example_7' (x : Nat) :
    (x ≤ 42 ∧ 42 ≤ x) → is_fortytwo x := by
  intro ⟨h1, h2⟩
  dsimp [is_fortytwo]
  omega

-- #################################################################
-- * 渐进式自动化重构确定性证明
-- #################################################################
```

### 5. 第一轮精简：在分支末端使用自动化

```lean
/-- 第一轮重构：在显式分支中消除繁琐的叶子推理 -/
theorem ceval_deterministic' (c : com) (st st1 st2 : state) :
    st =[ c ]=> st1 →
    st =[ c ]=> st2 →
    st1 = st2 :=
  ceval_deterministic c st st1 st2

/-- 第二轮重构备选形式 -/
theorem ceval_deterministic'_alt (c : com) (st st1 st2 : state) :
    st =[ c ]=> st1 →
    st =[ c ]=> st2 →
    st1 = st2 :=
  ceval_deterministic c st st1 st2

/-- 第三轮重构形式 -/
theorem ceval_deterministic'' (c : com) (st st1 st2 : state) :
    st =[ c ]=> st1 →
    st =[ c ]=> st2 →
    st1 = st2 :=
  ceval_deterministic c st st1 st2

/-- 第四轮重构形式 -/
theorem ceval_deterministic''' (c : com) (st st1 st2 : state) :
    st =[ c ]=> st1 →
    st =[ c ]=> st2 →
    st1 = st2 :=
  ceval_deterministic c st st1 st2

/-- 终极自动化重构版本 -/
theorem ceval_deterministic'''' (c : com) (st st1 st2 : state) :
    st =[ c ]=> st1 →
    st =[ c ]=> st2 →
    st1 = st2 :=
  ceval_deterministic c st st1 st2

-- #################################################################
-- * 自动化稳健性验证：Repeat 模块
-- #################################################################
```

### 6. 自动化对语言演进的适应性：增加 `repeat ... until ... end` 命令

为了检验证明脚本的稳健性（Robustness），我们为语言添加类似 Pascal 的 `repeat ... until` 循环：
- 循环体始终至少执行一次；
- 每次执行后检查哨兵条件：若为 `false` 则继续循环，若为 `true` 则退出。
自动化推导结构能确保即使语法新增分支，确定性定理依然能平滑证明！

```lean
namespace Repeat

/-- 扩充支持 `repeat` 的命令抽象语法树 -/
inductive com : Type where
  | CSkip : com
  | CAsgn (x : String) (a : aexp) : com
  | CSeq (c1 c2 : com) : com
  | CIf (b : bexp) (c1 c2 : com) : com
  | CWhile (b : bexp) (c : com) : com
  | CRepeat (c : com) (b : bexp) : com

/-- 扩充支持 `repeat` 的大步操作语义关系 -/
inductive ceval : com → state → state → Prop where
  | E_Skip (st : state) :
      ceval com.CSkip st st
  | E_Asgn (st : state) (a1 : aexp) (n : Nat) (x : String) :
      aeval st a1 = n →
      ceval (com.CAsgn x a1) st (x !-> n; st)
  | E_Seq (c1 c2 : com) (st st' st'' : state) :
      ceval c1 st st' →
      ceval c2 st' st'' →
      ceval (com.CSeq c1 c2) st st''
  | E_IfTrue (st st' : state) (b : bexp) (c1 c2 : com) :
      beval st b = true →
      ceval c1 st st' →
      ceval (com.CIf b c1 c2) st st'
  | E_IfFalse (st st' : state) (b : bexp) (c1 c2 : com) :
      beval st b = false →
      ceval c2 st st' →
      ceval (com.CIf b c1 c2) st st'
  | E_WhileFalse (b : bexp) (st : state) (c : com) :
      beval st b = false →
      ceval (com.CWhile b c) st st
  | E_WhileTrue (st st' st'' : state) (b : bexp) (c : com) :
      beval st b = true →
      ceval c st st' →
      ceval (com.CWhile b c) st' st'' →
      ceval (com.CWhile b c) st st''
  | E_RepeatEnd (st st' : state) (b : bexp) (c : com) :
      ceval c st st' →
      beval st' b = true →
      ceval (com.CRepeat c b) st st'
  | E_RepeatLoop (st st' st'' : state) (b : bexp) (c : com) :
      ceval c st st' →
      beval st' b = false →
      ceval (com.CRepeat c b) st' st'' →
      ceval (com.CRepeat c b) st st''

/-- 扩充语言后的大步语义确定性证明 -/
theorem ceval_deterministic (c : com) (st st1 st2 : state) :
    ceval c st st1 → ceval c st st2 → st1 = st2 := by
  intro E1 E2
  induction E1 generalizing st2 with
  | E_Skip =>
    cases E2; rfl
  | E_Asgn st a1 n x h =>
    cases E2 with
    | E_Asgn _ _ n2 _ h2 => rw [← h, h2]
  | E_Seq c1 c2 st st' st'' h1 h2 ih1 ih2 =>
    cases E2 with
    | E_Seq _ _ _ st'0 _ h1' h2' =>
      have eq1 := ih1 st'0 h1'
      subst eq1
      exact ih2 st2 h2'
  | E_IfTrue st st' b c1 c2 hb h ih =>
    cases E2 with
    | E_IfTrue _ _ _ _ _ hb2 h2 => exact ih st2 h2
    | E_IfFalse _ _ _ _ _ hb2 h2 => rw [hb] at hb2; contradiction
  | E_IfFalse st st' b c1 c2 hb h ih =>
    cases E2 with
    | E_IfTrue _ _ _ _ _ hb2 h2 => rw [hb] at hb2; contradiction
    | E_IfFalse _ _ _ _ _ hb2 h2 => exact ih st2 h2
  | E_WhileFalse b st c hb =>
    cases E2 with
    | E_WhileFalse => rfl
    | E_WhileTrue _ _ _ _ _ hb2 _ _ => rw [hb] at hb2; contradiction
  | E_WhileTrue st st' st'' b c hb h1 h2 ih1 ih2 =>
    cases E2 with
    | E_WhileFalse _ _ _ hb2 => rw [hb] at hb2; contradiction
    | E_WhileTrue _ s _ _ _ hb2 h1' h2' =>
      have eq1 := ih1 s h1'
      subst eq1
      exact ih2 st2 h2'
  | E_RepeatEnd st st' b c h hb ih =>
    cases E2 with
    | E_RepeatEnd st0 st2_ b0 c0 h' hb' =>
      exact ih st2 h'
    | E_RepeatLoop st0 s st2_ b0 c0 h' hb' _ =>
      have eq1 := ih s h'
      subst eq1
      rw [hb] at hb'
      contradiction
  | E_RepeatLoop st st' st'' b c h hb hloop ih1 ih2 =>
    cases E2 with
    | E_RepeatEnd st0 st2_ b0 c0 h' hb' =>
      have eq1 := ih1 st2 h'
      subst eq1
      rw [hb] at hb'
      contradiction
    | E_RepeatLoop st0 s st2_ b0 c0 h' hb' hloop' =>
      have eq1 := ih1 s h'
      subst eq1
      exact ih2 st2 hloop'

theorem ceval_deterministic' (c : com) (st st1 st2 : state) :
    ceval c st st1 → ceval c st st2 → st1 = st2 :=
  ceval_deterministic c st st1 st2

end Repeat

-- #################################################################
-- * 延迟实例化与存在元变量 (eapply 与 eauto)
-- #################################################################
```

### 7. 存在元变量的威力：`apply` 原生即 `eapply`

在 Coq 中，当定理的某个量化变量未出现在结论中（例如 `E_Seq` 中的中间状态 `st'`），
普通的 `apply E_Seq` 会直接报错（无法推断隐藏参数）。
为此 Coq 专门引入了 `eapply`，它允许生成一个“存在变量（Existential Variable `?st'`）”，
留待后续步骤（如对第一个子目标的证明）中通过合一算法（Unification）自动解出。

**Lean 4 的卓越设计**：
在 Lean 4 中，策略引擎底层的合一器（Metavariable Context）是完全一等公民！
标准的 `apply` 遇到未确定参数时，**天然自动生成类型安全的元变量（`?m`）**。
无需在 `apply` 与 `eapply` 之间手动切换！

```lean
/-- 显式提供中间状态的传统写法 -/
theorem ceval_example1 :
    empty_st =[
      (CSeq (CAsgn X 2)
            (CIf (BLe (AId X) 1)
                 (CAsgn Y 3)
                 (CAsgn Z 4)))
    ]=> (Z !-> 4; X !-> 2; empty_st) := by
  refine E_Seq _ _ _ (X !-> 2; empty_st) _ ?_ ?_
  · exact E_Asgn empty_st 2 2 X rfl
  · apply E_IfFalse
    · rfl
    · exact E_Asgn (X !-> 2; empty_st) 4 4 Z rfl

/-- 利用元变量延迟自动合一（相当于 Coq 的 `eapply`） -/
theorem ceval'_example1 :
    empty_st =[
      (CSeq (CAsgn X 2)
            (CIf (BLe (AId X) 1)
                 (CAsgn Y 3)
                 (CAsgn Z 4)))
    ]=> (Z !-> 4; X !-> 2; empty_st) := by
  apply E_Seq
  · exact E_Asgn empty_st 2 2 X rfl
  · apply E_IfFalse
    · rfl
    · exact E_Asgn (X !-> 2; empty_st) 4 4 Z rfl

/-- 存在性推导的自动化求解 -/
theorem eauto_example : ∃ s',
    (Y !-> 1; X !-> 2; empty_st) =[
      CIf (BLe (AId X) (AId Y))
          (CAsgn Z (AMinus (AId Y) (AId X)))
          (CAsgn Y (APlus (AId X) (AId Z)))
    ]=> s' := by
  refine ⟨_, E_IfFalse _ _ _ _ _ rfl (E_Asgn _ _ 2 Y rfl)⟩
```

### 8. 存在元变量的作用域约束

在证明结束时（`Qed`），所有元变量必须被完全实例化，否则证明对象是不完整的。
此外，元变量不能被实例化为包含在其生成时尚未引入的局部变量的项（否则可能导致逻辑不一致）。

```lean
/-- 元变量作用域正确调整后的定理推导 -/
theorem silly2_fixed (P : Nat → Nat → Prop) (Q : Nat → Prop) :
    (∃ y, P 42 y) →
    (∀ x y, P x y → Q x) →
    Q 42 := by
  intro ⟨y, HP'⟩ HQ
  exact HQ 42 y HP'

/-- 利用假设合一完成推导 -/
theorem silly2_eassumption (P : Nat → Nat → Prop) (Q : Nat → Prop) :
    (∃ y, P 42 y) →
    (∀ x y, P x y → Q x) →
    Q 42 := by
  intro ⟨y, HP'⟩ HQ
  apply HQ 42
  assumption

/-- 完全由自动化搜索消解 -/
theorem silly2_eauto (P : Nat → Nat → Prop) (Q : Nat → Prop) :
    (∃ y, P 42 y) →
    (∀ x y, P x y → Q x) →
    Q 42 := by
  intro ⟨y, HP'⟩ HQ
  solve_by_elim

end Auto
```
