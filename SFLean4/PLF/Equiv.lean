import SFLean4.LF.Basics
import SFLean4.LF.Induction
import SFLean4.LF.Maps
import SFLean4.LF.Imp

set_option linter.defProp false
set_option linter.ambiguousOpen false
set_option linter.unusedVariables false

/-!
# 《软件基础》(Software Foundations) 卷二：程序语言基础 (PLF)

## 第一章：程序等价性 (Equiv: Program Equivalence)

在卷一《逻辑基础》(LF) 的 [Imp](/LF/Imp) 章节中，
我们形式化定义了简单命令式语言 Imp 的语法以及基于大步操作语义（Big-Step Operational Semantics）的求值关系 `st =[ c ]=> st'`。
在那个阶段，我们关注的是单个具体程序的执行与性质验证（例如证明阶乘程序的正确性、大步语义与小步函数求值的一致性等）。

然而，在编译器工程、程序分析与程序逻辑中，一个更为根本和核心的问题是：**两个程序何时在行为上是不可区分的？**
更进一步：
- 编译器进行死代码消除、常量折叠、公共子表达式消除或循环展开等变换时，如何严格证明这些优化没有改变程序的原始语义？
- 当程序中引入非确定性（Non-determinism，如 C 语言中未指定的表达式求值顺序、并发交错或随机赋值）时，等价性的概念又将如何拓展？

本章将系统研究程序的形式化**行为等价性（Behavioral Equivalence）**及其代数性质：
1. **算术表达式、布尔表达式与命令的等价性定义**：
   - 表达式等价：在任意初始状态下均求值到相同的结果；
   - 命令等价：在任意给定的初始状态下，两个命令要么同时发散（Diverge），要么均终止并产生完全一致的最终状态。
2. **等价关系的代数性质**：
   - 自反性、对称性与传递性；
   - **同余性（Congruence Property）**：局部程序的等价性保证了包含它们的复合程序整体等价性，这使得编译器优化的局部模块化证明成为可能。
3. **程序优化变换的可靠性验证（Soundness of Program Transformations）**：
   - 常量折叠变换（Constant Folding）；
   - 代数恒等式消除（0 + n 消除）；
   - 复合优化器的构造与链式可靠性传递。
4. **程序不等价性的证明反例构造**：
   - 变量替换的不等价反例；
   - 依赖分析与无干扰赋值交换条件。
5. **拓展案例：非确定性语言 Himp（Imp with HAVOC）**：
   - 形式化非确定性大步操作语义；
   - 非确定性程序等价性的微妙边界（如发散与任意值的交互）。
6. **程序近似关系（Program Approximation）**：
   - 模拟与单向精化关系。
-/

namespace PLF.Equiv

open Maps
open Imp
open Imp.aexp
open Imp.bexp
open Imp.com
open ceval

-- #################################################################
-- * 1. 行为等价性的定义 (Behavioral Equivalence)
-- #################################################################

/-!
### 1.1 表达式等价性

对于包含程序状态变量的算术表达式 `aexp` 与布尔表达式 `bexp`，
如果两个表达式在**任意可能的状态**下进行求值，产生的结果都完全相等，
则称它们是行为等价的。
-/

/-- 算术表达式行为等价定义：在所有程序状态下求值结果均相等 -/
def aequiv (a1 a2 : aexp) : Prop :=
  ∀ st : state, aeval st a1 = aeval st a2

/-- 布尔表达式行为等价定义：在所有程序状态下求值结果均相等 -/
def bequiv (b1 b2 : bexp) : Prop :=
  ∀ st : state, beval st b1 = beval st b2

/-- 算术表达式等价符号记号 -/
scoped notation:50 a1:51 " ==a " a2:51 => aequiv a1 a2
/-- 布尔表达式等价符号记号 -/
scoped notation:50 b1:51 " ==b " b2:51 => bequiv b1 b2

/-!
例如：
- `X - X` 与 `0` 在算术上等价；
- `X - X = 0` 与 `true` 在布尔意义上等价。
-/

/-- 算术表达式等价简单示例：X - X 等价于 0 -/
theorem aequiv_example : (AMinus (AId X) (AId X)) ==a (ANum 0) := by
  intro st
  dsimp [aeval]
  omega

/-- 布尔表达式等价简单示例：(X - X = 0) 等价于 true -/
theorem bequiv_example : (BEq (AMinus (AId X) (AId X)) (ANum 0)) ==b BTrue := by
  intro st
  dsimp [beval, aeval]
  have : st X - st X = 0 := by omega
  simp [this]

/-!
### 1.2 命令等价性

对于命令 `com`，情况要比纯表达式更加微妙。
由于 Imp 语言具有图灵完备的 `while` 循环，某些命令在某些初始状态下可能永远不会停机（即发散）。
因此，我们不能简单地要求“两个命令在同一初始状态下求出的最终状态相同”，因为可能根本不存在最终状态！

正确的定义是：
两个命令行为等价，当且仅当对于任意给定的起始状态 `st`，
“第一个命令能执行终止于 `st'`” 与 “第二个命令能执行终止于 `st'`” 是**充分必要**的。
这意味着它们要么以完全相同的最终状态停机，要么均无限循环发散。
-/

/-- 命令行为等价定义：对于任意初态与末态，大步语义关系完全双向等价 -/
def cequiv (c1 c2 : com) : Prop :=
  ∀ st st' : state, (st =[ c1 ]=> st') ↔ (st =[ c2 ]=> st')

/-- 命令等价符号记号 -/
scoped notation:50 c1:51 " ==c " c2:51 => cequiv c1 c2

-- #################################################################
-- * 2. 基础等价定理与练习 (Simple Examples)
-- #################################################################

/-!
### 2.1 关于 `SKIP` 的等价性

最简单的等价性涉及空命令 `SKIP`。
-/

/-- 左侧消除 SKIP：(SKIP ;; c) 行为等价于 c -/
theorem skip_left (c : com) : (SKIP ;; c) ==c c := by
  intro st st'
  constructor
  · intro h
    cases h with
    | E_Seq _ _ _ _ _ h1 h2 =>
      cases h1
      exact h2
  · intro h
    apply E_Seq com.CSkip c st st st'
    · exact E_Skip st
    · exact h

/-!
#### 练习：2 星, standard (skip_right)

证明右侧消除 `SKIP` 同样保持行为等价。
-/

theorem skip_right (c : com) : (c ;; SKIP) ==c c := by
  sorry

/-!
### 2.2 关于条件分支 `TEST` 的等价性
-/

/-- 条件恒为 True 时的简单化简 -/
theorem if_true_simple (c1 c2 : com) : (TEST BTrue THEN c1 ELSE c2 FI) ==c c1 := by
  intro st st'
  constructor
  · intro h
    cases h with
    | E_IfTrue _ _ _ _ _ _ h2 => exact h2
    | E_IfFalse _ _ _ _ _ h1 _ => contradiction
  · intro h
    apply E_IfTrue
    · rfl
    · exact h

/-- 条件表达式行为等价于 BTrue 时的通用化简 -/
theorem if_true (b : bexp) (c1 c2 : com) (hb : b ==b BTrue) :
    (TEST b THEN c1 ELSE c2 FI) ==c c1 := by
  intro st st'
  constructor
  · intro h
    cases h with
    | E_IfTrue _ _ _ _ _ _ h2 => exact h2
    | E_IfFalse _ _ _ _ _ h1 _ =>
      have hb_st := hb st
      dsimp [beval] at hb_st
      rw [h1] at hb_st
      contradiction
  · intro h
    apply E_IfTrue
    · exact hb st
    · exact h

/-!
#### 练习：2 星, standard, especially useful (if_false)

当条件表达式行为等价于 `BFalse` 时，条件分支等价于 `else` 分支。
-/

theorem if_false (b : bexp) (c1 c2 : com) (hb : b ==b BFalse) :
    (TEST b THEN c1 ELSE c2 FI) ==c c2 := by
  sorry

/-!
#### 练习：3 星, standard (swap_if_branches)

如果同时取反条件表达式，我们可以安全地交换条件分支的 then 与 else 两个子分支。
-/

theorem swap_if_branches (b : bexp) (c1 c2 : com) :
    (TEST b THEN c1 ELSE c2 FI) ==c (TEST (BNot b) THEN c2 ELSE c1 FI) := by
  sorry

/-!
### 2.3 关于循环 `WHILE` 的等价性

一个守卫条件恒为假的循环，等价于直接执行 `SKIP`；
而一个守卫条件恒为真的循环，则永远不会停机。
-/

/-- 循环守卫恒为假时，循环等价于 SKIP -/
theorem while_false (b : bexp) (c : com) (hb : b ==b BFalse) :
    (WHILE b DO c END) ==c SKIP := by
  intro st st'
  constructor
  · intro h
    cases h with
    | E_WhileFalse _ _ _ h1 => exact E_Skip st
    | E_WhileTrue _ _ _ _ _ h1 _ _ =>
      have hb_st := hb st
      dsimp [beval] at hb_st
      rw [h1] at hb_st
      contradiction
  · intro h
    cases h
    apply E_WhileFalse b st c
    exact hb st

/-!
#### 练习：2 星, advanced, optional (while_false_informal)

请用自然语言形式给出 `while_false` 定理的非形式化证明思路：
根据大步语义规则，当循环求值时只有两种可能的推导规则：
若最后一步应用 `E_WhileFalse`，则初态即末态，等价于 `E_Skip`；
若最后一步应用 `E_WhileTrue`，则要求守卫条件在初态下求值为 `true`，这与守卫等价于 `BFalse` 的假设矛盾。
反向推导同样显然。
-/

/-- 辅助引理：守卫恒为 True 的循环永不停机（无终止状态） -/
theorem while_true_nonterm (b : bexp) (c : com) (st st' : state) (hb : b ==b BTrue) :
    ¬ (st =[ WHILE b DO c END ]=> st') := by
  intro h
  generalize hcw : (WHILE b DO c END) = cw
  rw [hcw] at h
  induction h generalizing b c with
  | E_Skip => contradiction
  | E_Asgn => contradiction
  | E_Seq => contradiction
  | E_IfTrue => contradiction
  | E_IfFalse => contradiction
  | E_WhileFalse bf st_f cf hbf =>
    injection hcw with h1 h2
    subst h1 h2
    have hb_st := hb st_f
    dsimp [beval] at hb_st
    rw [hbf] at hb_st
    contradiction
  | E_WhileTrue st_t st_m st_end bt ct hbt h1 h2 ih1 ih2 =>
    injection hcw with h1_eq h2_eq
    subst h1_eq h2_eq
    exact ih2 b c hb rfl

/-!
#### 练习：2 星, standard, optional (while_true_nonterm_informal)

解释引理 `while_true_nonterm` 在语义层面的直观含义：
若循环条件在任意状态下均恒真，则不存在任何有限的大步操作语义推导树能够从任意初态到达终态。
-/

/-!
#### 练习：2 星, standard, especially useful (while_true)

证明守卫恒真的循环与标准死循环 `WHILE BTrue DO SKIP END` 行为等价。
-/

theorem while_true (b : bexp) (c : com) (hb : b ==b BTrue) :
    (WHILE b DO c END) ==c (WHILE BTrue DO SKIP END) := by
  sorry

/-- 循环展开定理 (Loop Unrolling)：
    将循环体展开一次并由条件分支守卫，不改变程序语义。 -/
theorem loop_unrolling (b : bexp) (c : com) :
    (WHILE b DO c END) ==c (TEST b THEN (c ;; WHILE b DO c END) ELSE SKIP FI) := by
  intro st st'
  constructor
  · intro h
    cases h with
    | E_WhileFalse _ _ _ h1 =>
      apply E_IfFalse
      · exact h1
      · exact E_Skip st
    | E_WhileTrue _ st_mid _ _ _ h1 h2 h3 =>
      apply E_IfTrue
      · exact h1
      · exact E_Seq c (WHILE b DO c END) st st_mid st' h2 h3
  · intro h
    cases h with
    | E_IfTrue _ _ _ _ _ h1 h2 =>
      cases h2 with
      | E_Seq _ _ _ st_mid _ h21 h22 =>
        exact E_WhileTrue st st_mid st' b c h1 h21 h22
    | E_IfFalse _ _ _ _ _ h1 h2 =>
      cases h2
      exact E_WhileFalse b st c h1

/-!
#### 练习：2 星, standard, optional (seq_assoc)

证明顺序复合算子的结合律：`((c1 ;; c2) ;; c3)` 等价于 `(c1 ;; (c2 ;; c3))`。
-/

theorem seq_assoc (c1 c2 c3 : com) :
    ((c1 ;; c2) ;; c3) ==c (c1 ;; (c2 ;; c3)) := by
  sorry

/-!
### 2.4 涉及赋值与程序状态外延性的等价性
-/

/-- 自赋值恒等消除：将变量赋值给自身的语句 x := x 行为等价于 SKIP -/
theorem identity_assignment (x : String) : (x ::= AId x) ==c SKIP := by
  intro st st'
  constructor
  · intro h
    cases h with
    | E_Asgn _ _ n _ hn =>
      dsimp [aeval] at hn
      subst hn
      rw [t_update_same]
      exact E_Skip st
  · intro h
    cases h
    have h_asgn : st =[ x ::= AId x ]=> (x !-> st x; st) := by
      apply E_Asgn
      rfl
    rw [t_update_same] at h_asgn
    exact h_asgn

/-!
#### 练习：2 星, standard, especially useful (assign_aequiv)

若表达式 `a` 与变量 `X` 在任意状态下的求值结果完全相等，
则将 `a` 赋给 `X` 的语句与 `SKIP` 行为等价。
-/

theorem assign_aequiv (X : String) (a : aexp) (ha : (AId X) ==a a) :
    SKIP ==c (X ::= a) := by
  sorry

/-!
#### 练习：2 星, standard, optional (equiv_classes)

给定以下 9 个 Imp 程序，将彼此行为等价的程序分组为等价类列表。
-/

def prog_a : com := (WHILE (BGt (AId X) (ANum 0)) DO (X ::= AId X + ANum 1) END)
def prog_b : com :=
  (TEST (BEq (AId X) (ANum 0))
   THEN ((X ::= AId X + ANum 1) ;; (Y ::= ANum 1))
   ELSE (Y ::= ANum 0) FI) ;;
  (X ::= AId X - AId Y) ;;
  (Y ::= ANum 0)
def prog_c : com := SKIP
def prog_d : com := (WHILE (BNeq (AId X) (ANum 0)) DO (X ::= (AId X * AId Y) + ANum 1) END)
def prog_e : com := (Y ::= ANum 0)
def prog_f : com :=
  (Y ::= AId X + ANum 1) ;;
  (WHILE (BNeq (AId X) (AId Y)) DO (Y ::= AId X + ANum 1) END)
def prog_g : com := (WHILE BTrue DO SKIP END)
def prog_h : com := (WHILE (BNeq (AId X) (AId X)) DO (X ::= AId X + ANum 1) END)
def prog_i : com := (WHILE (BNeq (AId X) (AId Y)) DO (X ::= AId Y + ANum 1) END)

def equiv_classes : List (List com) :=
  [[prog_a, prog_d], [prog_b, prog_e], [prog_c, prog_h], [prog_f, prog_g], [prog_i]]

def manual_grade_for_equiv_classes : Option (Nat × String) := none

-- #################################################################
-- * 3. 行为等价性的代数性质 (Properties of Behavioral Equivalence)
-- #################################################################

/-!
### 3.1 等价关系基本性质（自反、对称、传递）
-/

theorem refl_aequiv (a : aexp) : a ==a a := by
  intro st; rfl

theorem sym_aequiv (a1 a2 : aexp) (h : a1 ==a a2) : a2 ==a a1 := by
  intro st; exact (h st).symm

theorem trans_aequiv (a1 a2 a3 : aexp) (h12 : a1 ==a a2) (h23 : a2 ==a a3) : a1 ==a a3 := by
  intro st; rw [h12 st, h23 st]

theorem refl_bequiv (b : bexp) : b ==b b := by
  intro st; rfl

theorem sym_bequiv (b1 b2 : bexp) (h : b1 ==b b2) : b2 ==b b1 := by
  intro st; exact (h st).symm

theorem trans_bequiv (b1 b2 b3 : bexp) (h12 : b1 ==b b2) (h23 : b2 ==b b3) : b1 ==b b3 := by
  intro st; rw [h12 st, h23 st]

theorem refl_cequiv (c : com) : c ==c c := by
  intro st st'; rfl

theorem sym_cequiv (c1 c2 : com) (h : c1 ==c c2) : c2 ==c c1 := by
  intro st st'; exact (h st st').symm

theorem trans_cequiv (c1 c2 c3 : com) (h12 : c1 ==c c2) (h23 : c2 ==c c3) : c1 ==c c3 := by
  intro st st'; rw [h12 st st', h23 st st']

/-!
### 3.2 行为等价性是同余关系 (Congruence)

行为等价性不仅是一个等价关系，更是各个语法构造器上的**同余关系**。
即：如果子程序是等价的，那么将子程序替换后得到的更大复合程序整体也是等价的。
这一性质对于现代编译器具有至关重要的意义：
它允许编译器针对程序的局部微小结构进行优化，而无需重新分析程序其余未经修改的部分。
-/

/-- 赋值语句对算术表达式等价的同余性 -/
theorem CAsgn_congruence (x : String) (a a' : aexp) (heqv : a ==a a') :
    (x ::= a) ==c (x ::= a') := by
  intro st st'
  constructor
  · intro h
    cases h with
    | E_Asgn _ _ n _ hn =>
      subst hn
      apply E_Asgn
      rw [← heqv]
  · intro h
    cases h with
    | E_Asgn _ _ n _ hn =>
      subst hn
      apply E_Asgn
      rw [heqv]

/-- 循环语句对条件和循环体等价的同余性 -/
theorem CWhile_congruence (b b' : bexp) (c c' : com) (hb : b ==b b') (hc : c ==c c') :
    (WHILE b DO c END) ==c (WHILE b' DO c' END) := by
  have A : ∀ (b_1 b_2 : bexp) (c_1 c_2 : com) (st st' : state),
      b_1 ==b b_2 → c_1 ==c c_2 → (st =[ WHILE b_1 DO c_1 END ]=> st') → (st =[ WHILE b_2 DO c_2 END ]=> st') := by
    intro b_1 b_2 c_1 c_2 st_1 st_2 hbe hce h_ev
    generalize hcw : (WHILE b_1 DO c_1 END) = cw
    rw [hcw] at h_ev
    induction h_ev generalizing b_1 b_2 c_1 c_2 with
    | E_Skip => contradiction
    | E_Asgn => contradiction
    | E_Seq => contradiction
    | E_IfTrue => contradiction
    | E_IfFalse => contradiction
    | E_WhileFalse bf st_f cf hbf =>
      injection hcw with h1 h2
      subst h1 h2
      apply E_WhileFalse b_2 st_f c_2
      rw [← hbe]
      exact hbf
    | E_WhileTrue st_t st_m st_end bt ct hbt hstep hrest ih1 ih2 =>
      injection hcw with h1 h2
      subst h1 h2
      apply E_WhileTrue st_t st_m st_end b_2 c_2
      · rw [← hbe]; exact hbt
      · rw [← hce st_t st_m]; exact hstep
      · exact ih2 b_1 b_2 c_1 c_2 hbe hce rfl
  intro st st'
  constructor
  · exact A b b' c c' st st' hb hc
  · exact A b' b c' c st st' (sym_bequiv b b' hb) (sym_cequiv c c' hc)

/-!
#### 练习：3 星, standard, optional (CSeq_congruence)

证明顺序复合语句在两子命令分别等价下的同余性。
-/

theorem CSeq_congruence (c1 c1' c2 c2' : com) (h1 : c1 ==c c1') (h2 : c2 ==c c2') :
    (c1 ;; c2) ==c (c1' ;; c2') := by
  sorry

/-!
#### 练习：3 星, standard (CIf_congruence)

证明条件分支语句在条件表达式与两分支分别等价下的同余性。
-/

theorem CIf_congruence (b b' : bexp) (c1 c1' c2 c2' : com)
    (hb : b ==b b') (h1 : c1 ==c c1') (h2 : c2 ==c c2') :
    (TEST b THEN c1 ELSE c2 FI) ==c (TEST b' THEN c1' ELSE c2' FI) := by
  sorry

/-- 利用同余定理证明复合程序等价性的典范用例 -/
theorem congruence_example :
    ((X ::= ANum 0) ;;
     (TEST (BEq (AId X) (ANum 0))
      THEN (Y ::= ANum 0)
      ELSE (Y ::= ANum 42) FI)) ==c
    ((X ::= ANum 0) ;;
     (TEST (BEq (AId X) (ANum 0))
      THEN (Y ::= AMinus (AId X) (AId X))
      ELSE (Y ::= ANum 42) FI)) := by
  apply CSeq_congruence
  · exact refl_cequiv (X ::= ANum 0)
  · apply CIf_congruence
    · exact refl_bequiv (BEq (AId X) (ANum 0))
    · apply CAsgn_congruence
      intro st
      dsimp [aeval]
      omega
    · exact refl_cequiv (Y ::= ANum 42)

/-!
#### 练习：3 星, advanced (not_congr)

是否能构造出一种命令之间的二元关系，它是等价关系（自反、对称、传递），但**不是同余关系**？
例如：命令长度相等关系、或者在某一特定固定状态下产生相同输出的关系。
-/

def manual_grade_for_not_congr : Option (Nat × String) := none

-- #################################################################
-- * 4. 程序变换及其可靠性 (Program Transformations)
-- #################################################################

/-!
### 4.1 程序变换可靠性的形式化定义

一个程序变换如果能保持原程序的语义行为不变，就称其为**可靠的（Sound）**。
-/

def atrans_sound (atrans : aexp → aexp) : Prop :=
  ∀ a : aexp, aequiv a (atrans a)

def btrans_sound (btrans : bexp → bexp) : Prop :=
  ∀ b : bexp, bequiv b (btrans b)

def ctrans_sound (ctrans : com → com) : Prop :=
  ∀ c : com, cequiv c (ctrans c)

/-!
### 4.2 常量折叠变换 (Constant Folding)
-/

/-- 算术表达式常量折叠变换 -/
def fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | .ANum n => .ANum n
  | .AId x => .AId x
  | .APlus a1 a2 =>
    match fold_constants_aexp a1, fold_constants_aexp a2 with
    | .ANum n1, .ANum n2 => .ANum (n1 + n2)
    | a1', a2' => .APlus a1' a2'
  | .AMinus a1 a2 =>
    match fold_constants_aexp a1, fold_constants_aexp a2 with
    | .ANum n1, .ANum n2 => .ANum (n1 - n2)
    | a1', a2' => .AMinus a1' a2'
  | .AMult a1 a2 =>
    match fold_constants_aexp a1, fold_constants_aexp a2 with
    | .ANum n1, .ANum n2 => .ANum (n1 * n2)
    | a1', a2' => .AMult a1' a2'

theorem fold_aexp_ex1 : fold_constants_aexp (.AMult (.APlus (.ANum 1) (.ANum 2)) (.AId X)) =
    .AMult (.ANum 3) (.AId X) := rfl

theorem fold_aexp_ex2 : fold_constants_aexp (.AMinus (.AId X) (.APlus (.AMult (.ANum 0) (.ANum 6)) (.AId Y))) =
    .AMinus (.AId X) (.APlus (.ANum 0) (.AId Y)) := rfl

/-- 布尔表达式常量折叠变换 -/
def fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | .BTrue => .BTrue
  | .BFalse => .BFalse
  | .BEq a1 a2 =>
    match fold_constants_aexp a1, fold_constants_aexp a2 with
    | .ANum n1, .ANum n2 => if n1 == n2 then .BTrue else .BFalse
    | a1', a2' => .BEq a1' a2'
  | .BNeq a1 a2 =>
    match fold_constants_aexp a1, fold_constants_aexp a2 with
    | .ANum n1, .ANum n2 => if !(n1 == n2) then .BTrue else .BFalse
    | a1', a2' => .BNeq a1' a2'
  | .BLe a1 a2 =>
    match fold_constants_aexp a1, fold_constants_aexp a2 with
    | .ANum n1, .ANum n2 => if n1 <= n2 then .BTrue else .BFalse
    | a1', a2' => .BLe a1' a2'
  | .BGt a1 a2 =>
    match fold_constants_aexp a1, fold_constants_aexp a2 with
    | .ANum n1, .ANum n2 => if n1 > n2 then .BTrue else .BFalse
    | a1', a2' => .BGt a1' a2'
  | .BNot b1 =>
    match fold_constants_bexp b1 with
    | .BTrue => .BFalse
    | .BFalse => .BTrue
    | b1' => .BNot b1'
  | .BAnd b1 b2 =>
    match fold_constants_bexp b1, fold_constants_bexp b2 with
    | .BTrue, .BTrue => .BTrue
    | .BTrue, .BFalse => .BFalse
    | .BFalse, .BTrue => .BFalse
    | .BFalse, .BFalse => .BFalse
    | b1', b2' => .BAnd b1' b2'

theorem fold_bexp_ex1 : fold_constants_bexp (.BAnd .BTrue (.BNot (.BAnd .BFalse .BTrue))) = .BTrue := rfl

theorem fold_bexp_ex2 : fold_constants_bexp (.BAnd (.BEq (.AId X) (.AId Y))
    (.BEq (.ANum 0) (.AMinus (.ANum 2) (.APlus (.ANum 1) (.ANum 1))))) =
    (.BAnd (.BEq (.AId X) (.AId Y)) .BTrue) := rfl

/-- 命令常量折叠优化器：消除已知恒真/恒假分支，以及折叠赋值与循环条件中的常量 -/
def fold_constants_com (c : com) : com :=
  match c with
  | .CSkip => .CSkip
  | .CAsgn x a => .CAsgn x (fold_constants_aexp a)
  | .CSeq c1 c2 => .CSeq (fold_constants_com c1) (fold_constants_com c2)
  | .CIf b c1 c2 =>
    match fold_constants_bexp b with
    | .BTrue => fold_constants_com c1
    | .BFalse => fold_constants_com c2
    | b' => .CIf b' (fold_constants_com c1) (fold_constants_com c2)
  | .CWhile b c1 =>
    match fold_constants_bexp b with
    | .BTrue => .CWhile .BTrue .CSkip
    | .BFalse => .CSkip
    | b' => .CWhile b' (fold_constants_com c1)

theorem fold_com_ex1 :
  fold_constants_com
    ((X ::= (ANum 4 + ANum 5)) ;;
     (Y ::= (AId X - ANum 3)) ;;
     (TEST (BEq (AId X - AId Y) (ANum 2 + ANum 4)) THEN SKIP ELSE (Y ::= ANum 0) FI) ;;
     (TEST (BLe (ANum 0) (ANum 4 - (ANum 2 + ANum 1))) THEN (Y ::= ANum 0) ELSE SKIP FI) ;;
     (WHILE (BEq (AId Y) (ANum 0)) DO (X ::= AId X + ANum 1) END)) =
    ((X ::= ANum 9) ;;
     (Y ::= (AId X - ANum 3)) ;;
     (TEST (BEq (AId X - AId Y) (ANum 6)) THEN SKIP ELSE (Y ::= ANum 0) FI) ;;
     (Y ::= ANum 0) ;;
     (WHILE (BEq (AId Y) (ANum 0)) DO (X ::= AId X + ANum 1) END)) := rfl

/-!
### 4.3 常量折叠的可靠性证明
-/

/-- 算术表达式常量折叠的可靠性 -/
theorem fold_constants_aexp_sound : atrans_sound fold_constants_aexp := by
  intro a st
  induction a with
  | ANum n => rfl
  | AId x => rfl
  | APlus a1 a2 ih1 ih2 =>
    dsimp [fold_constants_aexp, aeval]
    rw [ih1, ih2]
    split <;> (try simp_all; try rfl)
  | AMinus a1 a2 ih1 ih2 =>
    dsimp [fold_constants_aexp, aeval]
    rw [ih1, ih2]
    split <;> (try simp_all; try rfl)
  | AMult a1 a2 ih1 ih2 =>
    dsimp [fold_constants_aexp, aeval]
    rw [ih1, ih2]
    split <;> (try simp_all; try rfl)

/-!
#### 练习：3 星, standard, optional (fold_bexp_Eq_informal)

非形式化叙述 `fold_constants_bexp` 在 `BEq` 与 `BLe` 各种情况下的可靠性证明逻辑。
-/

/-- 布尔表达式常量折叠的可靠性 -/
theorem fold_constants_bexp_sound : btrans_sound fold_constants_bexp := by
  intro b st
  induction b with
  | BTrue => rfl
  | BFalse => rfl
  | BEq a1 a2 =>
    dsimp [fold_constants_bexp, beval]
    rw [fold_constants_aexp_sound a1 st, fold_constants_aexp_sound a2 st]
    split
    · rename_i n1 n2 heq1 heq2
      rw [heq1, heq2]
      dsimp [aeval, beval]
      split <;> rename_i h
      · simp [h, beval]
      · simp [h, beval]
    · rfl
  | BNeq a1 a2 =>
    dsimp [fold_constants_bexp, beval]
    rw [fold_constants_aexp_sound a1 st, fold_constants_aexp_sound a2 st]
    split
    · rename_i n1 n2 heq1 heq2
      rw [heq1, heq2]
      dsimp [aeval, beval]
      split <;> rename_i h
      · simp [h, beval]
      · simp [h, beval]
    · rfl
  | BLe a1 a2 =>
    dsimp [fold_constants_bexp, beval]
    rw [fold_constants_aexp_sound a1 st, fold_constants_aexp_sound a2 st]
    split
    · rename_i n1 n2 heq1 heq2
      rw [heq1, heq2]
      dsimp [aeval, beval]
      split <;> rename_i h
      · simp [h, beval]
      · simp [h, beval]
    · rfl
  | BGt a1 a2 =>
    dsimp [fold_constants_bexp, beval]
    rw [fold_constants_aexp_sound a1 st, fold_constants_aexp_sound a2 st]
    split
    · rename_i n1 n2 heq1 heq2
      rw [heq1, heq2]
      dsimp [aeval, beval]
      split <;> rename_i h
      · have : ¬(n1 ≤ n2) := by omega
        simp [this, beval]
      · have : n1 ≤ n2 := by omega
        simp [this, beval]
    · rfl
  | BNot b1 ih =>
    dsimp [fold_constants_bexp, beval]
    generalize h : fold_constants_bexp b1 = b1'
    rw [h] at ih
    cases b1' <;> (try simp_all [beval])
  | BAnd b1 b2 ih1 ih2 =>
    dsimp [fold_constants_bexp, beval]
    generalize h1 : fold_constants_bexp b1 = b1'
    generalize h2 : fold_constants_bexp b2 = b2'
    rw [h1] at ih1
    rw [h2] at ih2
    cases b1' <;> cases b2' <;> (try simp_all [beval])

/-!
#### 练习：3 星, standard (fold_constants_com_sound)

证明整语言的命令常量折叠优化器是可靠的。
提示：使用各种同余引理以及 `if_true`、`if_false`、`while_true`、`while_false`！
-/

theorem fold_constants_com_sound : ctrans_sound fold_constants_com := by
  sorry

/-!
### 4.4 消除 (0 + n) 优化器及其可靠性

#### 练习：4 星, standard, optional (optimize_0plus_var)
-/

/-- 算术表达式 (0 + n) 代数优化器 -/
def optimize_0plus_aexp (a : aexp) : aexp :=
  match a with
  | .ANum n => .ANum n
  | .AId x => .AId x
  | .APlus a1 a2 =>
    match optimize_0plus_aexp a1, optimize_0plus_aexp a2 with
    | .ANum 0, a2' => a2'
    | a1', a2' => .APlus a1' a2'
  | .AMinus a1 a2 => .AMinus (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | .AMult a1 a2 => .AMult (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)

/-- 布尔表达式 (0 + n) 递归优化器 -/
def optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
  | .BTrue => .BTrue
  | .BFalse => .BFalse
  | .BEq a1 a2 => .BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | .BNeq a1 a2 => .BNeq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | .BLe a1 a2 => .BLe (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | .BGt a1 a2 => .BGt (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | .BNot b1 => .BNot (optimize_0plus_bexp b1)
  | .BAnd b1 b2 => .BAnd (optimize_0plus_bexp b1) (optimize_0plus_bexp b2)

/-- 命令式语句 (0 + n) 优化器 -/
def optimize_0plus_com (c : com) : com :=
  match c with
  | .CSkip => .CSkip
  | .CAsgn x a => .CAsgn x (optimize_0plus_aexp a)
  | .CSeq c1 c2 => .CSeq (optimize_0plus_com c1) (optimize_0plus_com c2)
  | .CIf b c1 c2 => .CIf (optimize_0plus_bexp b) (optimize_0plus_com c1) (optimize_0plus_com c2)
  | .CWhile b c1 => .CWhile (optimize_0plus_bexp b) (optimize_0plus_com c1)

theorem test_optimize_0plus :
    optimize_0plus_com (WHILE (BNeq (AId X) (ANum 0)) DO (X ::= (ANum 0 + AId X) - ANum 1) END) =
    (WHILE (BNeq (AId X) (ANum 0)) DO (X ::= AId X - ANum 1) END) := rfl

theorem optimize_0plus_aexp_sound : atrans_sound optimize_0plus_aexp := by
  sorry

theorem optimize_0plus_bexp_sound : btrans_sound optimize_0plus_bexp := by
  sorry

theorem optimize_0plus_com_sound : ctrans_sound optimize_0plus_com := by
  sorry

/-- 复合优化器：串联常量折叠与 0 + n 代数简化 -/
def optimizer (c : com) : com :=
  optimize_0plus_com (fold_constants_com c)

/-- 复合优化器的可靠性：由传递性直接由各子优化器可靠性组合而成 -/
theorem optimizer_sound : ctrans_sound optimizer := by
  intro c
  dsimp [optimizer]
  apply trans_cequiv c (fold_constants_com c) (optimize_0plus_com (fold_constants_com c))
  · exact fold_constants_com_sound c
  · exact optimize_0plus_com_sound (fold_constants_com c)

-- #################################################################
-- * 5. 证明程序不等价 (Proving Inequivalence)
-- #################################################################

/-!
### 5.1 变量代换与反例构造

考虑赋值语句序列：
`x1 := a1; x2 := a2`
我们是否能直接将 `a2` 中出现的 `x1` 全部替换为 `a1`？
-/

/-- 算术表达式内的变量语法替换 -/
def subst_aexp (x : String) (u : aexp) (a : aexp) : aexp :=
  match a with
  | .ANum n => .ANum n
  | .AId x' => if x == x' then u else .AId x'
  | .APlus a1 a2 => .APlus (subst_aexp x u a1) (subst_aexp x u a2)
  | .AMinus a1 a2 => .AMinus (subst_aexp x u a1) (subst_aexp x u a2)
  | .AMult a1 a2 => .AMult (subst_aexp x u a1) (subst_aexp x u a2)

theorem subst_aexp_ex : subst_aexp X (.APlus (.ANum 42) (.ANum 53)) (.APlus (.AId Y) (.AId X)) =
    .APlus (.AId Y) (.APlus (.ANum 42) (.ANum 53)) := rfl

/-- 猜想的代换等价性命题 -/
def subst_equiv_property : Prop :=
  ∀ x1 x2 a1 a2,
    ((x1 ::= a1) ;; (x2 ::= a2)) ==c
    ((x1 ::= a1) ;; (x2 ::= subst_aexp x1 a1 a2))

/-- 反例证明：该猜想在普遍意义下**并不成立**！
    例如：X := X + 1; Y := X 与 X := X + 1; Y := X + 1 显然不等价。 -/
theorem subst_inequiv : ¬ subst_equiv_property := by
  intro contra
  have h := contra X Y (AId X + ANum 1) (AId X)
  dsimp [subst_aexp] at h
  have c1_eval : empty_st =[ (X ::= AId X + ANum 1) ;; (Y ::= AId X) ]=> (Y !-> 1; X !-> 1; empty_st) := by
    apply E_Seq (X ::= AId X + ANum 1) (Y ::= AId X) empty_st (X !-> 1; empty_st)
    · exact E_Asgn empty_st (AId X + ANum 1) 1 X rfl
    · exact E_Asgn (X !-> 1; empty_st) (AId X) 1 Y rfl
  have c2_eval_from_c1 : empty_st =[ (X ::= AId X + ANum 1) ;; (Y ::= AId X + ANum 1) ]=> (Y !-> 1; X !-> 1; empty_st) := by
    rw [← (h empty_st (Y !-> 1; X !-> 1; empty_st))]
    exact c1_eval
  have c2_eval_direct : empty_st =[ (X ::= AId X + ANum 1) ;; (Y ::= AId X + ANum 1) ]=> (Y !-> 2; X !-> 1; empty_st) := by
    apply E_Seq (X ::= AId X + ANum 1) (Y ::= AId X + ANum 1) empty_st (X !-> 1; empty_st)
    · exact E_Asgn empty_st (AId X + ANum 1) 1 X rfl
    · exact E_Asgn (X !-> 1; empty_st) (AId X + ANum 1) 2 Y rfl
  have h_det := ceval_deterministic ((X ::= AId X + ANum 1) ;; (Y ::= AId X + ANum 1)) empty_st
    (Y !-> 1; X !-> 1; empty_st) (Y !-> 2; X !-> 1; empty_st) c2_eval_from_c1 c2_eval_direct
  have h_val : (Y !-> 1; X !-> 1; empty_st) Y = (Y !-> 2; X !-> 1; empty_st) Y := by
    rw [h_det]
  dsimp [t_update] at h_val
  contradiction

/-!
#### 练习：4 星, standard, optional (better_subst_equiv)

只要排除 `x1` 在第一个赋值语句右侧 `a1` 中自由出现的情况，代换就是可靠的！
-/

/-- 归纳命题：变量 x 未在算术表达式 a 中出现 -/
inductive var_not_used_in_aexp (x : String) : aexp → Prop where
  | VNUNum (n : Nat) : var_not_used_in_aexp x (.ANum n)
  | VNUId (y : String) (h : x ≠ y) : var_not_used_in_aexp x (.AId y)
  | VNUPlus (a1 a2 : aexp) (h1 : var_not_used_in_aexp x a1) (h2 : var_not_used_in_aexp x a2) :
      var_not_used_in_aexp x (.APlus a1 a2)
  | VNUMinus (a1 a2 : aexp) (h1 : var_not_used_in_aexp x a1) (h2 : var_not_used_in_aexp x a2) :
      var_not_used_in_aexp x (.AMinus a1 a2)
  | VNUMult (a1 a2 : aexp) (h1 : var_not_used_in_aexp x a1) (h2 : var_not_used_in_aexp x a2) :
      var_not_used_in_aexp x (.AMult a1 a2)

/-- 弱化引理：在未被使用的变量上更新状态，不影响表达式求值 -/
theorem aeval_weakening (x : String) (st : state) (a : aexp) (ni : Nat)
    (h : var_not_used_in_aexp x a) :
    aeval (x !-> ni; st) a = aeval st a := by
  sorry

/-- 修复后的代换等价性定理 -/
theorem better_subst_equiv (x1 x2 : String) (a1 a2 : aexp)
    (h : var_not_used_in_aexp x1 a1) :
    ((x1 ::= a1) ;; (x2 ::= a2)) ==c
    ((x1 ::= a1) ;; (x2 ::= subst_aexp x1 a1 a2)) := by
  sorry

/-!
#### 练习：3 星, standard (inequiv_exercise)

证明死循环与 `SKIP` 必然是不等价的。
-/

theorem inequiv_exercise :
    ¬ (WHILE BTrue DO SKIP END) ==c SKIP := by
  sorry

-- #################################################################
-- * 6. 拓展研讨：非确定性语言 Himp (Nondeterministic Imp)
-- #################################################################

/-!
### 6.1 非确定性命令 HAVOC

在系统级编程语言（如 C）中，未初始化变量、多线程并发交错以及编译器指令调度均引入了非确定性。
在此我们拓展 Imp 语言引入新命令 `HAVOC X`：
执行 `HAVOC X` 会非确定性地向变量 `X` 写入任意一个自然数。
-/

namespace Himp

/-- 拓展 HAVOC 后的命令抽象语法 -/
inductive com : Type where
  | CSkip : com
  | CAsgn : String → aexp → com
  | CSeq : com → com → com
  | CIf : bexp → com → com → com
  | CWhile : bexp → com → com
  | CHavoc : String → com

/-!
#### 练习：2 星, standard (himp_ceval)

在大步操作语义中，为 `HAVOC` 添加语义规则 `E_Havoc`。
-/

inductive ceval : com → state → state → Prop where
  | E_Skip (st : state) :
      ceval .CSkip st st
  | E_Asgn (st : state) (a : aexp) (n : Nat) (x : String) (h : aeval st a = n) :
      ceval (.CAsgn x a) st (x !-> n; st)
  | E_Seq (c1 c2 : com) (st st' st'' : state)
      (h1 : ceval c1 st st') (h2 : ceval c2 st' st'') :
      ceval (.CSeq c1 c2) st st''
  | E_IfTrue (st st' : state) (b : bexp) (c1 c2 : com)
      (hb : beval st b = true) (h : ceval c1 st st') :
      ceval (.CIf b c1 c2) st st'
  | E_IfFalse (st st' : state) (b : bexp) (c1 c2 : com)
      (hb : beval st b = false) (h : ceval c2 st st') :
      ceval (.CIf b c1 c2) st st'
  | E_WhileFalse (b : bexp) (st : state) (c : com)
      (hb : beval st b = false) :
      ceval (.CWhile b c) st st
  | E_WhileTrue (st st' st'' : state) (b : bexp) (c : com)
      (hb : beval st b = true) (h1 : ceval c st st') (h2 : ceval (.CWhile b c) st' st'') :
      ceval (.CWhile b c) st st''
  | E_Havoc (st : state) (n : Nat) (x : String) :
      ceval (.CHavoc x) st (x !-> n; st)

theorem havoc_example1 : ceval (.CHavoc X) empty_st (X !-> 0; empty_st) := by
  exact ceval.E_Havoc empty_st 0 X

theorem havoc_example2 : ceval (.CSeq .CSkip (.CHavoc Z)) empty_st (Z !-> 42; empty_st) := by
  apply ceval.E_Seq .CSkip (.CHavoc Z) empty_st empty_st
  · exact ceval.E_Skip empty_st
  · exact ceval.E_Havoc empty_st 42 Z

def manual_grade_for_Check_rule_for_HAVOC : Option (Nat × String) := none

/-- Himp 程序等价性：可能终止的所有最终状态集合相同 -/
def cequiv (c1 c2 : com) : Prop :=
  ∀ st st' : state, (ceval c1 st st') ↔ (ceval c2 st st')

scoped notation:50 c1:51 " ==c " c2:51 => cequiv c1 c2

/-!
#### 练习：3 星, standard (havoc_swap)
-/

def pXY : com := .CSeq (.CHavoc X) (.CHavoc Y)
def pYX : com := .CSeq (.CHavoc Y) (.CHavoc X)

theorem pXY_cequiv_pYX : (pXY ==c pYX) ∨ ¬(pXY ==c pYX) := by
  sorry

/-!
#### 练习：4 星, standard, optional (havoc_copy)
-/

def ptwice : com := .CSeq (.CHavoc X) (.CHavoc Y)
def pcopy : com := .CSeq (.CHavoc X) (.CAsgn Y (.AId X))

theorem ptwice_cequiv_pcopy : (ptwice ==c pcopy) ∨ ¬(ptwice ==c pcopy) := by
  sorry

/-!
#### 练习：4 星, advanced (p1_p2_term)
-/

def p1 : com :=
  .CWhile (bexp.BNot (bexp.BEq (.AId X) (.ANum 0)))
    (.CSeq (.CHavoc Y) (.CAsgn X (.APlus (.AId X) (.ANum 1))))

def p2 : com :=
  .CWhile (bexp.BNot (bexp.BEq (.AId X) (.ANum 0)))
    .CSkip

theorem p1_may_diverge (st st' : state) (h : st X ≠ 0) :
    ¬ ceval p1 st st' := by
  sorry

theorem p2_may_diverge (st st' : state) (h : st X ≠ 0) :
    ¬ ceval p2 st st' := by
  sorry

/-!
#### 练习：4 星, advanced (p1_p2_equiv)
-/

theorem p1_p2_equiv : p1 ==c p2 := by
  sorry

/-!
#### 练习：4 星, advanced (p3_p4_inequiv)
-/

def p3 : com :=
  .CSeq (.CAsgn Z (.ANum 1))
    (.CWhile (bexp.BNeq (.AId X) (.ANum 0))
      (.CSeq (.CHavoc X) (.CHavoc Z)))

def p4 : com :=
  .CSeq (.CAsgn X (.ANum 0)) (.CAsgn Z (.ANum 1))

theorem p3_p4_inequiv : ¬ (p3 ==c p4) := by
  sorry

/-!
#### 练习：5 星, advanced, optional (p5_p6_equiv)
-/

def p5 : com :=
  .CWhile (bexp.BNeq (.AId X) (.ANum 1)) (.CHavoc X)

def p6 : com :=
  .CAsgn X (.ANum 1)

theorem p5_p6_equiv : p5 ==c p6 := by
  sorry

end Himp

-- #################################################################
-- * 7. 附加综合练习 (Additional Exercises)
-- #################################################################

/-!
#### 练习：3 星, standard, optional (swap_noninterfering_assignments)

若两个赋值语句之间互不干扰（变量名不同且互不依赖右端值），则执行顺序可安全交换。
-/

theorem swap_noninterfering_assignments (l1 l2 : String) (a1 a2 : aexp)
    (h_diff : l1 ≠ l2)
    (h12 : var_not_used_in_aexp l1 a2)
    (h21 : var_not_used_in_aexp l2 a1) :
    ((l1 ::= a1) ;; (l2 ::= a2)) ==c
    ((l2 ::= a2) ;; (l1 ::= a1)) := by
  sorry

/-!
#### 练习：4 星, standard, optional (for_while_equiv)

证明 C 风格 for 循环与标准 while 循环的等价性。
-/

/-!
#### 练习：4 星, advanced, optional (capprox)

定义单向的**程序近似关系（Program Approximation）**：
`c1` 近似 `c2` 当且仅当只要 `c1` 能从初态停机，`c2` 也必定能从同一起始状态停机并产生完全相同的最终状态。
若两个程序双向近似，则它们行为等价。
-/

/-- 程序单向近似定义 -/
def capprox (c1 c2 : com) : Prop :=
  ∀ (st st' : state), (st =[ c1 ]=> st') → (st =[ c2 ]=> st')

def c3 : com := (X ::= ANum 1)
def c4 : com := (X ::= ANum 2)

theorem c3_c4_different : ¬ capprox c3 c4 ∧ ¬ capprox c4 c3 := by
  sorry

/-- 近似所有程序的极小程序（恒发散循环） -/
def cmin : com := (WHILE BTrue DO SKIP END)

theorem cmin_minimal (c : com) : capprox cmin c := by
  sorry

/-- 停机性质在程序近似关系下的正向保持性 -/
def zprop (c : com) : Prop :=
  ∀ st, ∃ st', (st =[ c ]=> st')

theorem zprop_preserving (c c' : com) (hz : zprop c) (hc : capprox c c') :
    zprop c' := by
  sorry

end PLF.Equiv
