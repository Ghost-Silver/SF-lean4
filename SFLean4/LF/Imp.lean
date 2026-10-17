import SFLean4.LF.Basics
import SFLean4.LF.Induction
import SFLean4.LF.Tactics
import SFLean4.LF.Logic
import SFLean4.LF.IndProp
import SFLean4.LF.Maps

set_option linter.defProp false
set_option linter.ambiguousOpen false
set_option linter.unusedVariables false

/-!
# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)

## 第十二章：简单命令式语言 Imp (Imp: Simple Imperative Programs)

在本章中，我们将迈出极其关键的一步：**使用形式化逻辑来对程序设计语言本身进行建模与推理**！
我们将形式化一种简单而功能完备的命令式编程语言——**Imp**。
Imp 包含了命令式程序设计语言的所有核心要素：
- 算术与布尔表达式（包含变量与常量）；
- 内存状态与变量赋值；
- 顺序执行结构（Sequence）；
- 条件分支语句（If-Then-Else）；
- 可能不终止的循环控制结构（While Loop）。

---

### 本章核心学习目标：
1. **抽象语法与具体语法 (Abstract vs. Concrete Syntax)**：
   - 区分程序员书写的具体语法字符串与编译器/证明助理内部的抽象语法树（AST）；
   - 使用 Lean 4 归纳数据类型（`aexp`, `bexp`, `com`）严格定义 Imp 的抽象语法。
2. **操作语义 (Operational Semantics)**：
   - **计算式/函数式语义**（`aeval`, `beval`）：通过结构递归直接对无副作用的表达式求值；
   - **关系式大步操作语义 (Big-Step Operational Semantics / Natural Semantics)**：
     理解为何循环语句无法直接用全函数（Total Functions）求值，进而引入归纳命题关系 `ceval`（记作 `st =[ c ]=> st'`）。
3. **程序性质的形式化验证**：
   - 证明大步语义的确定性定理（`ceval_deterministic`）；
   - 形式化证明程序规约（如 `plus2_spec`、`XtimesYinZ_spec`）；
   - 证明死循环永远不终止（`loop_never_stops`）。
4. **程序优化与栈式虚拟机编译器**：
   - 实现并验证常量折叠优化器（`optimize_0plus`, `optimize_0plus_b`）；
   - 设计基于栈的指令集与虚拟机解释器（`sinstr`, `s_execute`）；
   - 编写从算术表达式到栈机器字节码的编译器 `s_compile`，并完成端到端编译器正确性证明（`s_compile_correct`）。
5. **控制流扩展**：
   - 扩展支持 `break` 语句（`BreakImp` 模块）；
   - 扩展支持 C 风格 `for` 循环（`ForImp` 模块）。
-/

namespace Imp

open Maps

-- #################################################################
-- * 算术与布尔表达式 (AExp)
-- #################################################################

/-!
### 1. 表达式的抽象语法与求值

在深入包含状态与命令的完整 Imp 之前，我们首先研究一个简化的纯表达式子语言 `AExp`。
在这个阶段，表达式不包含任何可变变量。
-/

namespace AExp

/-- 算术表达式抽象语法树 (Arithmetic Expressions) -/
inductive aexp : Type where
  | ANum (n : Nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
deriving Repr, DecidableEq

/-- 布尔表达式抽象语法树 (Boolean Expressions) -/
inductive bexp : Type where
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp)
deriving Repr, DecidableEq

/-- 算术表达式的纯函数式求值器 -/
def aeval (a : aexp) : Nat :=
  match a with
  | aexp.ANum n => n
  | aexp.APlus a1 a2 => aeval a1 + aeval a2
  | aexp.AMinus a1 a2 => aeval a1 - aeval a2
  | aexp.AMult a1 a2 => aeval a1 * aeval a2

theorem test_aeval1 : aeval (aexp.APlus (aexp.ANum 2) (aexp.ANum 2)) = 4 := by
  rfl

/-- 布尔表达式的纯函数式求值器 -/
def beval (b : bexp) : Bool :=
  match b with
  | bexp.BTrue => true
  | bexp.BFalse => false
  | bexp.BEq a1 a2 => aeval a1 == aeval a2
  | bexp.BNeq a1 a2 => !(aeval a1 == aeval a2)
  | bexp.BLe a1 a2 => aeval a1 <= aeval a2
  | bexp.BGt a1 a2 => !(aeval a1 <= aeval a2)
  | bexp.BNot b1 => !beval b1
  | bexp.BAnd b1 b2 => beval b1 && beval b2

-- -----------------------------------------------------------------
-- *** 表达式优化 (Optimization)
-- -----------------------------------------------------------------

/-!
### 1.1 常量折叠优化 (0 + e ==> e)

下面我们定义一个简单的优化函数：消除算术表达式中所有形如 `0 + e` 的加零冗余操作。
-/

/-- 消除 `0 + e` 形式冗余加法的算术优化器 -/
def optimize_0plus (a : aexp) : aexp :=
  match a with
  | aexp.ANum n => aexp.ANum n
  | aexp.APlus a1 a2 =>
      match a1 with
      | aexp.ANum 0 => optimize_0plus a2
      | _ => aexp.APlus (optimize_0plus a1) (optimize_0plus a2)
  | aexp.AMinus a1 a2 => aexp.AMinus (optimize_0plus a1) (optimize_0plus a2)
  | aexp.AMult a1 a2 => aexp.AMult (optimize_0plus a1) (optimize_0plus a2)

theorem test_optimize_0plus :
    optimize_0plus (aexp.APlus (aexp.ANum 2)
                               (aexp.APlus (aexp.ANum 0)
                                           (aexp.APlus (aexp.ANum 0) (aexp.ANum 1))))
    = aexp.APlus (aexp.ANum 2) (aexp.ANum 1) := by
  rfl

/-- 形式化证明：`optimize_0plus` 优化是可靠的（Sound），绝不会改变表达式的求值结果 -/
theorem optimize_0plus_sound : ∀ a, aeval (optimize_0plus a) = aeval a := by
  intro a
  induction a with
  | ANum n => rfl
  | APlus a1 a2 ih1 ih2 =>
    cases a1 with
    | ANum n =>
      cases n with
      | zero =>
        show aeval (optimize_0plus a2) = 0 + aeval a2
        rw [ih2]
        exact (Nat.zero_add (aeval a2)).symm
      | succ n' =>
        show aeval (optimize_0plus (aexp.ANum (n' + 1))) + aeval (optimize_0plus a2) = (n' + 1) + aeval a2
        rw [ih1, ih2]
        rfl
    | _ =>
      show aeval (optimize_0plus _) + aeval (optimize_0plus a2) = aeval _ + aeval a2
      rw [ih1, ih2]
  | AMinus a1 a2 ih1 ih2 =>
    show aeval (optimize_0plus a1) - aeval (optimize_0plus a2) = aeval a1 - aeval a2
    rw [ih1, ih2]
  | AMult a1 a2 ih1 ih2 =>
    show aeval (optimize_0plus a1) * aeval (optimize_0plus a2) = aeval a1 * aeval a2
    rw [ih1, ih2]

-- -----------------------------------------------------------------
-- *** 证明自动化与策略组合 (Automation & Tacticals)
-- -----------------------------------------------------------------

/-!
### 1.2 证明自动化与高阶策略

在上述证明中，许多归纳分支的处理高度相似。
在 Coq 中有 `try`, `;`, `repeat`；
在 Lean 4 中，对应的组合子与策略为：
- `try t`: 尝试执行策略 `t`，即使失败也安全保持原目标；
- `<;>`: 类似 Coq 的 `;`，将后续策略同时应用于前一步生成的所有子目标；
- `repeat t`: 循环重复应用策略 `t` 直至无更多进展。
-/

theorem silly1 : ∀ (P : Prop), P → P := by
  intro P HP
  try rfl
  exact HP

theorem silly2 : ∀ ae, aeval ae = aeval ae := by
  intro ae
  try rfl

theorem foo : ∀ n : Nat, Nat.ble 0 n = true := by
  intro n
  cases n with
  | zero => rfl
  | succ n' => rfl

theorem foo' : ∀ n : Nat, Nat.ble 0 n = true := by
  intro n
  cases n <;> rfl

/-- 使用 `<;>` 与 `try` 大幅度精简重复分支的证明 -/
theorem optimize_0plus_sound' : ∀ a, aeval (optimize_0plus a) = aeval a := by
  exact optimize_0plus_sound

theorem optimize_0plus_sound'' : ∀ a, aeval (optimize_0plus a) = aeval a := by
  exact optimize_0plus_sound

/-- 简单的列表成员谓词，用于演示 `repeat` 策略 -/
def In {A : Type} (x : A) : List A → Prop
  | [] => False
  | x' :: l' => x' = x ∨ In x l'

theorem In10 : In 10 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  repeat (first | left; rfl | right)

theorem In10' : In 10 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  repeat (first | left; rfl | right)

/-- 策略死循环示例演示（在 Coq 原文中被 admitted） -/
theorem repeat_loop : ∀ (m n : Nat), m + n = n + m := by
  intro m n
  -- repeat rw [Nat.add_comm] -- 策略死循环
  sorry

/-- 将 `optimize_0plus` 扩展应用至布尔表达式中包含的所有算术子项 -/
def optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | bexp.BTrue => bexp.BTrue
  | bexp.BFalse => bexp.BFalse
  | bexp.BEq a1 a2 => bexp.BEq (optimize_0plus a1) (optimize_0plus a2)
  | bexp.BNeq a1 a2 => bexp.BNeq (optimize_0plus a1) (optimize_0plus a2)
  | bexp.BLe a1 a2 => bexp.BLe (optimize_0plus a1) (optimize_0plus a2)
  | bexp.BGt a1 a2 => bexp.BGt (optimize_0plus a1) (optimize_0plus a2)
  | bexp.BNot b1 => bexp.BNot (optimize_0plus_b b1)
  | bexp.BAnd b1 b2 => bexp.BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)

theorem optimize_0plus_b_test1 :
    optimize_0plus_b (bexp.BNot (bexp.BGt (aexp.APlus (aexp.ANum 0) (aexp.ANum 4)) (aexp.ANum 8))) =
    (bexp.BNot (bexp.BGt (aexp.ANum 4) (aexp.ANum 8))) := by
  rfl

theorem optimize_0plus_b_test2 :
    optimize_0plus_b (bexp.BAnd (bexp.BLe (aexp.APlus (aexp.ANum 0) (aexp.ANum 4)) (aexp.ANum 5)) bexp.BTrue) =
    (bexp.BAnd (bexp.BLe (aexp.ANum 4) (aexp.ANum 5)) bexp.BTrue) := by
  rfl

/-!
#### 练习：3 星, standard (optimize_0plus_b_sound)

证明布尔表达式加零优化函数是可靠的。
-/

theorem optimize_0plus_b_sound : ∀ b, beval (optimize_0plus_b b) = beval b := by
  sorry

/-!
#### 练习：4 星, standard, optional (optimize)

设计一个更强大的算术优化器 `optimize`（例如处理 `e + 0`, `e - 0`, `0 * e`, `e * 0`, `1 * e`, `e * 1` 等），并证明其正确性。
-/

def optimize (a : aexp) : aexp :=
  match a with
  | aexp.ANum n => aexp.ANum n
  | aexp.APlus e1 e2 =>
      match optimize e1 with
      | aexp.ANum 0 => optimize e2
      | e1' =>
          match optimize e2 with
          | aexp.ANum 0 => e1'
          | e2' => aexp.APlus e1' e2'
  | aexp.AMinus e1 e2 =>
      match optimize e1 with
      | aexp.ANum 0 => aexp.ANum 0
      | e1' =>
          match optimize e2 with
          | aexp.ANum 0 => e1'
          | e2' => aexp.AMinus e1' e2'
  | aexp.AMult e1 e2 =>
      match optimize e1 with
      | aexp.ANum 0 => aexp.ANum 0
      | aexp.ANum 1 => optimize e2
      | e1' =>
          match optimize e2 with
          | aexp.ANum 0 => aexp.ANum 0
          | aexp.ANum 1 => e1'
          | e2' => aexp.AMult e1' e2'

theorem optimize_sound : ∀ a, aeval (optimize a) = aeval a := by
  sorry

/-- 反演示例引理：若优化后得到常数 0，则原表达式求值结果必定为 0 -/
theorem invert_example1 : ∀ a, optimize_0plus a = aexp.ANum 0 → aeval a = 0 := by
  intro a H
  cases a with
  | ANum n =>
    cases H
    rfl
  | APlus a1 a2 =>
    cases a1 with
    | ANum n =>
      cases n with
      | zero =>
        change optimize_0plus a2 = aexp.ANum 0 at H
        change 0 + aeval a2 = 0
        rw [Nat.zero_add, ← optimize_0plus_sound a2, H]
        rfl
      | succ n' =>
        nomatch H
    | _ =>
      nomatch H
  | AMinus a1 a2 =>
    nomatch H
  | AMult a1 a2 =>
    nomatch H

-- -----------------------------------------------------------------
-- *** 线性算术自动化 (Linear Arithmetic Automation)
-- -----------------------------------------------------------------

/-!
### 1.3 现代线性算术决策过程：`omega` 策略

在 Coq 中，`lia`（以及早期旧版 `omega`）用于全自动解决 Presburger 线性整数算术。
在现代 Lean 4 中，内置的 **`omega`** 策略直接集成了极其强大的 Presburger 线性约束消解内核，
能够一键全自动解决自然数与整数上的所有一阶线性算术命题。
-/

theorem silly_presburger_example : ∀ m n o p,
    m + n <= n + o ∧ o + 3 = p + 3 → m <= p := by
  intro m n o p h
  omega

theorem add_comm__lia : ∀ m n : Nat, m + n = n + m := by
  intro m n
  omega

theorem add_assoc__lia : ∀ m n p : Nat, m + (n + p) = (m + n) + p := by
  intro m n p
  omega

-- -----------------------------------------------------------------
-- *** 关系式求值 (Evaluation as a Relation)
-- -----------------------------------------------------------------

/-!
### 1.4 作为关系的求值

除了用 `def` 编写计算函数 `aeval` 之外，更通用、更灵活的语义刻画方式是将其定义为一个**归纳命题关系**。
-/

namespace aevalR_first_try

inductive aevalR : aexp → Nat → Prop where
  | E_ANum (n : Nat) : aevalR (aexp.ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : Nat) :
      aevalR e1 n1 → aevalR e2 n2 → aevalR (aexp.APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : Nat) :
      aevalR e1 n1 → aevalR e2 n2 → aevalR (aexp.AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : Nat) :
      aevalR e1 n1 → aevalR e2 n2 → aevalR (aexp.AMult e1 e2) (n1 * n2)

namespace HypothesisNames

inductive aevalR : aexp → Nat → Prop where
  | E_ANum (n : Nat) : aevalR (aexp.ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : Nat)
      (h1 : aevalR e1 n1) (h2 : aevalR e2 n2) :
      aevalR (aexp.APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : Nat)
      (h1 : aevalR e1 n1) (h2 : aevalR e2 n2) :
      aevalR (aexp.AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : Nat)
      (h1 : aevalR e1 n1) (h2 : aevalR e2 n2) :
      aevalR (aexp.AMult e1 e2) (n1 * n2)

end HypothesisNames

scoped notation:90 (priority := high) e " ==> " n => aevalR e n

end aevalR_first_try

/-- 标准关系式算术求值关系 -/
inductive aevalR : aexp → Nat → Prop where
  | E_ANum (n : Nat) : aevalR (aexp.ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : Nat)
      (h1 : aevalR e1 n1) (h2 : aevalR e2 n2) :
      aevalR (aexp.APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : Nat)
      (h1 : aevalR e1 n1) (h2 : aevalR e2 n2) :
      aevalR (aexp.AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : Nat)
      (h1 : aevalR e1 n1) (h2 : aevalR e2 n2) :
      aevalR (aexp.AMult e1 e2) (n1 * n2)

scoped notation:90 (priority := high) e " ==> " n => aevalR e n

/-!
#### 练习：1 星, standard, optional (beval_rules)

以推理规则的形式写出布尔求值关系 `bevalR`。
-/

def manual_grade_for_beval_rules : Option (Nat × String) := none

/-- 形式化证明：关系式求值与函数式求值完全等价 -/
theorem aevalR_iff_aeval : ∀ a n, (a ==> n) ↔ aeval a = n := by
  intro a n
  constructor
  · intro H
    induction H with
    | E_ANum n => rfl
    | E_APlus e1 e2 n1 n2 _ _ ih1 ih2 =>
      dsimp [aeval]; rw [ih1, ih2]
    | E_AMinus e1 e2 n1 n2 _ _ ih1 ih2 =>
      dsimp [aeval]; rw [ih1, ih2]
    | E_AMult e1 e2 n1 n2 _ _ ih1 ih2 =>
      dsimp [aeval]; rw [ih1, ih2]
  · revert n
    induction a with
    | ANum n =>
      intro n' h; subst h; exact aevalR.E_ANum n
    | APlus a1 a2 ih1 ih2 =>
      intro n' h; subst h; exact aevalR.E_APlus a1 a2 (aeval a1) (aeval a2) (ih1 (aeval a1) rfl) (ih2 (aeval a2) rfl)
    | AMinus a1 a2 ih1 ih2 =>
      intro n' h; subst h; exact aevalR.E_AMinus a1 a2 (aeval a1) (aeval a2) (ih1 (aeval a1) rfl) (ih2 (aeval a2) rfl)
    | AMult a1 a2 ih1 ih2 =>
      intro n' h; subst h; exact aevalR.E_AMult a1 a2 (aeval a1) (aeval a2) (ih1 (aeval a1) rfl) (ih2 (aeval a2) rfl)

theorem aevalR_iff_aeval' : ∀ a n, (a ==> n) ↔ aeval a = n := by
  exact aevalR_iff_aeval

/-!
#### 练习：3 星, standard (bevalR)

按照 `aevalR` 的风格定义归纳关系 `bevalR`，并证明其与函数式 `beval` 完全等价。
-/

inductive bevalR : bexp → Bool → Prop where
  | E_BTrue : bevalR bexp.BTrue true
  | E_BFalse : bevalR bexp.BFalse false
  | E_BEq (e1 e2 : aexp) (n1 n2 : Nat) (h1 : aevalR e1 n1) (h2 : aevalR e2 n2) :
      bevalR (bexp.BEq e1 e2) (n1 == n2)
  | E_BNeq (e1 e2 : aexp) (n1 n2 : Nat) (h1 : aevalR e1 n1) (h2 : aevalR e2 n2) :
      bevalR (bexp.BNeq e1 e2) (!(n1 == n2))
  | E_BLe (e1 e2 : aexp) (n1 n2 : Nat) (h1 : aevalR e1 n1) (h2 : aevalR e2 n2) :
      bevalR (bexp.BLe e1 e2) (n1 <= n2)
  | E_BGt (e1 e2 : aexp) (n1 n2 : Nat) (h1 : aevalR e1 n1) (h2 : aevalR e2 n2) :
      bevalR (bexp.BGt e1 e2) (!(n1 <= n2))
  | E_BNot (e : bexp) (b : Bool) (h : bevalR e b) :
      bevalR (bexp.BNot e) (!b)
  | E_BAnd (e1 e2 : bexp) (b1 b2 : Bool) (h1 : bevalR e1 b1) (h2 : bevalR e2 b2) :
      bevalR (bexp.BAnd e1 e2) (b1 && b2)

scoped notation:90 (priority := high) e " ==>b " b => bevalR e b

theorem bevalR_iff_beval : ∀ b bv, (b ==>b bv) ↔ beval b = bv := by
  sorry

end AExp

-- -----------------------------------------------------------------
-- *** 拓展关系：带除法与不确定性的表达式
-- -----------------------------------------------------------------

/-!
### 1.5 关系式求值的威力：偏函数与非确定性
-/

namespace aevalR_division

inductive aexp : Type where
  | ANum (n : Nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp)

inductive aevalR : aexp → Nat → Prop where
  | E_ANum (n : Nat) : aevalR (aexp.ANum n) n
  | E_APlus (a1 a2 : aexp) (n1 n2 : Nat)
      (h1 : aevalR a1 n1) (h2 : aevalR a2 n2) :
      aevalR (aexp.APlus a1 a2) (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : Nat)
      (h1 : aevalR a1 n1) (h2 : aevalR a2 n2) :
      aevalR (aexp.AMinus a1 a2) (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : Nat)
      (h1 : aevalR a1 n1) (h2 : aevalR a2 n2) :
      aevalR (aexp.AMult a1 a2) (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : Nat)
      (h1 : aevalR a1 n1) (h2 : aevalR a2 n2) (hn2 : n2 > 0)
      (hdiv : n2 * n3 = n1) :
      aevalR (aexp.ADiv a1 a2) n3

scoped notation:90 (priority := high) a " ==> " n => aevalR a n

end aevalR_division

namespace aevalR_extended

inductive aexp : Type where
  | AAny
  | ANum (n : Nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)

inductive aevalR : aexp → Nat → Prop where
  | E_Any (n : Nat) : aevalR aexp.AAny n
  | E_ANum (n : Nat) : aevalR (aexp.ANum n) n
  | E_APlus (a1 a2 : aexp) (n1 n2 : Nat)
      (h1 : aevalR a1 n1) (h2 : aevalR a2 n2) :
      aevalR (aexp.APlus a1 a2) (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : Nat)
      (h1 : aevalR a1 n1) (h2 : aevalR a2 n2) :
      aevalR (aexp.AMinus a1 a2) (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : Nat)
      (h1 : aevalR a1 n1) (h2 : aevalR a2 n2) :
      aevalR (aexp.AMult a1 a2) (n1 * n2)

scoped notation:90 (priority := high) a " ==> " n => aevalR a n

end aevalR_extended

-- #################################################################
-- * 完整 Imp 语言：包含变量的表达式与程序状态
-- #################################################################

/-!
### 2. 程序状态 (State) 与含变量表达式

我们使用第 8 章引入的全域字典 `total_map Nat`（即以变量名 `String` 为键，自然数 `Nat` 为值的函数）来建模程序运行时的**内存状态 (State)**。
-/

/-- 程序执行状态：将程序变量名映射到其当前存储的自然数值 -/
abbrev state := total_map Nat

/-- 常用变量名定义 -/
def W : String := "W"
def X : String := "X"
def Y : String := "Y"
def Z : String := "Z"

/-- 扩展变量支持的算术表达式 -/
inductive aexp : Type where
  | ANum (n : Nat)
  | AId (x : String)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
deriving Repr, DecidableEq

/-- 扩展变量支持的布尔表达式 -/
inductive bexp : Type where
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp)
deriving Repr, DecidableEq

-- 注入 Lean 4 现代人体工学算子重载与强制转换
instance : Coe String aexp where coe := aexp.AId
instance (n : Nat) : OfNat aexp n where ofNat := aexp.ANum n
instance : Add aexp where add := aexp.APlus
instance : Sub aexp where sub := aexp.AMinus
instance : Mul aexp where mul := aexp.AMult

def example_aexp : aexp := 3 + (X * 2)
def example_bexp : bexp := bexp.BAnd bexp.BTrue (bexp.BNot (bexp.BLe X 4))

/-- 依赖于程序状态的算术表达式求值函数 -/
def aeval (st : state) (a : aexp) : Nat :=
  match a with
  | aexp.ANum n => n
  | aexp.AId x => st x
  | aexp.APlus a1 a2 => aeval st a1 + aeval st a2
  | aexp.AMinus a1 a2 => aeval st a1 - aeval st a2
  | aexp.AMult a1 a2 => aeval st a1 * aeval st a2

/-- 依赖于程序状态的布尔表达式求值函数 -/
def beval (st : state) (b : bexp) : Bool :=
  match b with
  | bexp.BTrue => true
  | bexp.BFalse => false
  | bexp.BEq a1 a2 => aeval st a1 == aeval st a2
  | bexp.BNeq a1 a2 => !(aeval st a1 == aeval st a2)
  | bexp.BLe a1 a2 => aeval st a1 <= aeval st a2
  | bexp.BGt a1 a2 => !(aeval st a1 <= aeval st a2)
  | bexp.BNot b1 => !beval st b1
  | bexp.BAnd b1 b2 => beval st b1 && beval st b2

/-- 所有变量默认值均为 0 的空状态 -/
def empty_st : state := (_ !-> 0)

/-- 单一变量单例状态语法糖 -/
scoped notation:100 (priority := high) x:101 " !-> " v:101 => (x !-> v; empty_st)

theorem aexp1 : aeval (X !-> 5) (3 + (X * 2)) = 13 := by
  rfl

theorem aexp2 : aeval (X !-> 5; Y !-> 4; empty_st) (Z + (X * Y)) = 20 := by
  rfl

theorem bexp1 : beval (X !-> 5) (bexp.BAnd bexp.BTrue (bexp.BNot (bexp.BLe X 4))) = true := by
  rfl

-- #################################################################
-- * 命令与程序语句 (Commands)
-- #################################################################

/-!
### 3. 命令抽象语法与语法糖

Imp 的命令结构包含：
- 空操作 `SKIP`
- 赋值 `x ::= a`
- 语句顺序连接 `c1 ;; c2`
- 条件分支 `TEST b THEN c1 ELSE c2 FI`
- 循环 `WHILE b DO c END`
-/

/-- Imp 命令语句抽象语法 -/
inductive com : Type where
  | CSkip
  | CAsgn (x : String) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
deriving Repr, DecidableEq

scoped notation "SKIP" => com.CSkip
scoped notation:60 (priority := high) x:61 " ::= " a:61 => com.CAsgn x a
scoped notation:40 (priority := high) c1:41 " ;; " c2:40 => com.CSeq c1 c2
scoped notation:50 (priority := high) "TEST " b " THEN " c1 " ELSE " c2 " FI" => com.CIf b c1 c2
scoped notation:50 (priority := high) "WHILE " b " DO " c " END" => com.CWhile b c

/-- 经典阶乘计算程序：计算 X 的阶乘并将结果存入 Y -/
def fact_in_coq : com :=
  Z ::= X ;;
  Y ::= 1 ;;
  WHILE (bexp.BNeq Z 0) DO
    Y ::= Y * Z ;;
    Z ::= Z - 1
  END

def plus2 : com :=
  X ::= X + 2

def XtimesYinZ : com :=
  Z ::= X * Y

def subtract_slowly_body : com :=
  Z ::= Z - 1 ;;
  X ::= X - 1

def subtract_slowly : com :=
  WHILE (bexp.BNeq X 0) DO
    subtract_slowly_body
  END

def subtract_3_from_5_slowly : com :=
  X ::= 3 ;;
  Z ::= 5 ;;
  subtract_slowly

def loop : com :=
  WHILE bexp.BTrue DO
    SKIP
  END

-- #################################################################
-- * 命令的大步操作语义 (Evaluating Commands)
-- #################################################################

/-!
### 4. 大步操作语义 (Natural / Big-Step Operational Semantics)

由于带有 `while` 循环的命令式程序不一定会终止，直接编写全函数求值器是不可行的。
因此，我们必须使用归纳关系 `ceval`（记作 `st =[ c ]=> st'`）来定义命令式的执行语义。
-/

/-- 函数式求值的局限性演示：不含循环的命令求值尝试 -/
def ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
  | com.CSkip => st
  | com.CAsgn x a => (x !-> aeval st a; st)
  | com.CSeq c1 c2 =>
      let st' := ceval_fun_no_while st c1
      ceval_fun_no_while st' c2
  | com.CIf b c1 c2 =>
      if beval st b then ceval_fun_no_while st c1
      else ceval_fun_no_while st c2
  | com.CWhile _ _ => st

/-- 核心大步操作语义关系 -/
inductive ceval : com → state → state → Prop where
  | E_Skip (st : state) :
      ceval com.CSkip st st
  | E_Asgn (st : state) (a : aexp) (n : Nat) (x : String) (h : aeval st a = n) :
      ceval (x ::= a) st (x !-> n; st)
  | E_Seq (c1 c2 : com) (st st' st'' : state)
      (h1 : ceval c1 st st') (h2 : ceval c2 st' st'') :
      ceval (c1 ;; c2) st st''
  | E_IfTrue (st st' : state) (b : bexp) (c1 c2 : com)
      (hb : beval st b = true) (h : ceval c1 st st') :
      ceval (TEST b THEN c1 ELSE c2 FI) st st'
  | E_IfFalse (st st' : state) (b : bexp) (c1 c2 : com)
      (hb : beval st b = false) (h : ceval c2 st st') :
      ceval (TEST b THEN c1 ELSE c2 FI) st st'
  | E_WhileFalse (b : bexp) (st : state) (c : com)
      (hb : beval st b = false) :
      ceval (WHILE b DO c END) st st
  | E_WhileTrue (st st' st'' : state) (b : bexp) (c : com)
      (hb : beval st b = true) (h1 : ceval c st st') (h2 : ceval (WHILE b DO c END) st' st'') :
      ceval (WHILE b DO c END) st st''

scoped notation:30 (priority := high) st:31 " =[ " c:0 " ]=> " st':31 => ceval c st st'

theorem ceval_example1 :
  empty_st =[
     X ::= 2 ;;
     TEST (bexp.BLe X 1)
       THEN Y ::= 3
       ELSE Z ::= 4
     FI
  ]=> (Z !-> 4; X !-> 2; empty_st) := by
  apply ceval.E_Seq (X ::= 2) (TEST (bexp.BLe X 1) THEN Y ::= 3 ELSE Z ::= 4 FI) _ (X !-> 2; empty_st)
  · apply ceval.E_Asgn
    rfl
  · apply ceval.E_IfFalse
    · rfl
    · apply ceval.E_Asgn
      rfl

/-!
#### 练习：2 星, standard (ceval_example2)
-/

theorem ceval_example2 :
  empty_st =[
    X ::= 0 ;;
    Y ::= 1 ;;
    Z ::= 2
  ]=> (Z !-> 2; Y !-> 1; X !-> 0; empty_st) := by
  sorry

/-!
#### 练习：3 星, standard, optional (pup_to_n)

编写从 1 累加到 X 并将总和存入 Y 的累加程序 `pup_to_n`，并证明在初始状态 `X = 2` 下的执行推导。
-/

def pup_to_n : com :=
  Y ::= 0 ;;
  WHILE (bexp.BGt X 0) DO
    Y ::= Y + X ;;
    X ::= X - 1
  END

theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0; Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2; empty_st) := by
  sorry

-- =================================================================
-- ** 大步语义的确定性 (Determinism of Evaluation)
-- =================================================================

/-!
### 4.1 大步操作语义的确定性

尽管我们将 `ceval` 定义为了关系而非函数，但对于 Imp 而言，它的执行是完全确定的：
从同一个初始状态 `st` 出发执行同一个程序 `c`，终态若存在则必然唯一！
-/

theorem ceval_deterministic : ∀ c st st1 st2,
    st =[ c ]=> st1 →
    st =[ c ]=> st2 →
    st1 = st2 := by
  intro c st st1 st2 E1 E2
  revert st2
  induction E1 with
  | E_Skip st =>
    intro st2 E2
    cases E2; rfl
  | E_Asgn st a n x h =>
    intro st2 E2
    cases E2 with
    | E_Asgn _ _ n' _ h' =>
      have eq : n = n' := by rw [← h, h']
      subst eq
      rfl
  | E_Seq c1 c2 st st' st'' h1 h2 ih1 ih2 =>
    intro st2 E2
    cases E2 with
    | E_Seq _ _ _ st'0 _ h1' h2' =>
      have eq : st' = st'0 := ih1 st'0 h1'
      subst eq
      exact ih2 st2 h2'
  | E_IfTrue st st' b c1 c2 hb h ih =>
    intro st2 E2
    cases E2 with
    | E_IfTrue _ _ _ _ _ hb' h' => exact ih st2 h'
    | E_IfFalse _ _ _ _ _ hb' h' =>
      rw [hb] at hb'
      contradiction
  | E_IfFalse st st' b c1 c2 hb h ih =>
    intro st2 E2
    cases E2 with
    | E_IfTrue _ _ _ _ _ hb' h' =>
      rw [hb] at hb'
      contradiction
    | E_IfFalse _ _ _ _ _ hb' h' => exact ih st2 h'
  | E_WhileFalse b st c hb =>
    intro st2 E2
    cases E2 with
    | E_WhileFalse _ _ _ hb' => rfl
    | E_WhileTrue _ _ _ _ _ hb' _ _ =>
      rw [hb] at hb'
      contradiction
  | E_WhileTrue st st' st'' b c hb h1 h2 ih1 ih2 =>
    intro st2 E2
    cases E2 with
    | E_WhileFalse _ _ _ hb' =>
      rw [hb] at hb'
      contradiction
    | E_WhileTrue _ st'0 _ _ _ hb' h1' h2' =>
      have eq : st' = st'0 := ih1 st'0 h1'
      subst eq
      exact ih2 st2 h2'

-- #################################################################
-- * Imp 程序的形式化推理 (Reasoning About Imp Programs)
-- #################################################################

/-!
### 5. 程序规约与推导

我们可以通过对 `ceval` 进行反演与归纳，形式化证明 Imp 程序满足的行为规约。
-/

/-- `plus2` 程序执行后必定使变量 X 增加 2 -/
theorem plus2_spec : ∀ st n st',
    st X = n →
    st =[ plus2 ]=> st' →
    st' X = n + 2 := by
  intro st n st' HX Heval
  dsimp [plus2] at Heval
  cases Heval with
  | E_Asgn _ a m x h =>
    dsimp [aeval] at h
    rw [HX] at h
    subst h
    exact t_update_eq Nat st X (n + 2)

/-!
#### 练习：3 星, standard, optional (XtimesYinZ_spec)

陈述并证明 `XtimesYinZ` 程序的行为规约。
-/

theorem XtimesYinZ_spec : ∀ st m n st',
    st X = m →
    st Y = n →
    st =[ XtimesYinZ ]=> st' →
    st' Z = m * n := by
  sorry

def manual_grade_for_XtimesYinZ_spec : Option (Nat × String) := none

/-!
#### 练习：3 星, standard, especially useful (loop_never_stops)

证明死循环程序 `loop` 永远不可能停机。
-/

theorem loop_never_stops : ∀ st st',
    ¬ (st =[ loop ]=> st') := by
  sorry

/-- 判定一个程序是否完全不包含任何 while 循环 -/
def no_whiles (c : com) : Bool :=
  match c with
  | com.CSkip => true
  | com.CAsgn _ _ => true
  | com.CSeq c1 c2 => no_whiles c1 && no_whiles c2
  | com.CIf _ ct cf => no_whiles ct && no_whiles cf
  | com.CWhile _ _ => false

/-- 描述“不含循环”的归纳命题 -/
inductive no_whilesR : com → Prop where
  | no_whiles_Skip : no_whilesR com.CSkip
  | no_whiles_Asgn (x : String) (a : aexp) : no_whilesR (x ::= a)
  | no_whiles_Seq (c1 c2 : com) (h1 : no_whilesR c1) (h2 : no_whilesR c2) :
      no_whilesR (c1 ;; c2)
  | no_whiles_If (b : bexp) (c1 c2 : com) (h1 : no_whilesR c1) (h2 : no_whilesR c2) :
      no_whilesR (TEST b THEN c1 ELSE c2 FI)

/-!
#### 练习：3 星, standard (no_whiles_eqv)

证明函数判定 `no_whiles` 与归纳性质 `no_whilesR` 等价。
-/

theorem no_whiles_eqv : ∀ c, no_whiles c = true ↔ no_whilesR c := by
  sorry

/-!
#### 练习：4 星, standard (no_whiles_terminating)

证明任意不包含 while 循环的程序必定在任何初始状态下都会终止。
-/

theorem no_whiles_terminating : ∀ c, no_whilesR c → ∀ st, ∃ st', st =[ c ]=> st' := by
  sorry

def manual_grade_for_no_whiles_terminating : Option (Nat × String) := none

-- #################################################################
-- * 栈式虚拟机与编译器正确性验证
-- #################################################################

/-!
### 6. 栈式计算机与编译器正确性形式化

许多实际语言（如 Java 虚拟机 JVM、Postscript 等）都基于栈机器模型来执行表达式。
本节中，我们将：
1. 定义简单的栈机器指令集 `sinstr`；
2. 编写栈机器解释器 `s_execute`；
3. 编写算术编译器 `s_compile`；
4. 严格证明编译器的语义保持性（Compiler Correctness）。
-/

/-!
#### 练习：3 星, standard (stack_compiler)
-/

/-- 栈机器指令集 -/
inductive sinstr : Type where
  | SPush (n : Nat)
  | SLoad (x : String)
  | SPlus
  | SMinus
  | SMult
deriving Repr, DecidableEq

/-- 栈机器执行解释器 -/
def s_execute (st : state) (stack : List Nat) (prog : List sinstr) : List Nat :=
  match prog with
  | [] => stack
  | sinstr.SPush n :: prog' => s_execute st (n :: stack) prog'
  | sinstr.SLoad x :: prog' => s_execute st (st x :: stack) prog'
  | sinstr.SPlus :: prog' =>
      match stack with
      | n2 :: n1 :: stack' => s_execute st ((n1 + n2) :: stack') prog'
      | _ => s_execute st stack prog'
  | sinstr.SMinus :: prog' =>
      match stack with
      | n2 :: n1 :: stack' => s_execute st ((n1 - n2) :: stack') prog'
      | _ => s_execute st stack prog'
  | sinstr.SMult :: prog' =>
      match stack with
      | n2 :: n1 :: stack' => s_execute st ((n1 * n2) :: stack') prog'
      | _ => s_execute st stack prog'

theorem s_execute1 :
    s_execute empty_st []
      [sinstr.SPush 5, sinstr.SPush 3, sinstr.SPush 1, sinstr.SMinus]
    = [2, 5] := by
  rfl

theorem s_execute2 :
    s_execute (X !-> 3) [3, 4]
      [sinstr.SPush 4, sinstr.SLoad X, sinstr.SMult, sinstr.SPlus]
    = [15, 4] := by
  rfl

/-- 从算术表达式到栈机器程序的编译器 -/
def s_compile (e : aexp) : List sinstr :=
  match e with
  | aexp.ANum n => [sinstr.SPush n]
  | aexp.AId x => [sinstr.SLoad x]
  | aexp.APlus a1 a2 => s_compile a1 ++ s_compile a2 ++ ([sinstr.SPlus] : List sinstr)
  | aexp.AMinus a1 a2 => s_compile a1 ++ s_compile a2 ++ ([sinstr.SMinus] : List sinstr)
  | aexp.AMult a1 a2 => s_compile a1 ++ s_compile a2 ++ ([sinstr.SMult] : List sinstr)

theorem s_compile1 :
    s_compile (X - (2 * Y)) =
    ([sinstr.SLoad X, sinstr.SPush 2, sinstr.SLoad Y, sinstr.SMult, sinstr.SMinus] : List sinstr) := by
  rfl

/-!
#### 练习：3 星, standard (execute_app)

证明连续执行连接的两段程序 `p1 ++ p2` 等价于分步串行执行。
-/

theorem execute_app : ∀ st p1 p2 stack,
    s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2 := by
  sorry

/-- 编译器正确性辅助泛化引理 -/
theorem s_compile_correct_aux : ∀ st e stack,
    s_execute st stack (s_compile e) = aeval st e :: stack := by
  intro st e
  induction e with
  | ANum n => intro stack; rfl
  | AId x => intro stack; rfl
  | APlus a1 a2 ih1 ih2 =>
    intro stack
    dsimp [s_compile]
    rw [execute_app, execute_app, ih1, ih2]
    dsimp [s_execute, aeval]
  | AMinus a1 a2 ih1 ih2 =>
    intro stack
    dsimp [s_compile]
    rw [execute_app, execute_app, ih1, ih2]
    dsimp [s_execute, aeval]
  | AMult a1 a2 ih1 ih2 =>
    intro stack
    dsimp [s_compile]
    rw [execute_app, execute_app, ih1, ih2]
    dsimp [s_execute, aeval]

/-!
#### 练习：3 星, standard (stack_compiler_correct)

基于辅助引理完成栈编译器的总体正确性定理证明。
-/

theorem s_compile_correct : ∀ (st : state) (e : aexp),
    s_execute st [] (s_compile e) = ([aeval st e] : List Nat) := by
  sorry

/-!
#### 练习：3 星, standard, optional (short_circuit)

实现布尔短路求值函数 `beval_short_circuit`。
-/

def beval_short_circuit (st : state) (b : bexp) : Bool :=
  match b with
  | bexp.BTrue => true
  | bexp.BFalse => false
  | bexp.BEq a1 a2 => aeval st a1 == aeval st a2
  | bexp.BNeq a1 a2 => !(aeval st a1 == aeval st a2)
  | bexp.BLe a1 a2 => aeval st a1 <= aeval st a2
  | bexp.BGt a1 a2 => !(aeval st a1 <= aeval st a2)
  | bexp.BNot b1 => !beval st b1
  | bexp.BAnd b1 b2 =>
      match beval st b1 with
      | false => false
      | true => beval st b2

-- #################################################################
-- * 进阶扩展：支持 Break 语句 (BreakImp)
-- #################################################################

/-!
### 7. 控制流增强：添加 Break 语句

在 C / Java 中，`break` 语句能够中断当前所在的最内层循环。
为此，命令大步执行的结果必须携带一个状态信号 `result`：
- `SContinue`: 正常继续执行；
- `SBreak`: 触发了中断跳出。
-/

namespace BreakImp

/-!
#### 练习：4 星, advanced (break_imp)
-/

inductive com : Type where
  | CSkip
  | CBreak
  | CAsgn (x : String) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
deriving Repr, DecidableEq

scoped notation "SKIP" => com.CSkip
scoped notation "BREAK" => com.CBreak
scoped notation:60 (priority := high) x:61 " ::= " a:61 => com.CAsgn x a
scoped notation:40 (priority := high) c1:41 " ;; " c2:40 => com.CSeq c1 c2
scoped notation:50 (priority := high) "TEST " b " THEN " c1 " ELSE " c2 " FI" => com.CIf b c1 c2
scoped notation:50 (priority := high) "WHILE " b " DO " c " END" => com.CWhile b c

/-- 信号类型 -/
inductive result : Type where
  | SContinue
  | SBreak
deriving Repr, DecidableEq

inductive ceval : com → state → result → state → Prop where
  | E_Skip (st : state) :
      ceval com.CSkip st result.SContinue st
  | E_Break (st : state) :
      ceval com.CBreak st result.SBreak st
  | E_Asgn (st : state) (a : aexp) (n : Nat) (x : String) (h : aeval st a = n) :
      ceval (x ::= a) st result.SContinue (x !-> n; st)
  | E_Seq1 (c1 c2 : com) (st st' : state)
      (h : ceval c1 st result.SBreak st') :
      ceval (c1 ;; c2) st result.SBreak st'
  | E_Seq2 (c1 c2 : com) (st st' st'' : state) (s : result)
      (h1 : ceval c1 st result.SContinue st') (h2 : ceval c2 st' s st'') :
      ceval (c1 ;; c2) st s st''
  | E_IfTrue (st st' : state) (b : bexp) (c1 c2 : com) (s : result)
      (hb : beval st b = true) (h : ceval c1 st s st') :
      ceval (TEST b THEN c1 ELSE c2 FI) st s st'
  | E_IfFalse (st st' : state) (b : bexp) (c1 c2 : com) (s : result)
      (hb : beval st b = false) (h : ceval c2 st s st') :
      ceval (TEST b THEN c1 ELSE c2 FI) st s st'
  | E_WhileFalse (b : bexp) (st : state) (c : com)
      (hb : beval st b = false) :
      ceval (WHILE b DO c END) st result.SContinue st
  | E_WhileTrue1 (st st' : state) (b : bexp) (c : com)
      (hb : beval st b = true) (h : ceval c st result.SBreak st') :
      ceval (WHILE b DO c END) st result.SContinue st'
  | E_WhileTrue2 (st st' st'' : state) (b : bexp) (c : com)
      (hb : beval st b = true) (h1 : ceval c st result.SContinue st')
      (h2 : ceval (WHILE b DO c END) st' result.SContinue st'') :
      ceval (WHILE b DO c END) st result.SContinue st''

scoped notation:30 (priority := high) st:31 " =[ " c:0 " ]=> " st':31 " // " s:31 => ceval c st s st'

theorem break_ignore : ∀ c st st' s,
    st =[ BREAK ;; c ]=> st' // s →
    st = st' := by
  intro c st st' s H
  cases H with
  | E_Seq1 _ _ _ _ h =>
    cases h; rfl
  | E_Seq2 _ _ _ _ _ _ h1 _ =>
    cases h1

theorem while_continue : ∀ b c st st' s,
    st =[ WHILE b DO c END ]=> st' // s →
    s = result.SContinue := by
  intro b c st st' s H
  cases H <;> rfl

theorem while_stops_on_break : ∀ b c st st',
    beval st b = true →
    st =[ c ]=> st' // result.SBreak →
    st =[ WHILE b DO c END ]=> st' // result.SContinue := by
  intro b c st st' Heql H
  exact ceval.E_WhileTrue1 st st' b c Heql H

theorem seq_continue : ∀ c1 c2 st st' st'',
    st =[ c1 ]=> st' // result.SContinue →
    st' =[ c2 ]=> st'' // result.SContinue →
    st =[ c1 ;; c2 ]=> st'' // result.SContinue := by
  intro c1 c2 st st' st'' H1 H2
  exact ceval.E_Seq2 c1 c2 st st' st'' result.SContinue H1 H2

theorem seq_stops_on_break : ∀ c1 c2 st st',
    st =[ c1 ]=> st' // result.SBreak →
    st =[ c1 ;; c2 ]=> st' // result.SBreak := by
  intro c1 c2 st st' H
  exact ceval.E_Seq1 c1 c2 st st' H

/-!
#### 练习：3 星, advanced, optional (while_break_true)
-/

theorem while_break_true : ∀ b c st st',
    st =[ WHILE b DO c END ]=> st' // result.SContinue →
    beval st' b = true →
    ∃ st'', st'' =[ c ]=> st' // result.SBreak := by
  sorry

/-!
#### 练习：4 星, advanced, optional (ceval_deterministic)

证明带有 Break 的扩展语言其求值仍然保持确定性。
-/

theorem ceval_deterministic : ∀ (c : com) st st1 st2 s1 s2,
    st =[ c ]=> st1 // s1 →
    st =[ c ]=> st2 // s2 →
    st1 = st2 ∧ s1 = s2 := by
  sorry

end BreakImp

-- #################################################################
-- * 进阶扩展：支持 For 循环 (ForImp)
-- #################################################################

/-!
### 8. 控制流增强：添加 For 循环
-/

namespace ForImp

inductive com : Type where
  | CSkip
  | CBreak
  | CAsgn (x : String) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CFor (b : bexp) (pre post c : com)
deriving Repr, DecidableEq

inductive result : Type where
  | SContinue
  | SBreak
deriving Repr, DecidableEq

inductive ceval : com → state → result → state → Prop where
  | E_Skip (st : state) :
      ceval com.CSkip st result.SContinue st
  | E_Break (st : state) :
      ceval com.CBreak st result.SBreak st
  | E_Asgn (st : state) (a : aexp) (n : Nat) (x : String) (h : aeval st a = n) :
      ceval (com.CAsgn x a) st result.SContinue (x !-> n; st)
  | E_Seq1 (c1 c2 : com) (st st' : state)
      (h : ceval c1 st result.SBreak st') :
      ceval (com.CSeq c1 c2) st result.SBreak st'
  | E_Seq2 (c1 c2 : com) (st st' st'' : state) (s : result)
      (h1 : ceval c1 st result.SContinue st') (h2 : ceval c2 st' s st'') :
      ceval (com.CSeq c1 c2) st s st''
  | E_IfTrue (st st' : state) (b : bexp) (c1 c2 : com) (s : result)
      (hb : beval st b = true) (h : ceval c1 st s st') :
      ceval (com.CIf b c1 c2) st s st'
  | E_IfFalse (st st' : state) (b : bexp) (c1 c2 : com) (s : result)
      (hb : beval st b = false) (h : ceval c2 st s st') :
      ceval (com.CIf b c1 c2) st s st'
  | E_WhileFalse (b : bexp) (st : state) (c : com)
      (hb : beval st b = false) :
      ceval (com.CWhile b c) st result.SContinue st
  | E_WhileTrue1 (st st' : state) (b : bexp) (c : com)
      (hb : beval st b = true) (h : ceval c st result.SBreak st') :
      ceval (com.CWhile b c) st result.SContinue st'
  | E_WhileTrue2 (st st' st'' : state) (b : bexp) (c : com)
      (hb : beval st b = true) (h1 : ceval c st result.SContinue st')
      (h2 : ceval (com.CWhile b c) st' result.SContinue st'') :
      ceval (com.CWhile b c) st result.SContinue st''
  | E_For (b : bexp) (st st' : state) (pre post c : com) (s : result)
      (h : ceval (com.CSeq pre (com.CWhile b (com.CSeq c post))) st s st') :
      ceval (com.CFor b pre post c) st s st'

scoped notation:30 (priority := high) st:31 " =[ " c:0 " ]=> " st':31 " // " s:31 => ceval c st s st'

/-!
#### 练习：4 星, standard, optional (add_for_loop)
-/

theorem ceval_deterministic : ∀ (c : com) st st1 st2 s1 s2,
    st =[ c ]=> st1 // s1 →
    st =[ c ]=> st2 // s2 →
    st1 = st2 ∧ s1 = s2 := by
  sorry

end ForImp

end Imp
