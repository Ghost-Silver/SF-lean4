---
title: "Hoare2: 霍尔逻辑 (II)：带标注程序与验证条件生成器 VCGen"
---

```lean
import SFLean4.LF.Basics
import SFLean4.LF.Induction
import SFLean4.LF.Maps
import SFLean4.LF.Imp
import SFLean4.PLF.Equiv
import SFLean4.PLF.Hoare

set_option linter.defProp false
set_option linter.ambiguousOpen false
set_option linter.unusedVariables false
```

# 《软件基础》(Software Foundations) 卷二：程序语言基础 (PLF)

## 第三章：霍尔逻辑（第二部分）(Hoare2: Hoare Logic, Part II)

在上一章 [Hoare](/PLF/Hoare) 中，我们引入了霍尔三元组 `{{ P }} c {{ Q }}` 的语义定义，
并推导了一套关于 Imp 核心语法结构的完全公理化推理规则（`hoare_skip`、`hoare_asgn`、`hoare_seq`、`hoare_if`、`hoare_while` 与 `hoare_consequence`）。

然而，直接手动应用这些规则进行交互式证明往往显得繁冗甚至笨拙：
- 霍尔逻辑的巨大美感在于它是**语法导向（Syntax-Directed）**的：证明的逻辑骨架与程序的抽象语法树完全同构。
- 程序员或验证工程师在直观思考代码正确性时，通常习惯在程序的关键程序点（Program Points）插入局部断言。

这种将断言穿插在命令之间的程序表示形式被称为**带标注程序（Decorated Programs）**或**程序证明大纲（Proof Outlines）**。
带标注程序自身便蕴含了其正确性证明的核心思想。

### 本章核心目标：
1. **形式化带标注程序的语法**：定义带有内嵌断言的命令类型 `dcom` 与完整标注程序 `decorated`。
2. **提取擦除命令**：实现 `erase` 函数，抹除所有断言注解以恢复原始 Imp 程序。
3. **验证条件生成器 (Verification Condition Generator, VCGen)**：
   构造递归函数 `verification_conditions`，自动遍历带标注程序，生成确保所有局部断言自洽的纯一阶逻辑命题（验证条件 VC）。
4. **验证健全性定理 (Soundness of Verification)**：
   形式化证明定理 `verification_correct`：若所有验证条件均成立，则擦除后的 Imp 程序必定满足外层霍尔三元组规约！
5. **循环不变量构造艺术**：
   系统探讨构造有效循环不变量（Loop Invariant）的思维范式，涵盖经典算法：
   慢速减法、奇偶性检验、整数平方根、阶乘计算、最小值求解、双重循环累加、幂级数求和与斐波那契数列计算。
6. **最弱前置条件 (Weakest Preconditions, WP)**：
   形式化定义狄克斯特拉（Dijkstra）的最弱前置条件概念，证明赋值规则 `hoare_asgn` 与不确定赋值规则 `hoare_havoc` 的最弱前置条件性质。

---

## 带标注程序 (Decorated Programs)

```lean
namespace PLF.Hoare2

open Imp
open Maps
open aexp bexp com
open PLF.Hoare

/-- 占位断言（用于练习填空提示） -/
def FILL_IN_HERE : Assertion := fun _ => True
```

### 1. 手工证明到带标注程序

考虑一个将变量 `X` 递减至 0 的简单程序：
```
while X ≠ 0 do
  X := X - 1
end
```
其外层规约为 `{{ True }} reduce_to_zero {{ X = 0 }}`。

### 语法形式化 (Syntax)

```lean
/-- 归零程序：反复自减直到 X 为 0 -/
def reduce_to_zero : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    X ::= AMinus (AId X) (ANum 1)
  END

/-- 手动应用霍尔规则证明 reduce_to_zero 的正确性 -/
theorem reduce_to_zero_correct' :
  {{fun _ => True}} reduce_to_zero {{fun st => st X = 0}} := by
  unfold reduce_to_zero
  apply hoare_consequence_post (Q' := fun st => True ∧ ¬ bassertion (BNot (BEq (AId X) (ANum 0))) st)
  · apply hoare_while
    apply hoare_consequence_pre (P' := (fun _ => True) [ X ↦ AMinus (AId X) (ANum 1) ])
    · apply hoare_asgn
    · intro st _
      trivial
  · intro st ⟨_, hguard⟩
    dsimp [bassertion, beval, aeval] at hguard
    cases h : (st X == 0) with
    | true => exact Nat.eq_of_beq_eq_true h
    | false =>
      have : (!(st X == 0)) = true := by rw [h]; rfl
      exact (hguard this).elim

/-- 自动化断言求解视角下的归零证明 -/
theorem reduce_to_zero_correct''' :
  {{fun _ => True}} reduce_to_zero {{fun st => st X = 0}} := by
  exact reduce_to_zero_correct'
```

### 2. 带标注命令的抽象语法树

直接为每个命令同时标注前置条件与后置条件会导致大量冗余信息。
在标准设计中，每个带标注命令（`dcom`）内嵌其**后置条件**，而从其上下文环境中“继承”其前置条件：
- `DCSkip Q`：`skip {{ Q }}`
- `DCSeq d1 d2`：`d1 ; d2`（`d1` 的后置条件即为 `d2` 的前置条件）
- `DCAsgn X a Q`：`X := a {{ Q }}`
- `DCIf b P1 d1 P2 d2 Q`：带有分支前置条件与整体后置条件的条件分支
- `DCWhile b P d Q`：带有循环体前置条件 `P`、循环体 `d`（其后置条件充当循环不变量）及最终后置条件 `Q` 的循环
- `DCPre P d`：强化前置条件 `->> {{ P }} d`
- `DCPost d Q`：弱化后置条件 `d ->> {{ Q }}`

### 擦除与断言提取 (Erasure and Assertion Extraction)

## 验证条件生成器与健全性 (Verification Conditions and Soundness)

```lean
namespace DComFirstTry

/-- 初步尝试：完全标注的命令（未优化冗余） -/
inductive dcom : Type where
  | DCSkip (P : Assertion) : dcom
  | DCSeq (P : Assertion) (d1 : dcom) (Q : Assertion)
          (d2 : dcom) (R : Assertion) : dcom
  | DCAsgn (X : String) (a : aexp) (Q : Assertion) : dcom
  | DCIf (P : Assertion) (b : bexp) (P1 : Assertion) (d1 : dcom)
         (P2 : Assertion) (d2 : dcom) (Q : Assertion) : dcom
  | DCWhile (P : Assertion) (b : bexp)
            (P1 : Assertion) (d : dcom) (P2 : Assertion)
            (Q : Assertion) : dcom
  | DCPre (P : Assertion) (d : dcom) : dcom
  | DCPost (d : dcom) (Q : Assertion) : dcom

end DComFirstTry

/-- 正式带标注命令定义 -/
inductive dcom : Type where
  | DCSkip (Q : Assertion) : dcom
  | DCSeq (d1 d2 : dcom) : dcom
  | DCAsgn (X : String) (a : aexp) (Q : Assertion) : dcom
  | DCIf (b : bexp) (P1 : Assertion) (d1 : dcom)
         (P2 : Assertion) (d2 : dcom) (Q : Assertion) : dcom
  | DCWhile (b : bexp) (P : Assertion) (d : dcom)
            (Q : Assertion) : dcom
  | DCPre (P : Assertion) (d : dcom) : dcom
  | DCPost (d : dcom) (Q : Assertion) : dcom

/-- 完整的带标注程序：由全局初始前置条件与带标注命令构成 -/
inductive decorated : Type where
  | Decorated : Assertion → dcom → decorated

/-- 基础示例 0：单条空操作标注 -/
def dec0 : dcom :=
  dcom.DCSkip (fun _ => True)

/-- 基础示例 1：死循环标注 -/
def dec1 : dcom :=
  dcom.DCWhile BTrue (fun _ => True) (dcom.DCSkip (fun _ => True)) (fun _ => True)

/-- 示例：带标注的归零程序 -/
def dec_while : decorated :=
  decorated.Decorated (fun _ => True)
    (dcom.DCPost
      (dcom.DCWhile (BNot (BEq (AId X) (ANum 0)))
        (fun st => True ∧ st X ≠ 0)
        (dcom.DCAsgn X (AMinus (AId X) (ANum 1)) (fun _ => True))
        (fun st => True ∧ st X = 0))
      (fun st => st X = 0))


/-- 抹除命令中的所有断言注解，恢复原始 Imp 程序 -/
def erase (d : dcom) : com :=
  match d with
  | dcom.DCSkip _ => com.CSkip
  | dcom.DCSeq d1 d2 => com.CSeq (erase d1) (erase d2)
  | dcom.DCAsgn X a _ => com.CAsgn X a
  | dcom.DCIf b _ d1 _ d2 _ => com.CIf b (erase d1) (erase d2)
  | dcom.DCWhile b _ d _ => com.CWhile b (erase d)
  | dcom.DCPre _ d => erase d
  | dcom.DCPost d _ => erase d

/-- 抹除带标注程序的外层断言与所有内嵌注解 -/
def erase_d (dec : decorated) : com :=
  match dec with
  | decorated.Decorated _ d => erase d

/-- 擦除示例验证 -/
def erase_while_ex :
    erase_d dec_while = (WHILE (BNot (BEq (AId X) (ANum 0))) DO (X ::= AMinus (AId X) (ANum 1)) END) := by
  rfl

/-- 提取带标注程序的最外层前置条件 -/
def precondition_from (dec : decorated) : Assertion :=
  match dec with
  | decorated.Decorated P _ => P

/-- 提取带标注命令内嵌的最末后置条件 -/
def post (d : dcom) : Assertion :=
  match d with
  | dcom.DCSkip P => P
  | dcom.DCSeq _ d2 => post d2
  | dcom.DCAsgn _ _ Q => Q
  | dcom.DCIf _ _ _ _ _ Q => Q
  | dcom.DCWhile _ _ _ Q => Q
  | dcom.DCPre _ d => post d
  | dcom.DCPost _ Q => Q

/-- 提取带标注程序的最外层后置条件 -/
def postcondition_from (dec : decorated) : Assertion :=
  match dec with
  | decorated.Decorated _ d => post d

/-- 提取归零程序的前置条件示例 -/
def precondition_from_while : precondition_from dec_while = (fun _ => True) := by
  rfl

/-- 提取归零程序的后置条件示例 -/
def postcondition_from_while : postcondition_from dec_while = (fun st => st X = 0) := by
  rfl

/-- 带标注程序的外层三元组有效性定义 -/
def outer_triple_valid (dec : decorated) : Prop :=
  {{precondition_from dec}} (erase_d dec) {{postcondition_from dec}}

/-- 归零程序的外层三元组正确性规约 -/
def dec_while_triple_correct :
    outer_triple_valid dec_while =
      {{fun _ => True}}
        (WHILE (BNot (BEq (AId X) (ANum 0))) DO (X ::= AMinus (AId X) (ANum 1)) END)
      {{fun st => st X = 0}} := by
  rfl
```

### 3. 验证条件生成 (Verification Condition Generator)

`verification_conditions P d` 递归遍历带标注命令 `d` 并结合当前上下文供给的前置条件 `P`，
生成一组纯命题合取（Verification Conditions）。
若这组条件可被证明，则根据霍尔逻辑规则系统，三元组 `{{ P }} (erase d) {{ post d }}` 必定成立！

## 经典程序验证实例 (Classic Verified Programs)

```lean
/-- 核心验证条件生成函数 -/
def verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | dcom.DCSkip Q =>
      P ->> Q
  | dcom.DCSeq d1 d2 =>
      verification_conditions P d1 ∧
      verification_conditions (post d1) d2
  | dcom.DCAsgn X a Q =>
      P ->> (Q [ X ↦ a ])
  | dcom.DCIf b P1 d1 P2 d2 Q =>
      (fun st => P st ∧ bassertion b st) ->> P1 ∧
      (fun st => P st ∧ ¬ bassertion b st) ->> P2 ∧
      (post d1 ->> Q) ∧ (post d2 ->> Q) ∧
      verification_conditions P1 d1 ∧
      verification_conditions P2 d2
  | dcom.DCWhile b Q d R =>
      (P ->> post d) ∧
      (fun st => post d st ∧ bassertion b st) ->> Q ∧
      (fun st => post d st ∧ ¬ bassertion b st) ->> R ∧
      verification_conditions Q d
  | dcom.DCPre P' d =>
      (P ->> P') ∧
      verification_conditions P' d
  | dcom.DCPost d Q =>
      verification_conditions P d ∧
      (post d ->> Q)

/-- 核心定理：验证条件生成的健全性定理 -/
theorem verification_correct : ∀ d P,
  verification_conditions P d → {{P}} (erase d) {{post d}} := by
  intro d
  induction d with
  | DCSkip Q =>
    intro P H
    dsimp [verification_conditions, erase, post] at *
    apply hoare_consequence_pre (P' := Q)
    · apply hoare_skip
    · exact H
  | DCSeq d1 d2 ih1 ih2 =>
    intro P H
    dsimp [verification_conditions, erase, post] at *
    rcases H with ⟨H1, H2⟩
    apply hoare_seq (Q := post d1)
    · exact ih2 (post d1) H2
    · exact ih1 P H1
  | DCAsgn X a Q =>
    intro P H
    dsimp [verification_conditions, erase, post] at *
    apply hoare_consequence_pre (P' := Q [ X ↦ a ])
    · apply hoare_asgn
    · exact H
  | DCIf b P1 d1 P2 d2 Q ih1 ih2 =>
    intro P H
    dsimp [verification_conditions, erase, post] at *
    rcases H with ⟨HPre1, HPre2, Hpost1, Hpost2, Hd1, Hd2⟩
    apply hoare_if
    · apply hoare_consequence (P' := P1) (Q' := post d1)
      · exact ih1 P1 Hd1
      · exact HPre1
      · exact Hpost1
    · apply hoare_consequence (P' := P2) (Q' := post d2)
      · exact ih2 P2 Hd2
      · exact HPre2
      · exact Hpost2
  | DCWhile b Q d R ih =>
    intro P H
    dsimp [verification_conditions, erase, post] at *
    rcases H with ⟨Hpre, Hbody, Hpost, Hd⟩
    apply hoare_consequence_post (Q' := fun st => post d st ∧ ¬ bassertion b st)
    · apply hoare_consequence_pre (P' := post d)
      · apply hoare_while
        apply hoare_consequence_pre (P' := Q)
        · exact ih Q Hd
        · exact Hbody
      · exact Hpre
    · exact Hpost
  | DCPre P' d ih =>
    intro P H
    dsimp [verification_conditions, erase, post] at *
    rcases H with ⟨HP, Hd⟩
    apply hoare_consequence_pre (P' := P')
    · exact ih P' Hd
    · exact HP
  | DCPost d Q ih =>
    intro P H
    dsimp [verification_conditions, erase, post] at *
    rcases H with ⟨Hd, HQ⟩
    apply hoare_consequence_post (Q' := post d)
    · exact ih P Hd
    · exact HQ

/-- 生成整个带标注程序的验证条件 -/
def verification_conditions_from (dec : decorated) : Prop :=
  match dec with
  | decorated.Decorated P d => verification_conditions P d

/-- 推论：带标注程序全体验证条件成立可推出外层三元组有效 -/
theorem verification_conditions_correct : ∀ dec,
  verification_conditions_from dec → outer_triple_valid dec := by
  intro dec
  cases dec with
  | Decorated P d =>
    intro h
    exact verification_correct d P h

/-- 验证归零程序的验证条件 -/
def vc_dec_while : verification_conditions_from dec_while := by
  dsimp [dec_while, verification_conditions_from, verification_conditions, post, assert_implies, assertion_sub, bassertion, beval, aeval]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro st h; trivial
  · intro st ⟨_, hb⟩
    constructor
    · trivial
    · intro hx; rw [hx] at hb; revert hb; decide
  · intro st ⟨_, hb⟩
    constructor
    · trivial
    · cases h : (st X == 0) with
      | true => exact Nat.eq_of_beq_eq_true h
      | false =>
        have : (!(st X == 0)) = true := by rw [h]; rfl
        exact (hb this).elim
  · intro st _; trivial
  · intro st ⟨_, hx⟩; exact hx

/-- 归零程序验证条件的自动化放行 -/
theorem dec_while_correct :
  outer_triple_valid dec_while := by
  apply verification_conditions_correct
  exact vc_dec_while
```

### 4. 加减法无临时变量交换程序 (Swapping)

```lean
/-- 加减法变量交换带标注程序 -/
def swap_dec (m n : Nat) : decorated :=
  decorated.Decorated (fun st => st X = m ∧ st Y = n)
    (dcom.DCPre (fun st => (st X + st Y) - ((st X + st Y) - st Y) = n ∧ (st X + st Y) - st Y = m)
      (dcom.DCSeq
        (dcom.DCAsgn X (APlus (AId X) (AId Y))
          (fun st => st X - (st X - st Y) = n ∧ st X - st Y = m))
        (dcom.DCSeq
          (dcom.DCAsgn Y (AMinus (AId X) (AId Y))
            (fun st => st X - st Y = n ∧ st Y = m))
          (dcom.DCAsgn X (AMinus (AId X) (AId Y))
            (fun st => st X = n ∧ st Y = m)))))

/-- 交换程序正确性定理 -/
theorem swap_correct : ∀ m n,
  outer_triple_valid (swap_dec m n) := by
  intro m n
  apply verification_conditions_correct
  dsimp [swap_dec, verification_conditions_from, verification_conditions, post, assert_implies, assertion_sub, t_update]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro st ⟨hx, hy⟩; subst hx hy; omega
  · intro st h; exact h
  · intro st h; exact h
  · intro st h; exact h
```

### 5. 正差值计算 (Positive Difference)

```lean
/-- 正差值带标注程序 -/
def positive_difference_dec : decorated :=
  decorated.Decorated (fun _ => True)
    (dcom.DCIf (BLe (AId X) (AId Y))
      (fun st => (st Y - st X) + st X = st Y ∨ (st Y - st X) + st Y = st X)
      (dcom.DCAsgn Z (AMinus (AId Y) (AId X))
        (fun st => st Z + st X = st Y ∨ st Z + st Y = st X))
      (fun st => (st X - st Y) + st X = st Y ∨ (st X - st Y) + st Y = st X)
      (dcom.DCAsgn Z (AMinus (AId X) (AId Y))
        (fun st => st Z + st X = st Y ∨ st Z + st Y = st X))
      (fun st => st Z + st X = st Y ∨ st Z + st Y = st X))

/-- 正差值计算程序正确性 -/
theorem positive_difference_correct :
  outer_triple_valid positive_difference_dec := by
  apply verification_conditions_correct
  dsimp [positive_difference_dec, verification_conditions_from, verification_conditions, post, assert_implies, assertion_sub, bassertion, beval, aeval, t_update]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro st ⟨_, hle⟩
    have : st X ≤ st Y := of_decide_eq_true hle
    left; omega
  · intro st ⟨_, hnle⟩
    cases hdec : decide (st X ≤ st Y) with
    | true => contradiction
    | false =>
      have : st Y ≤ st X := by
        have := of_decide_eq_false hdec
        omega
      right; omega
  · intro st h; exact h
  · intro st h; exact h
  · intro st h; exact h
  · intro st h; exact h
```

**** 练习: 2 星, standard, optional (if_minus_plus_reloaded)
这是后面 `if_minus_plus_correct` 练习的绝佳热身。
为下列程序补充完整且合法的断言注解：
```
{{ True }}
  if X <= Y then
            {{ True ∧ X ≤ Y }} ->>
            {{ (Y - X) + X = Y ∨ (Y - X) + Y = X }}
    Z := Y - X
            {{ Y = X + Z }}
  else
            {{ True ∧ ¬(X ≤ Y) }} ->>
            {{ True }}
    Y := X + Z
            {{ Y = X + Z }}
  end
{{ Y = X + Z }}
```

## 循环不变量构造艺术 (Finding Loop Invariants)

```lean
/-- 条件分支减加程序 -/
def if_minus_plus_dec : decorated :=
  decorated.Decorated (fun _ => True)
    (dcom.DCIf (BLe (AId X) (AId Y))
      (fun st => (st Y - st X) + st X = st Y ∨ (st Y - st X) + st Y = st X)
      (dcom.DCAsgn Z (AMinus (AId Y) (AId X))
        (fun st => st Y = st X + st Z))
      (fun _ => True)
      (dcom.DCAsgn Y (APlus (AId X) (AId Z))
        (fun st => st Y = st X + st Z))
      (fun st => st Y = st X + st Z))

/--
**** 练习: 2 星, standard, especially useful (if_minus_plus_correct)
-/
theorem if_minus_plus_correct :
  outer_triple_valid if_minus_plus_dec := by
  sorry

/-- 整除与取模程序 -/
def div_mod_dec (a b : Nat) : decorated :=
  decorated.Decorated (fun _ => True)
    (dcom.DCPre (fun _ => a = a)
      (dcom.DCSeq
        (dcom.DCAsgn X (ANum a) (fun st => st X = a))
        (dcom.DCSeq
          (dcom.DCAsgn Y (ANum 0) (fun st => st X = a ∧ st Y = 0))
          (dcom.DCPost
            (dcom.DCWhile (BLe (ANum b) (AId X))
              (fun st => (st X - b) + (st Y + 1) * b = a)
              (dcom.DCSeq
                (dcom.DCAsgn X (AMinus (AId X) (ANum b))
                  (fun st => st X + (st Y + 1) * b = a))
                (dcom.DCAsgn Y (APlus (AId Y) (ANum 1))
                  (fun st => st X + st Y * b = a)))
              (fun st => st X + st Y * b = a ∧ ¬ (b ≤ st X)))
            (fun st => st X + st Y * b = a)))))

/--
**** 练习: 2 星, standard, optional (div_mod_outer_triple_valid)
-/
theorem div_mod_outer_triple_valid : ∀ a b,
  outer_triple_valid (div_mod_dec a b) := by
  sorry
```

### 6. 慢速减法 (Slow Subtraction)

```lean
/-- 慢速减法带标注程序 -/
def subtract_slowly_dec (m n : Nat) : decorated :=
  decorated.Decorated (fun st => st X = m ∧ st Y = n)
    (dcom.DCPre (fun st => st Y - st X = n - m)
      (dcom.DCPost
        (dcom.DCWhile (BNot (BEq (AId X) (ANum 0)))
          (fun st => (st Y - 1) - (st X - 1) = n - m)
          (dcom.DCSeq
            (dcom.DCAsgn Y (AMinus (AId Y) (ANum 1))
              (fun st => st Y - (st X - 1) = n - m))
            (dcom.DCAsgn X (AMinus (AId X) (ANum 1))
              (fun st => st Y - st X = n - m)))
          (fun st => st Y - st X = n - m ∧ st X = 0))
        (fun st => st Y = n - m)))

/-- 慢速减法正确性 -/
theorem subtract_slowly_outer_triple_valid : ∀ m n,
  outer_triple_valid (subtract_slowly_dec m n) := by
  intro m n
  apply verification_conditions_correct
  dsimp [subtract_slowly_dec, verification_conditions_from, verification_conditions, post, assert_implies, assertion_sub, bassertion, beval, aeval, t_update]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro st ⟨hx, hy⟩; subst hx hy; rfl
  · intro st h; exact h
  · intro st ⟨hinv, hb⟩
    have hx : st X ≠ 0 := by
      intro hc; rw [hc] at hb; revert hb; decide
    omega
  · intro st ⟨hinv, hb⟩
    have hx : st X = 0 := by
      cases h : (st X == 0) with
      | true => exact Nat.eq_of_beq_eq_true h
      | false =>
        have : (!(st X == 0)) = true := by rw [h]; rfl
        exact (hb this).elim
    exact ⟨hinv, hx⟩
  · intro st h; exact h
  · intro st h; exact h
  · intro st ⟨hinv, hx⟩
    rw [hx] at hinv
    omega

/-- 慢速赋值带标注程序 -/
def slow_assignment_dec (m : Nat) : decorated :=
  decorated.Decorated (fun st => st X = m)
    (dcom.DCSeq
      (dcom.DCAsgn Y (ANum 0) (fun st => st X = m ∧ st Y = 0))
      (dcom.DCPre (fun st => st X + st Y = m)
        (dcom.DCPost
          (dcom.DCWhile (BNot (BEq (AId X) (ANum 0)))
            (fun st => (st X - 1) + (st Y + 1) = m)
            (dcom.DCSeq
              (dcom.DCAsgn X (AMinus (AId X) (ANum 1))
                (fun st => st X + (st Y + 1) = m))
              (dcom.DCAsgn Y (APlus (AId Y) (ANum 1))
                (fun st => st X + st Y = m)))
            (fun st => ¬ (st X ≠ 0) ∧ st Y = m))
          (fun st => st Y = m))))

/--
**** 练习: 2 星, standard (slow_assignment)
-/
theorem slow_assignment : ∀ m,
  outer_triple_valid (slow_assignment_dec m) := by
  sorry
```

### 7. 奇偶性检验 (Parity)

```lean
/-- 奇偶性递归函数 -/
def parity (x : Nat) : Nat :=
  match x with
  | 0 => 0
  | 1 => 1
  | x' + 2 => parity x'

/-- 奇偶性计算带标注程序 -/
def parity_dec (m : Nat) : decorated :=
  decorated.Decorated (fun st => st X = m)
    (dcom.DCPre (fun st => parity (st X) = parity m)
      (dcom.DCPost
        (dcom.DCWhile (BLe (ANum 2) (AId X))
          (fun st => parity (st X - 2) = parity m)
          (dcom.DCAsgn X (AMinus (AId X) (ANum 2))
            (fun st => parity (st X) = parity m))
          (fun st => parity (st X) = parity m ∧ ¬ (2 ≤ st X)))
        (fun st => st X = parity m)))

/-- 引理：减 2 保持奇偶性 -/
theorem parity_ge_2 : ∀ x, 2 ≤ x → parity (x - 2) = parity x := by
  intro x
  match x with
  | 0 => intro h; omega
  | 1 => intro h; omega
  | x' + 2 =>
    intro _
    show parity x' = parity (x' + 2)
    rfl

/-- 引理：小于 2 的奇偶性为其自身 -/
theorem parity_lt_2 : ∀ x, ¬ 2 ≤ x → parity x = x := by
  intro x
  match x with
  | 0 => intro _; rfl
  | 1 => intro _; rfl
  | x' + 2 => intro h; exfalso; apply h; omega

/--
**** 练习: 3 星, standard, optional (parity)
-/
theorem parity_outer_triple_valid : ∀ m,
  outer_triple_valid (parity_dec m) := by
  sorry
```

### 8. 整数平方根 (Square Roots)

```lean
/-- 整数平方根带标注程序 -/
def sqrt_dec (m : Nat) : decorated :=
  decorated.Decorated (fun st => st X = m)
    (dcom.DCPre (fun st => st X = m ∧ 0 * 0 ≤ m)
      (dcom.DCSeq
        (dcom.DCAsgn Z (ANum 0) (fun st => st X = m ∧ st Z * st Z ≤ m))
        (dcom.DCPost
          (dcom.DCWhile (BLe (AMult (APlus (AId Z) (ANum 1)) (APlus (AId Z) (ANum 1))) (AId X))
            (fun st => st X = m ∧ (st Z + 1) * (st Z + 1) ≤ st X)
            (dcom.DCAsgn Z (APlus (AId Z) (ANum 1))
              (fun st => st X = m ∧ st Z * st Z ≤ m))
            (fun st => st X = m ∧ st Z * st Z ≤ m ∧ ¬ ((st Z + 1) * (st Z + 1) ≤ st X)))
          (fun st => st Z * st Z ≤ m ∧ m < (st Z + 1) * (st Z + 1)))))

/--
**** 练习: 3 星, standard, optional (sqrt)
-/
theorem sqrt_correct : ∀ m,
  outer_triple_valid (sqrt_dec m) := by
  sorry
```

### 9. 阶乘计算 (Factorial)

```lean
/-- 递归阶乘函数 -/
def fact (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n' + 1 => (n' + 1) * fact n'

/-- 阶乘计算带标注程序 -/
def factorial_dec (m : Nat) : decorated :=
  decorated.Decorated (fun st => st X = m)
    (dcom.DCSeq
      (dcom.DCAsgn Y (ANum 1) (fun st => st X = m ∧ st Y = 1))
      (dcom.DCPre (fun st => st Y * fact (st X) = fact m)
        (dcom.DCPost
          (dcom.DCWhile (BNot (BEq (AId X) (ANum 0)))
            (fun st => st X * st Y * fact (st X - 1) = fact m)
            (dcom.DCSeq
              (dcom.DCAsgn Y (AMult (AId X) (AId Y))
                (fun st => st Y * fact (st X - 1) = fact m))
              (dcom.DCAsgn X (AMinus (AId X) (ANum 1))
                (fun st => st Y * fact (st X) = fact m)))
            (fun st => ¬ (st X ≠ 0) ∧ st Y = fact m))
          (fun st => st Y = fact m))))

/--
**** 练习: 4 星, advanced (factorial_correct)
-/
theorem factorial_correct : ∀ m,
  outer_triple_valid (factorial_dec m) := by
  sorry
```

### 10. 最小值求解 (Minimum)

```lean
/-- 最小值计算带标注程序 -/
def minimum_dec (a b : Nat) : decorated :=
  decorated.Decorated (fun _ => True)
    (dcom.DCPre (fun _ => a = a)
      (dcom.DCSeq
        (dcom.DCAsgn X (ANum a) (fun st => st X = a))
        (dcom.DCSeq
          (dcom.DCAsgn Y (ANum b) (fun st => st X = a ∧ st Y = b))
          (dcom.DCSeq
            (dcom.DCAsgn Z (ANum 0) (fun st => min (st X) (st Y) + st Z = min a b))
            (dcom.DCPost
              (dcom.DCWhile (BAnd (BNot (BEq (AId X) (ANum 0))) (BNot (BEq (AId Y) (ANum 0))))
                (fun st => min (st X - 1) (st Y - 1) + (st Z + 1) = min a b)
                (dcom.DCSeq
                  (dcom.DCAsgn X (AMinus (AId X) (ANum 1))
                    (fun st => min (st X) (st Y - 1) + (st Z + 1) = min a b))
                  (dcom.DCSeq
                    (dcom.DCAsgn Y (AMinus (AId Y) (ANum 1))
                      (fun st => min (st X) (st Y) + (st Z + 1) = min a b))
                    (dcom.DCAsgn Z (APlus (AId Z) (ANum 1))
                      (fun st => min (st X) (st Y) + st Z = min a b))))
                (fun st => ¬ (st X ≠ 0 ∧ st Y ≠ 0) ∧ min (st X) (st Y) + st Z = min a b))
              (fun st => st Z = min a b))))))

/--
**** 练习: 3 星, advanced (minimum_correct)
-/
theorem minimum_correct : ∀ a b,
  outer_triple_valid (minimum_dec a b) := by
  sorry
```

### 11. 双重循环 (Two Loops)

```lean
/-- 双重循环累加带标注程序 -/
def two_loops_dec (a b c : Nat) : decorated :=
  decorated.Decorated (fun _ => True)
    (dcom.DCPre (fun _ => (0 : Nat) = 0)
      (dcom.DCSeq
        (dcom.DCAsgn X (ANum 0) (fun st => st X = 0))
        (dcom.DCSeq
          (dcom.DCAsgn Y (ANum 0) (fun st => st X = 0 ∧ st Y = 0))
          (dcom.DCSeq
            (dcom.DCAsgn Z (ANum c) (fun st => st Z = st X + st Y + c))
            (dcom.DCSeq
              (dcom.DCPost
                (dcom.DCWhile (BNot (BEq (AId X) (ANum a)))
                  (fun st => st Z + 1 = (st X + 1) + st Y + c)
                  (dcom.DCSeq
                    (dcom.DCAsgn X (APlus (AId X) (ANum 1))
                      (fun st => st Z + 1 = st X + st Y + c))
                    (dcom.DCAsgn Z (APlus (AId Z) (ANum 1))
                      (fun st => st Z = st X + st Y + c)))
                  (fun st => st Z = st X + st Y + c ∧ ¬ (st X ≠ a)))
                (fun st => st Z = a + st Y + c))
              (dcom.DCPost
                (dcom.DCWhile (BNot (BEq (AId Y) (ANum b)))
                  (fun st => st Z + 1 = a + (st Y + 1) + c)
                  (dcom.DCSeq
                    (dcom.DCAsgn Y (APlus (AId Y) (ANum 1))
                      (fun st => st Z + 1 = a + st Y + c))
                    (dcom.DCAsgn Z (APlus (AId Z) (ANum 1))
                      (fun st => st Z = a + st Y + c)))
                  (fun st => st Z = a + st Y + c ∧ ¬ (st Y ≠ b)))
                (fun st => st Z = a + b + c)))))))

/--
**** 练习: 3 星, standard (two_loops)
-/
theorem two_loops : ∀ a b c,
  outer_triple_valid (two_loops_dec a b c) := by
  sorry
```

### 12. 幂级数求和 (Power Series)

```lean
/-- 2 的幂函数 -/
def pow2 (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n' + 1 => 2 * pow2 n'

/-- 幂级数求和带标注程序 -/
def dpow2_dec (n : Nat) : decorated :=
  decorated.Decorated (fun _ => True)
    (dcom.DCPre (fun _ => (0 : Nat) = 0)
      (dcom.DCSeq
        (dcom.DCAsgn X (ANum 0) (fun st => st X = 0))
        (dcom.DCSeq
          (dcom.DCAsgn Y (ANum 1) (fun st => st X = 0 ∧ st Y = 1))
          (dcom.DCSeq
            (dcom.DCAsgn Z (ANum 1) (fun st => st Y = st Z + pow2 (st X) - 1 ∧ st Z = pow2 (st X)))
            (dcom.DCPost
              (dcom.DCWhile (BNot (BEq (AId X) (ANum n)))
                (fun st => st Y + 2 * st Z = 2 * st Z + pow2 (st X + 1) - 1 ∧ 2 * st Z = pow2 (st X + 1))
                (dcom.DCSeq
                  (dcom.DCAsgn Z (AMult (ANum 2) (AId Z))
                    (fun st => st Y + st Z = st Z + pow2 (st X + 1) - 1 ∧ st Z = pow2 (st X + 1)))
                  (dcom.DCSeq
                    (dcom.DCAsgn Y (APlus (AId Y) (AId Z))
                      (fun st => st Y = st Z + pow2 (st X + 1) - 1 ∧ st Z = pow2 (st X + 1)))
                    (dcom.DCAsgn X (APlus (AId X) (ANum 1))
                      (fun st => st Y = st Z + pow2 (st X) - 1 ∧ st Z = pow2 (st X)))))
                (fun st => st Y = st Z + pow2 (st X) - 1 ∧ st Z = pow2 (st X) ∧ ¬ (st X ≠ n)))
              (fun st => st Y = pow2 (n + 1) - 1))))))

/-- 幂递推引理 -/
theorem pow2_plus_1 : ∀ n, pow2 (n + 1) = pow2 n + pow2 n := by
  intro n
  dsimp [pow2]
  omega

/-- 幂大于等于 1 引理 -/
theorem pow2_le_1 : ∀ n, pow2 n ≥ 1 := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    dsimp [pow2]
    omega

/--
**** 练习: 4 星, standard, optional (dpow2)
-/
theorem dpow2_down_correct : ∀ n,
  outer_triple_valid (dpow2_dec n) := by
  sorry
```

### 13. 斐波那契数列计算 (Fibonacci)

### 极简带标注程序 (Improved Decorated Commands)

```lean
/-- 斐波那契数列递归定义 -/
def fib (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | n'' + 2 => fib (n'' + 1) + fib n''

/--
**** 练习: 2 星, advanced, optional (fib_eqn)
-/
theorem fib_eqn : ∀ n,
  n > 0 → fib n + fib (n - 1) = fib (1 + n) := by
  sorry

/-- 辅助变量 T -/
def T : String := "T"

/-- 斐波那契带标注程序 -/
def dfib (n : Nat) : decorated :=
  decorated.Decorated (fun _ => True)
    (dcom.DCPre (fun _ => (1 : Nat) = 1)
      (dcom.DCSeq
        (dcom.DCAsgn X (ANum 1) (fun st => st X = 1))
        (dcom.DCSeq
          (dcom.DCAsgn Y (ANum 1) (fun st => st X = 1 ∧ st Y = 1))
          (dcom.DCSeq
            (dcom.DCAsgn Z (ANum 1) (fun st => st Z = fib (st X) ∧ st Y = fib (st X - 1) ∧ st X > 0))
            (dcom.DCPost
              (dcom.DCWhile (BNot (BEq (AId X) (ANum (1 + n))))
                (fun st => st Z + st Y = fib (1 + st X) ∧ st Z = fib (st X) ∧ st X > 0)
                (dcom.DCSeq
                  (dcom.DCAsgn T (AId Z)
                    (fun st => st Z + st Y = fib (1 + st X) ∧ st Z = fib (st X) ∧ st T = st Z ∧ st X > 0))
                  (dcom.DCSeq
                    (dcom.DCAsgn Z (APlus (AId Z) (AId Y))
                      (fun st => st Z = fib (1 + st X) ∧ st T = fib (st X) ∧ st X > 0))
                    (dcom.DCSeq
                      (dcom.DCAsgn Y (AId T)
                        (fun st => st Z = fib (1 + st X) ∧ st Y = fib (st X) ∧ st X > 0))
                      (dcom.DCAsgn X (APlus (ANum 1) (AId X))
                        (fun st => st Z = fib (st X) ∧ st Y = fib (st X - 1) ∧ st X > 0)))))
                (fun st => st Z = fib (st X) ∧ st Y = fib (st X - 1) ∧ st X > 0 ∧ ¬ (st X ≠ 1 + n)))
              (fun st => st Y = fib n))))))

/--
**** 练习: 4 星, advanced, optional (fib)
-/
theorem dfib_correct : ∀ n,
  outer_triple_valid (dfib n) := by
  sorry
```

### 14. 极简标注语法模块 (DComImproved)

在实际验证工具中，绝大多数顺序复合与赋值语句的局部断言均可机械向前/向后传播，
无需人工逐行书写。通过仅在最终后置条件与循环入口处要求显式标注，可大幅简化带标注程序。

## 最弱前置条件 (Weakest Preconditions)

```lean
namespace DComImproved

/-- 极简带标注命令 -/
inductive dcom : Type where
  | DCSkip : dcom
  | DCSeq (d1 d2 : dcom) : dcom
  | DCAsgn (X : String) (a : aexp) : dcom
  | DCIf (b : bexp) (d1 d2 : dcom) : dcom
  | DCWhile (b : bexp) (P : Assertion) (d : dcom) (Q : Assertion) : dcom
  | DCPost (d : dcom) (Q : Assertion) : dcom

/-- 极简带标注命令的后置条件计算 -/
def post (d : dcom) : Assertion :=
  match d with
  | dcom.DCSkip => fun _ => True
  | dcom.DCSeq _ d2 => post d2
  | dcom.DCAsgn _ _ => fun _ => True
  | dcom.DCIf _ d1 d2 => fun st => post d1 st ∨ post d2 st
  | dcom.DCWhile _ _ _ Q => Q
  | dcom.DCPost _ Q => Q

/-- 极简带标注命令的擦除函数 -/
def erase (d : dcom) : com :=
  match d with
  | dcom.DCSkip => com.CSkip
  | dcom.DCSeq d1 d2 => com.CSeq (erase d1) (erase d2)
  | dcom.DCAsgn X a => com.CAsgn X a
  | dcom.DCIf b d1 d2 => com.CIf b (erase d1) (erase d2)
  | dcom.DCWhile b _ d _ => com.CWhile b (erase d)
  | dcom.DCPost d _ => erase d

/-- 极简验证条件生成 -/
def verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | dcom.DCSkip => True
  | dcom.DCSeq d1 d2 =>
      verification_conditions P d1 ∧
      verification_conditions (post d1) d2
  | dcom.DCAsgn X a =>
      P ->> (P [ X ↦ a ])
  | dcom.DCIf b d1 d2 =>
      verification_conditions (fun st => P st ∧ bassertion b st) d1 ∧
      verification_conditions (fun st => P st ∧ ¬ bassertion b st) d2
  | dcom.DCWhile b Q d R =>
      (P ->> post d) ∧
      (fun st => post d st ∧ bassertion b st) ->> Q ∧
      (fun st => post d st ∧ ¬ bassertion b st) ->> R ∧
      verification_conditions Q d
  | dcom.DCPost d Q =>
      verification_conditions P d ∧
      (post d ->> Q)

/--
**** 练习: 5 星, advanced, optional (improve_dcom)
-/
theorem verification_correct : ∀ d P,
  verification_conditions P d → {{P}} (erase d) {{post d}} := by
  sorry

end DComImproved
```

### 15. 最弱前置条件的形式化

断言 `P` 称为命令 `c` 关于后置条件 `Q` 的**最弱前置条件 (Weakest Precondition, WP)**，
若且唯若：
1. `{{ P }} c {{ Q }}` 成立；
2. 对于任意其它满足 `{{ P' }} c {{ Q }}` 的前置条件 `P'`，均有 `P' ->> P`。

```lean
/-- 最弱前置条件形式化定义 -/
def is_wp (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  {{P}} c {{Q}} ∧ ∀ P', {{P'}} c {{Q}} → (P' ->> P)
```

**** 练习: 1 星, standard, optional (wp)
指出下列各命令关于各后置条件的最弱前置条件：
1) `skip {{ X = 5 }}`：最弱前置条件为 `X = 5`。
2) `X := Y + Z {{ X = 5 }}`：最弱前置条件为 `Y + Z = 5`。
3) `X := Y {{ X = Y }}`：最弱前置条件为 `True`（因为 `Y = Y` 恒真）。
4) `TEST X = 0 THEN Y := Z + 1 ELSE Y := W + 2 FI {{ Y = 5 }}`：最弱前置条件为 `(X = 0 ∧ Z + 1 = 5) ∨ (X ≠ 0 ∧ W + 2 = 5)`。
5) `X := 5 {{ X = 0 }}`：最弱前置条件为 `False`（赋值 5 后绝不可能为 0）。
6) `WHILE true DO X := 0 END {{ X = 0 }}`：最弱前置条件为 `True`（程序永不终止，部分正确性下三元组无条件虚真成立）。

```lean
/--
**** 练习: 3 星, advanced, optional (is_wp)
-/
theorem is_wp_example :
  is_wp (fun st => st Y ≤ 4) (X ::= AId Y + ANum 1) (fun st => st X ≤ 5) := by
  sorry

/--
**** 练习: 2 星, advanced, optional (hoare_asgn_weakest)
-/
theorem hoare_asgn_weakest : ∀ Q X a,
  is_wp (Q [ X ↦ a ]) (X ::= a) Q := by
  sorry

namespace Himp2

open PLF.Hoare.Himp

/--
**** 练习: 2 星, advanced, optional (hoare_havoc_weakest)
-/
theorem hoare_havoc_weakest : ∀ (P Q : Assertion) (X : String),
  valid_hoare_triple P (com.CHavoc X) Q →
  (P ->> havoc_pre X Q) := by
  sorry

end Himp2

end PLF.Hoare2
```
