---
title: "Hoare: 霍尔逻辑 (I)：三元组、赋值规则与前向后向推理"
---

```lean
import SFLean4.LF.Basics
import SFLean4.LF.Induction
import SFLean4.LF.Maps
import SFLean4.LF.Imp
import SFLean4.PLF.Equiv

set_option linter.defProp false
set_option linter.ambiguousOpen false
set_option linter.unusedVariables false
```

# 《软件基础》(Software Foundations) 卷二：程序语言基础 (PLF)

## 第二章：霍尔逻辑（第一部分）(Hoare: Hoare Logic, Part I)

在卷一《逻辑基础》(LF) 的最后一章中，我们开始运用所掌握的数学与逻辑工具来研究一种小型的命令式编程语言——Imp：
- 我们为 Imp 定义了抽象语法树（AST），并引入了大步求值关系（关系式操作语义 `st =[ c ]=> st'`）。
- 我们证明了一系列**元理论性质（Metatheoretic Properties）**，例如求值的确定性、程序转换的保意性（常量折叠）、以及程序的行为等价性（[Equiv](file:///Users/ghostface/LuoJin/SF-lean4/SFLean4/PLF/Equiv.lean) 章节）。

然而，在软件工程与形式化验证中，一个更核心的任务是**程序验证（Program Verification）**：
即利用程序语言的形式化语义，严格证明**特定具体程序**是否满足关于其运行时行为的**形式化规约（Specification）**。

为此，本章我们将建立由 Tony Hoare（基于 Robert Floyd 的早期思想）于 1969 年提出的经典推理系统——**弗洛伊德-霍尔逻辑（Floyd-Hoare Logic）**，通常简称为**霍尔逻辑（Hoare Logic）**。

### 霍尔逻辑的核心思想：
1. **结构化规约（Structured Specifications）**：
   通过**霍尔三元组（Hoare Triple）** `{{ P }} c {{ Q }}` 表达程序规约，其中 `P` 为前置条件（Precondition），`c` 为程序命令，`Q` 为后置条件（Postcondition）。
   其直观含义是：若命令 `c` 在满足断言 `P` 的初始状态下开始执行，并且 `c` 最终终止，则终止时的最终状态必然满足断言 `Q`。
2. **组合式推理规则（Compositional Proof Rules）**：
   为语言的每一种语法结构（`SKIP`、赋值、顺序执行、条件分支、`WHILE` 循环）配备一条推理公理或规则，使得对复合程序的正确性证明可以精确拆解为对其子成分的正确性证明，证明的结构直接映射程序的语法结构。
3. **部分正确性（Partial Correctness）**：
   霍尔三元组仅保证“若程序终止则结论成立”，无需在三元组内部证明程序一定会终止。

---

## 断言 (Assertions)

```lean
namespace PLF.Hoare

open Imp
open Maps
open aexp bexp com
```

### 1. 状态断言 (Assertions)

断言是关于程序内存状态（`state`）的逻辑主张。在形式化逻辑中，断言就是一个状态的一元谓词：
`state → Prop`。

```lean
/-- 断言类型：从内存状态到命题的函数 -/
def Assertion : Type := state → Prop

namespace ExAssertions
```

**** 练习: 1 星, standard, optional (assertions)
使用自然语言（中文）转述下列断言的含义。

### 断言记号与提升 (Notations for Assertions)

### 断言蕴含 (Assertion Implication)

```lean
/-- 断言 1：状态中变量 X 的值不大于变量 Y 的值 -/
def assertion1 : Assertion := fun st => st X ≤ st Y

/-- 断言 2：变量 X 的值为 3，或者 X 的值不大于 Y 的值 -/
def assertion2 : Assertion :=
  fun st => st X = 3 ∨ st X ≤ st Y

/-- 断言 3：Z 是 X 的整数平方根（即 Z² ≤ X 且 (Z+1)² > X） -/
def assertion3 : Assertion :=
  fun st => st Z * st Z ≤ st X ∧
            ¬ (((st Z + 1) * (st Z + 1)) ≤ st X)

/-- 断言 4：Z 的值等于 X 和 Y 中的最大值 -/
def assertion4 : Assertion :=
  fun st => st Z = max (st X) (st Y)

end ExAssertions


/-- 算术表达式断言类型：从状态到自然数的映射 -/
def Aexp : Type := state → Nat

/-- 将一般 Prop 命题提升为与状态无关的恒常断言 -/
def assert_of_Prop (P : Prop) : Assertion := fun _ => P

/-- 将自然数提升为常数算术断言 -/
def Aexp_of_nat (n : Nat) : Aexp := fun _ => n

/-- 将 Imp 算术表达式 `aexp` 提升为求值函数 `Aexp` -/
def Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a

instance : Coe Prop Assertion where coe P := assert_of_Prop P
instance : Coe Nat Aexp where coe n := Aexp_of_nat n
instance : Coe aexp Aexp where coe a := Aexp_of_aexp a

namespace ExamplePrettyAssertions

def assertion1 : Assertion := fun st => st X = 3
def assertion2 : Assertion := fun _ => True
def assertion3 : Assertion := fun _ => False
def assertion4 : Assertion := fun _ => True ∨ False
def assertion5 : Assertion := fun st => st X ≤ st Y
def assertion6 : Assertion := fun st => st X = 3 ∨ st X ≤ st Y
def assertion7 : Assertion := fun st => st Z = max (st X) (st Y)
def assertion8 : Assertion := fun st => st Z * st Z ≤ st X ∧ ¬ ((st Z + 1) * (st Z + 1) ≤ st X)
def assertion9 : Assertion := fun st => st X + st Y > max (st Y) (st X)

end ExamplePrettyAssertions
```

### 2. 断言的蕴含关系

给定两个断言 `P` 与 `Q`，若在任意状态下只要 `P` 成立则 `Q` 亦成立，我们称 `P` 蕴含 `Q`，记作 `P ->> Q`。
若两者互相蕴含，则记作 `P <<->> Q`。

## 霍尔三元组 (Hoare Triples)

```lean
/-- 断言蕴含关系 -/
def assert_implies (P Q : Assertion) : Prop :=
  ∀ st, P st → Q st

infix:80 " ->> " => assert_implies

notation:80 P " <<->> " Q => (P ->> Q) ∧ (Q ->> P)
```

### 3. 霍尔三元组的形式化定义

霍尔三元组的直观表达为：
`{{ P }} c {{ Q }}`
表示：若命令 `c` 在满足前置条件 `P` 的状态 `st` 下执行，并最终终止于状态 `st'`，则 `st'` 必然满足后置条件 `Q`。

```lean
/-- 形式化霍尔三元组有效性定义 -/
def valid_hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  ∀ st st', st =[ c ]=> st' → P st → Q st'

/-- 语法包装：Imp 命令外层括号 -/
syntax "<{" term "}>" : term
macro_rules
  | `(<{$c}>) => `($c)

/-- 语法包装：霍尔三元组表示法 -/
syntax (name := hoare_triple) "{{" term "}}" term:max "{{" term "}}" : term
macro_rules
  | `({{$P}} $c {{$Q}}) => `(valid_hoare_triple $P $c $Q)
```

**** 练习: 1 星, standard, optional (triples)
转述下列霍尔三元组的自然语言含义：
1) `{{True}} c {{X = 5}}`：程序 c 终止时 X 的值必然为 5。
2) `∀ m, {{X = m}} c {{X = m + 5}}`：程序 c 将 X 的值增加 5。
3) `{{X <= Y}} c {{Y <= X}}`：若初始时 X ≤ Y，则终止时 Y ≤ X。
4) `{{True}} c {{False}}`：程序 c 绝不会正常终止（必然死循环发散）。
5) `∀ m, {{X = m}} c {{Y = real_fact m}}`：程序 c 计算 X 的阶乘并存入 Y。
6) `∀ m, {{X = m}} c {{Z * Z <= m ∧ ¬ ((Z + 1) * (Z + 1) <= m)}}`：程序 c 计算 X 的整数平方根存入 Z。

**** 练习: 1 星, standard, optional (valid_triples)
判断各三元组是否有效：
1) `{{True}} X := 5 {{X = 5}}`：有效。
2) `{{X = 2}} X := X + 1 {{X = 3}}`：有效。
3) `{{True}} X := 5; Y := 0 {{X = 5}}`：有效。
4) `{{X = 2 ∧ X = 3}} X := 5 {{X = 0}}`：有效（前置条件自相矛盾即为假，虚真）。
5) `{{True}} skip {{False}}`：无效（skip 必定终止）。
6) `{{False}} skip {{True}}`：有效（虚真）。
7) `{{True}} while true do skip end {{False}}`：有效（循环永不终止）。
8) `{{X = 0}} while X = 0 do X := X + 1 end {{X = 1}}`：有效。
9) `{{X = 1}} while X <> 0 do X := X + 1 end {{X = 100}}`：有效（死循环永不终止，结论虚真）。

## 证明规则 (Proof Rules)

```lean
/--
**** 练习: 1 星, standard (hoare_post_true)
若后置条件在任意状态下均恒真，则任何以其为后置条件的三元组皆有效。
-/
theorem hoare_post_true : ∀ (P Q : Assertion) (c : com),
  (∀ st, Q st) →
  {{P}} c {{Q}} := by
  sorry

/--
**** 练习: 1 星, standard, optional (hoare_pre_false)
若前置条件在任意状态下皆不成立，则任何以其为前置条件的三元组皆平凡有效。
-/
theorem hoare_pre_false : ∀ (P Q : Assertion) (c : com),
  (∀ st, ¬ P st) →
  {{P}} c {{Q}} := by
  sorry
```

### 4. 结构化证明规则 (Proof Rules)

### 空操作规则 (Skip)

### 顺序复合规则 (Sequencing)

### 赋值规则 (Assignment)

```lean
/-- 空操作证明规则：SKIP 保持任意断言 P -/
theorem hoare_skip : ∀ P,
  {{P}} SKIP {{P}} := by
  intro P st st' H HP
  cases H
  exact HP


/-- 顺序执行证明规则 -/
theorem hoare_seq : ∀ P Q R c1 c2,
  {{Q}} c2 {{R}} →
  {{P}} c1 {{Q}} →
  {{P}} (c1 ;; c2) {{R}} := by
  intro P Q R c1 c2 H2 H1 st st' H12 HP
  cases H12 with
  | E_Seq _ _ _ st_mid _ h1 h2 =>
    have hq := H1 st st_mid h1 HP
    exact H2 st_mid st' h2 hq
```

### 5. 赋值规则与断言代换 (Assertion Substitution)

赋值语句 `X := a` 的后置条件若为 `Q`，则其最弱前置条件是将 `Q` 中所有对变量 `X` 的读取替换为表达式 `a`。
在形式化中，断言是状态函数，因此“代换”等价于在更新后的状态 `t_update st X (aeval st a)` 下评估 `Q`。

```lean
/-- 断言代换：在更新状态下对断言进行评估 -/
def assertion_sub (X : String) (a : aexp) (P : Assertion) : Assertion :=
  fun st => P (t_update st X (aeval st a))

notation:90 P " [ " X " ↦ " a " ] " => assertion_sub X a P
notation:90 P " [ " X " |=> " a " ] " => assertion_sub X a P

namespace ExampleAssertionSub

theorem equivalent_assertion1 :
  (fun st => st X ≤ 5) [ X ↦ ANum 3 ] <<->> (fun _ => 3 ≤ 5) := by
  constructor <;> intro st H <;> exact H

theorem equivalent_assertion2 :
  (fun st => st X ≤ 5) [ X ↦ (AId X + ANum 1) ] <<->> (fun st => st X + 1 ≤ 5) := by
  constructor <;> intro st H <;> exact H

end ExampleAssertionSub

/-- 霍尔逻辑核心赋值规则 -/
theorem hoare_asgn : ∀ Q X a,
  {{Q [ X ↦ a ]}} (X ::= a) {{Q}} := by
  intro Q X a st st' HE HQ
  cases HE with
  | E_Asgn _ _ n _ heq =>
    dsimp [assertion_sub] at HQ
    subst heq
    exact HQ

theorem assertion_sub_example :
  {{(fun st => st X < 5) [ X ↦ (AId X + ANum 1) ]}}
    (X ::= AId X + ANum 1)
  {{fun st => st X < 5}} := by
  apply hoare_asgn
```

**** 练习: 2 星, standard, optional (hoare_asgn_examples1)

```lean
theorem hoare_asgn_examples1 :
  ∃ P,
    {{ P }}
      (X ::= ANum 2 * AId X)
    {{ fun st => st X ≤ 10 }} := by
  sorry
```

**** 练习: 2 星, standard, optional (hoare_asgn_examples2)

### 结果推论规则 (Rule of Consequence)

```lean
theorem hoare_asgn_examples2 :
  ∃ P,
    {{ P }}
      (X ::= ANum 3)
    {{ fun st => 0 ≤ st X ∧ st X ≤ 5 }} := by
  sorry

/--
**** 练习: 2 星, standard, especially useful (hoare_asgn_wrong)
反向赋值规则常常与初学者的前向直觉相悖。证明前向朴素猜测规则 `{{True}} X := a {{X = a}}` 是不成立的。
-/
theorem hoare_asgn_wrong : ∃ a : aexp,
  ¬ {{fun _ => True}} (X ::= a) {{fun st => st X = aeval st a}} := by
  sorry

/--
**** 练习: 3 星, advanced, optional (hoare_asgn_fwd)
通过辅助参数 `m` 记录变量初始值，构造可靠的前向赋值推理规则。
-/
theorem hoare_asgn_fwd :
  ∀ (m : Nat) (a : aexp) (P : Assertion),
  {{fun st => P st ∧ st X = m}}
    (X ::= a)
  {{fun st => P (t_update st X m) ∧ st X = aeval (t_update st X m) a}} := by
  sorry

/--
**** 练习: 2 星, advanced, optional (hoare_asgn_fwd_exists)
通过对历史初始状态值存在量化构造的前向赋值规则。
-/
theorem hoare_asgn_fwd_exists :
  ∀ (a : aexp) (P : Assertion),
  {{ P }}
    (X ::= a)
  {{fun st => ∃ m, P (t_update st X m) ∧ st X = aeval (t_update st X m) a}} := by
  sorry
```

### 6. 推论规则 (Rule of Consequence)

前置条件可以被强化（加强约束），后置条件可以被弱化（放宽保证）。

```lean
/-- 前置条件强化推论规则 -/
theorem hoare_consequence_pre : ∀ (P P' Q : Assertion) (c : com),
  {{P'}} c {{Q}} →
  (P ->> P') →
  {{P}} c {{Q}} := by
  intro P P' Q c Hhoare Himp st st' Heval Hpre
  exact Hhoare st st' Heval (Himp st Hpre)

/-- 后置条件弱化推论规则 -/
theorem hoare_consequence_post : ∀ (P Q Q' : Assertion) (c : com),
  {{P}} c {{Q'}} →
  (Q' ->> Q) →
  {{P}} c {{Q}} := by
  intro P Q Q' c Hhoare Himp st st' Heval Hpre
  exact Himp st' (Hhoare st st' Heval Hpre)

theorem hoare_asgn_example1 :
  {{fun _ => True}} (X ::= ANum 1) {{fun st => st X = 1}} := by
  apply hoare_consequence_pre (P' := (fun st => st X = 1) [ X ↦ ANum 1 ])
  · apply hoare_asgn
  · intro st _
    dsimp [assertion_sub, t_update, aeval]

theorem assertion_sub_example2 :
  {{fun st => st X < 4}}
    (X ::= AId X + ANum 1)
  {{fun st => st X < 5}} := by
  apply hoare_consequence_pre (P' := (fun st => st X < 5) [ X ↦ (AId X + ANum 1) ])
  · apply hoare_asgn
  · intro st H
    dsimp [assertion_sub, t_update, aeval] at *
    omega

/-- 联合推论规则：同时对前置条件与后置条件进行调整 -/
theorem hoare_consequence : ∀ (P P' Q Q' : Assertion) (c : com),
  {{P'}} c {{Q'}} →
  (P ->> P') →
  (Q' ->> Q) →
  {{P}} c {{Q}} := by
  intro P P' Q Q' c Htriple Hpre Hpost
  apply hoare_consequence_pre (P' := P')
  · apply hoare_consequence_post (Q' := Q')
    · exact Htriple
    · exact Hpost
  · exact Hpre

-- 自动化教学变体声明（与 Coq 原文保持 100% 对齐）
theorem hoare_consequence_pre' : ∀ (P P' Q : Assertion) (c : com),
  {{P'}} c {{Q}} → (P ->> P') → {{P}} c {{Q}} := hoare_consequence_pre

theorem hoare_consequence_pre'' : ∀ (P P' Q : Assertion) (c : com),
  {{P'}} c {{Q}} → (P ->> P') → {{P}} c {{Q}} := hoare_consequence_pre

theorem hoare_consequence_pre''' : ∀ (P P' Q : Assertion) (c : com),
  {{P'}} c {{Q}} → (P ->> P') → {{P}} c {{Q}} := hoare_consequence_pre

theorem hoare_consequence_pre'''' : ∀ (P P' Q : Assertion) (c : com),
  {{P'}} c {{Q}} → (P ->> P') → {{P}} c {{Q}} := hoare_consequence_pre

theorem hoare_consequence_post' : ∀ (P Q Q' : Assertion) (c : com),
  {{P}} c {{Q'}} → (Q' ->> Q) → {{P}} c {{Q}} := hoare_consequence_post

theorem hoare_asgn_example1' : {{fun _ => True}} (X ::= ANum 1) {{fun st => st X = 1}} := by
  apply hoare_consequence_pre (P' := (fun st => st X = 1) [ X ↦ ANum 1 ])
  · apply hoare_asgn
  · intro st _; dsimp [assertion_sub, t_update, aeval]

theorem hoare_asgn_example1'' : {{fun _ => True}} (X ::= ANum 1) {{fun st => st X = 1}} := by
  apply hoare_consequence_pre (P' := (fun st => st X = 1) [ X ↦ ANum 1 ])
  · apply hoare_asgn
  · intro st _; dsimp [assertion_sub, t_update, aeval]

theorem assertion_sub_example2' : {{fun st => st X < 4}} (X ::= AId X + ANum 1) {{fun st => st X < 5}} := by
  apply hoare_consequence_pre (P' := (fun st => st X < 5) [ X ↦ (AId X + ANum 1) ])
  · apply hoare_asgn
  · intro st h; dsimp [assertion_sub, t_update, aeval] at *; omega

theorem assertion_sub_example2'' : {{fun st => st X < 4}} (X ::= AId X + ANum 1) {{fun st => st X < 5}} := by
  apply hoare_consequence_pre (P' := (fun st => st X < 5) [ X ↦ (AId X + ANum 1) ])
  · apply hoare_asgn
  · intro st h; dsimp [assertion_sub, t_update, aeval] at *; omega

theorem hoare_asgn_example1''' : {{fun _ => True}} (X ::= ANum 1) {{fun st => st X = 1}} := by
  apply hoare_consequence_pre (P' := (fun st => st X = 1) [ X ↦ ANum 1 ])
  · apply hoare_asgn
  · intro st _; dsimp [assertion_sub, t_update, aeval]
```

**** 练习: 2 星, standard (hoare_asgn_examples_2)

### 顺序复合与赋值结合 (Sequencing + Assignment)

```lean
theorem assertion_sub_ex1' :
  {{ fun st => st X ≤ 5 }}
    (X ::= ANum 2 * AId X)
  {{ fun st => st X ≤ 10 }} := by
  sorry

theorem assertion_sub_ex2' :
  {{ fun _ => 0 ≤ 3 ∧ 3 ≤ 5 }}
    (X ::= ANum 3)
  {{ fun st => 0 ≤ st X ∧ st X ≤ 5 }} := by
  sorry


theorem hoare_asgn_example3 : ∀ (a : aexp) (n : Nat),
  {{fun st => aeval st a = n}}
    (X ::= a ;; SKIP)
  {{fun st => st X = n}} := by
  intro a n
  apply hoare_seq (Q := fun st => st X = n)
  · apply hoare_skip
  · apply hoare_consequence_pre (P' := (fun st => st X = n) [ X ↦ a ])
    · apply hoare_asgn
    · intro st H
      dsimp [assertion_sub, t_update, aeval]
      exact H
```

**** 练习: 2 星, standard, especially useful (hoare_asgn_example4)

### 条件分支语句规则 (Conditionals)

```lean
theorem hoare_asgn_example4 :
  {{ fun _ => True }}
    (X ::= ANum 1 ;; Y ::= ANum 2)
  {{ fun st => st X = 1 ∧ st Y = 2 }} := by
  sorry

/-- 变量交换程序定义 -/
def swap_program : com :=
  X ::= AId X + AId Y ;;
  Y ::= AId X - AId Y ;;
  X ::= AId X - AId Y

/--
**** 练习: 3 星, standard (swap_exercise)
证明经典的异或/加减法无额外空间交换两个变量值的程序满足规约。
-/
theorem swap_exercise :
  {{fun st => st X ≤ st Y}}
    swap_program
  {{fun st => st Y ≤ st X}} := by
  sorry

/--
**** 练习: 4 星, advanced (invalid_triple)
证明在特定表达式与常量下，连续覆盖赋值的三元组并不普遍有效。
-/
theorem invalid_triple : ¬ (∀ (a : aexp) (n : Nat),
    {{ fun st => aeval st a = n }}
      (X ::= ANum 3 ;; Y ::= a)
    {{ fun st => st Y = n }}) := by
  sorry
```

### 7. 条件分支规则 (Conditionals)

在条件分支 `TEST b THEN c1 ELSE c2 FI` 中：
- 进入 `Then` 分支时已知布尔表达式 `b` 求值为 `true`；
- 进入 `Else` 分支时已知布尔表达式 `b` 求值为 `false`。

```lean
/-- 将布尔表达式转化为状态断言 -/
def bassertion (b : bexp) : Assertion :=
  fun st => (beval st b = true)

theorem bexp_eval_false : ∀ b st,
  beval st b = false → ¬ bassertion b st := by
  intro b st h hb
  dsimp [bassertion] at hb
  rw [h] at hb
  cases hb

/-- 条件分支霍尔逻辑规则 -/
theorem hoare_if : ∀ P Q (b : bexp) c1 c2,
  {{fun st => P st ∧ bassertion b st}} c1 {{Q}} →
  {{fun st => P st ∧ ¬ bassertion b st}} c2 {{Q}} →
  {{P}} (TEST b THEN c1 ELSE c2 FI) {{Q}} := by
  intro P Q b c1 c2 HTrue HFalse st st' HE HP
  cases HE with
  | E_IfTrue _ _ _ _ _ hbeval hc1 =>
    apply HTrue st st' hc1
    exact ⟨HP, hbeval⟩
  | E_IfFalse _ _ _ _ _ hbeval hc2 =>
    apply HFalse st st' hc2
    refine ⟨HP, ?_⟩
    intro hb
    dsimp [bassertion] at hb
    rw [hbeval] at hb
    cases hb

theorem if_example :
  {{fun _ => True}}
    (TEST (BEq (AId X) (ANum 0))
     THEN (Y ::= ANum 2)
     ELSE (Y ::= AId X + ANum 1) FI)
  {{fun st => st X ≤ st Y}} := by
  apply hoare_if
  · apply hoare_consequence_pre (P' := (fun st => st X ≤ st Y) [ Y ↦ ANum 2 ])
    · apply hoare_asgn
    · intro st ⟨_, hb⟩
      dsimp [bassertion, beval] at hb
      have hX : st X = 0 := by
        revert hb; dsimp [aeval]
        cases (st X) <;> intro h <;> first | contradiction | rfl
      change st X ≤ 2
      omega
  · apply hoare_consequence_pre (P' := (fun st => st X ≤ st Y) [ Y ↦ (AId X + ANum 1) ])
    · apply hoare_asgn
    · intro st _
      change st X ≤ st X + 1
      omega

theorem if_example'' :
  {{fun _ => True}}
    (TEST (BEq (AId X) (ANum 0))
     THEN (Y ::= ANum 2)
     ELSE (Y ::= AId X + ANum 1) FI)
  {{fun st => st X ≤ st Y}} := by
  apply hoare_if
  · apply hoare_consequence_pre (P' := (fun st => st X ≤ st Y) [ Y ↦ ANum 2 ])
    · apply hoare_asgn
    · intro st ⟨_, hb⟩
      dsimp [bassertion, beval] at hb
      have hX : st X = 0 := by
        revert hb; dsimp [aeval]
        cases (st X) <;> intro h <;> first | contradiction | rfl
      change st X ≤ 2
      omega
  · apply hoare_consequence_pre (P' := (fun st => st X ≤ st Y) [ Y ↦ (AId X + ANum 1) ])
    · apply hoare_asgn
    · intro st _
      change st X ≤ st X + 1
      omega

theorem if_example''' :
  {{fun _ => True}}
    (TEST (BEq (AId X) (ANum 0))
     THEN (Y ::= ANum 2)
     ELSE (Y ::= AId X + ANum 1) FI)
  {{fun st => st X ≤ st Y}} := by
  apply hoare_if
  · apply hoare_consequence_pre (P' := (fun st => st X ≤ st Y) [ Y ↦ ANum 2 ])
    · apply hoare_asgn
    · intro st ⟨_, hb⟩
      dsimp [bassertion, beval] at hb
      have hX : st X = 0 := by
        revert hb; dsimp [aeval]
        cases (st X) <;> intro h <;> first | contradiction | rfl
      change st X ≤ 2
      omega
  · apply hoare_consequence_pre (P' := (fun st => st X ≤ st Y) [ Y ↦ (AId X + ANum 1) ])
    · apply hoare_asgn
    · intro st _
      change st X ≤ st X + 1
      omega

/--
**** 练习: 2 星, standard (if_minus_plus)
-/
theorem if_minus_plus :
  {{fun _ => True}}
    (TEST (BLe (AId X) (AId Y))
     THEN (Z ::= AId Y - AId X)
     ELSE (Y ::= AId X + AId Z) FI)
  {{fun st => st Y = st X + st Z}} := by
  sorry

-- *** 单边条件分支 (One-sided Conditionals)
```

### 8. 扩展模块：单边条件分支 If1
*** 练习: One-sided conditionals
形式化形如 `if1 b then c end` 的单边条件语句语法、语义与霍尔推理规则。

```lean
namespace If1

inductive com : Type where
  | CSkip : com
  | CAsgn : String → aexp → com
  | CSeq : com → com → com
  | CIf : bexp → com → com → com
  | CWhile : bexp → com → com
  | CIf1 : bexp → com → com
deriving Repr, DecidableEq
```

**** 练习: 2 星, standard, especially useful (if1_ceval)

```lean
inductive ceval : com → state → state → Prop where
  | E_Skip : ∀ st, ceval com.CSkip st st
  | E_Asgn : ∀ st a n x,
      aeval st a = n →
      ceval (com.CAsgn x a) st (t_update st x n)
  | E_Seq : ∀ c1 c2 st st' st'',
      ceval c1 st st' →
      ceval c2 st' st'' →
      ceval (com.CSeq c1 c2) st st''
  | E_IfTrue : ∀ st st' b c1 c2,
      beval st b = true →
      ceval c1 st st' →
      ceval (com.CIf b c1 c2) st st'
  | E_IfFalse : ∀ st st' b c1 c2,
      beval st b = false →
      ceval c2 st st' →
      ceval (com.CIf b c1 c2) st st'
  | E_WhileFalse : ∀ b st c,
      beval st b = false →
      ceval (com.CWhile b c) st st
  | E_WhileTrue : ∀ st st' st'' b c,
      beval st b = true →
      ceval c st st' →
      ceval (com.CWhile b c) st' st'' →
      ceval (com.CWhile b c) st st''
  | E_If1True : ∀ st st' b c,
      beval st b = true →
      ceval c st st' →
      ceval (com.CIf1 b c) st st'
  | E_If1False : ∀ st b c,
      beval st b = false →
      ceval (com.CIf1 b c) st st

theorem if1true_test :
  ceval (com.CIf1 (BEq (AId X) (ANum 0)) (com.CAsgn X (ANum 1))) empty_st (t_update empty_st X 1) := by
  apply ceval.E_If1True
  · rfl
  · apply ceval.E_Asgn
    rfl

theorem if1false_test :
  ceval (com.CIf1 (BEq (AId X) (ANum 0)) (com.CAsgn X (ANum 1))) (t_update empty_st X 2) (t_update empty_st X 2) := by
  apply ceval.E_If1False
  rfl

def valid_hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  ∀ st st', ceval c st st' → P st → Q st'

/--
**** 练习: 2 星, standard (hoare_if1)
-/
theorem hoare_if1 : ∀ P Q (b : bexp) c,
  valid_hoare_triple (fun st => P st ∧ beval st b = true) c Q →
  ((fun st => P st ∧ beval st b ≠ true) ->> Q) →
  valid_hoare_triple P (com.CIf1 b c) Q := by
  sorry

def manual_grade_for_hoare_if1 : Option (Nat × String) := none

theorem hoare_consequence_pre : ∀ (P P' Q : Assertion) c,
  valid_hoare_triple P' c Q →
  (P ->> P') →
  valid_hoare_triple P c Q := by
  intro P P' Q c Hhoare Himp st st' Heval Hpre
  exact Hhoare st st' Heval (Himp st Hpre)

theorem hoare_asgn : ∀ Q X a,
  valid_hoare_triple (assertion_sub X a Q) (com.CAsgn X a) Q := by
  intro Q X a st st' HE HQ
  cases HE with
  | E_Asgn _ _ n _ heq =>
    dsimp [assertion_sub] at HQ
    subst heq
    exact HQ
```

**** 练习: 2 星, standard (hoare_if1_good)

### 循环语句规则 (While Loops)

```lean
theorem hoare_if1_good :
  valid_hoare_triple
    (fun st => st X + st Y = st Z)
    (com.CIf1 (BNeq (AId Y) (ANum 0)) (com.CAsgn X (AId X + AId Y)))
    (fun st => st X = st Z) := by
  sorry

end If1
```

### 9. 循环不变式与 While 循环规则 (While Loops)

循环验证的核心是寻找**循环不变式（Loop Invariant）**：
若断言 `P` 满足 `{{ P ∧ b }} c {{ P }}`，则在循环开始前 `P` 成立，
循环无论迭代多少次，结束时不仅 `P` 依然成立，而且循环守卫必定变为假 `¬ b`。

```lean
/-- While 循环霍尔逻辑规则 -/
theorem hoare_while : ∀ P (b : bexp) c,
  valid_hoare_triple (fun st => P st ∧ bassertion b st) c P →
  valid_hoare_triple P (WHILE b DO c END) (fun st => P st ∧ ¬ bassertion b st) := by
  intro P b c Hhoare st st' Heval
  have H : ∀ cw, st =[ cw ]=> st' → cw = (com.CWhile b c) → P st → P st' ∧ ¬ bassertion b st' := by
    intro cw Hc
    induction Hc with
    | E_WhileFalse st_f b' c' hfalse =>
      intro hcw HP
      injection hcw with eq1 eq2
      subst eq1 eq2
      refine ⟨HP, ?_⟩
      intro hb
      dsimp [bassertion] at hb
      rw [hfalse] at hb
      cases hb
    | E_WhileTrue st1 st2 st3 b' c' htrue hc hwhile ih_c ih_while =>
      intro hcw HP
      injection hcw with eq1 eq2
      subst eq1 eq2
      have hp2 : P st2 := by
        apply Hhoare st1 st2 hc
        exact ⟨HP, htrue⟩
      exact ih_while hwhile rfl hp2
    | _ =>
      intro hcw _
      contradiction
  intro HP
  exact H (com.CWhile b c) Heval rfl HP

theorem while_example :
  {{fun st => st X ≤ 3}}
    (WHILE (BLe (AId X) (ANum 2)) DO
      (X ::= AId X + ANum 1)
    END)
  {{fun st => st X = 3}} := by
  apply hoare_consequence_post (Q' := fun st => st X ≤ 3 ∧ ¬ bassertion (BLe (AId X) (ANum 2)) st)
  · apply hoare_while
    apply hoare_consequence_pre (P' := (fun st => st X ≤ 3) [ X ↦ (AId X + ANum 1) ])
    · apply hoare_asgn
    · intro st ⟨hinv, hguard⟩
      dsimp [bassertion, beval, aeval] at hguard
      dsimp [assertion_sub, t_update, aeval]
      have hle : st X ≤ 2 := of_decide_eq_true hguard
      omega
  · intro st ⟨hinv, hguard⟩
    have hnot_le : ¬ (st X ≤ 2) := by
      intro hle
      have ht : bassertion (BLe (AId X) (ANum 2)) st := by
        dsimp [bassertion, beval, aeval]
        exact decide_eq_true hle
      exact hguard ht
    omega

/-- 死循环霍尔逻辑定理：永不终止的程序可以满足任意后置条件（部分正确性） -/
theorem always_loop_hoare : ∀ Q,
  valid_hoare_triple (fun _ => True) (WHILE bexp.BTrue DO SKIP END) Q := by
  intro Q st st' Heval
  have H : ∀ cw, st =[ cw ]=> st' → cw = (com.CWhile bexp.BTrue com.CSkip) → Q st' := by
    intro cw Hc
    induction Hc with
    | E_WhileFalse st_f b' c' hfalse =>
      intro hcw
      injection hcw with eq1 eq2
      subst eq1 eq2
      dsimp [beval] at hfalse
      contradiction
    | E_WhileTrue st1 st2 st3 b' c' htrue hc hwhile ih_c ih_while =>
      intro hcw
      injection hcw with eq1 eq2
      subst eq1 eq2
      exact ih_while hwhile rfl
    | _ =>
      intro hcw
      contradiction
  intro _
  exact H (com.CWhile bexp.BTrue com.CSkip) Heval rfl

-- *** 练习：Repeat-Until 循环
```

### 10. 扩展模块：RepeatExercise
*** 练习: [REPEAT]
形式化支持 `repeat c until b end` 循环结构的扩展命令与霍尔规则。

```lean
namespace RepeatExercise

inductive com : Type where
  | CSkip : com
  | CAsgn : String → aexp → com
  | CSeq : com → com → com
  | CIf : bexp → com → com → com
  | CWhile : bexp → com → com
  | CRepeat : com → bexp → com
deriving Repr, DecidableEq

inductive ceval : state → com → state → Prop where
  | E_Skip : ∀ st, ceval st com.CSkip st
  | E_Asgn : ∀ st a n x,
      aeval st a = n →
      ceval st (com.CAsgn x a) (t_update st x n)
  | E_Seq : ∀ c1 c2 st st' st'',
      ceval st c1 st' →
      ceval st' c2 st'' →
      ceval st (com.CSeq c1 c2) st''
  | E_IfTrue : ∀ st st' b c1 c2,
      beval st b = true →
      ceval st c1 st' →
      ceval st (com.CIf b c1 c2) st'
  | E_IfFalse : ∀ st st' b c1 c2,
      beval st b = false →
      ceval st c2 st' →
      ceval st (com.CIf b c1 c2) st'
  | E_WhileFalse : ∀ b st c,
      beval st b = false →
      ceval st (com.CWhile b c) st
  | E_WhileTrue : ∀ st st' st'' b c,
      beval st b = true →
      ceval st c st' →
      ceval st' (com.CWhile b c) st'' →
      ceval st (com.CWhile b c) st''
  | E_RepeatEnd : ∀ st st' b c,
      ceval st c st' →
      beval st' b = true →
      ceval st (com.CRepeat c b) st'
  | E_RepeatLoop : ∀ st st' st'' b c,
      ceval st c st' →
      beval st' b = false →
      ceval st' (com.CRepeat c b) st'' →
      ceval st (com.CRepeat c b) st''

def valid_hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  ∀ st st', ceval st c st' → P st → Q st'

def ex1_repeat : com :=
  com.CRepeat
    (com.CSeq (com.CAsgn X (ANum 1)) (com.CAsgn Y (AId Y + ANum 1)))
    (BEq (AId X) (ANum 1))

theorem ex1_repeat_works :
  ceval empty_st ex1_repeat (t_update (t_update empty_st X 1) Y 1) := by
  apply ceval.E_RepeatEnd
  · apply ceval.E_Seq
    · apply ceval.E_Asgn
      rfl
    · apply ceval.E_Asgn
      rfl
  · rfl
```

**** 练习: 4 星, advanced, optional (hoare_repeat)

## 补充练习 (Additional Exercises)

### 非确定性随机赋值 Havoc

```lean
theorem hoare_repeat : ∀ P Q (b : bexp) c,
  valid_hoare_triple P c Q →
  ((fun st => Q st ∧ beval st b ≠ true) ->> P) →
  valid_hoare_triple P (com.CRepeat c b) (fun st => Q st ∧ beval st b = true) := by
  sorry

end RepeatExercise

def manual_grade_for_hoare_repeat : Option (Nat × String) := none
```

### 11. 扩展模块：Himp (Havoc)
包含非确定性随机赋值语句 `havoc X` 的命令式语言与其霍尔逻辑公理。

```lean
namespace Himp

inductive com : Type where
  | CSkip : com
  | CAsgn : String → aexp → com
  | CSeq : com → com → com
  | CIf : bexp → com → com → com
  | CWhile : bexp → com → com
  | CHavoc : String → com
deriving Repr, DecidableEq

inductive ceval : com → state → state → Prop where
  | E_Skip : ∀ st, ceval com.CSkip st st
  | E_Asgn : ∀ st a n x,
      aeval st a = n →
      ceval (com.CAsgn x a) st (t_update st x n)
  | E_Seq : ∀ c1 c2 st st' st'',
      ceval c1 st st' →
      ceval c2 st' st'' →
      ceval (com.CSeq c1 c2) st st''
  | E_IfTrue : ∀ st st' b c1 c2,
      beval st b = true →
      ceval c1 st st' →
      ceval (com.CIf b c1 c2) st st'
  | E_IfFalse : ∀ st st' b c1 c2,
      beval st b = false →
      ceval c2 st st' →
      ceval (com.CIf b c1 c2) st st'
  | E_WhileFalse : ∀ b st c,
      beval st b = false →
      ceval (com.CWhile b c) st st
  | E_WhileTrue : ∀ st st' st'' b c,
      beval st b = true →
      ceval c st st' →
      ceval (com.CWhile b c) st' st'' →
      ceval (com.CWhile b c) st st''
  | E_Havoc : ∀ st x n,
      ceval (com.CHavoc x) st (t_update st x n)

def valid_hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  ∀ st st', ceval c st st' → P st → Q st'

theorem hoare_consequence_pre : ∀ (P P' Q : Assertion) c,
  valid_hoare_triple P' c Q →
  (P ->> P') →
  valid_hoare_triple P c Q := by
  intro P P' Q c Hhoare Himp st st' Heval Hpre
  exact Hhoare st st' Heval (Himp st Hpre)

/-- Havoc 最弱前置条件：对变量任意可能赋入的值，后置条件均成立 -/
def havoc_pre (X : String) (Q : Assertion) (st : state) : Prop :=
  ∀ n : Nat, Q (t_update st X n)

/--
**** 练习: 3 星, advanced (hoare_havoc)
-/
theorem hoare_havoc : ∀ (Q : Assertion) (X : String),
  valid_hoare_triple (havoc_pre X Q) (com.CHavoc X) Q := by
  sorry
```

**** 练习: 3 星, advanced (havoc_post)

### 断言与假定 (Assert and Assume)

```lean
theorem havoc_post : ∀ (P : Assertion) (X : String),
  valid_hoare_triple P (com.CHavoc X) (fun st => ∃ n : Nat, P (t_update st X n)) := by
  sorry

end Himp
```

### 12. 扩展模块：HoareAssertAssume
区分运行时断言（`assert`，失败则进入错误状态）与逻辑假定（`assume`，不满足则卡住发散）。

```lean
namespace HoareAssertAssume

inductive com : Type where
  | CSkip : com
  | CAsgn : String → aexp → com
  | CSeq : com → com → com
  | CIf : bexp → com → com → com
  | CWhile : bexp → com → com
  | CAssert : bexp → com
  | CAssume : bexp → com
deriving Repr, DecidableEq

inductive result : Type where
  | RNormal : state → result
  | RError : result

inductive ceval : com → state → result → Prop where
  | E_Skip : ∀ st, ceval com.CSkip st (result.RNormal st)
  | E_Asgn : ∀ st a n x,
      aeval st a = n →
      ceval (com.CAsgn x a) st (result.RNormal (t_update st x n))
  | E_SeqNormal : ∀ c1 c2 st st' r,
      ceval c1 st (result.RNormal st') →
      ceval c2 st' r →
      ceval (com.CSeq c1 c2) st r
  | E_SeqError : ∀ c1 c2 st,
      ceval c1 st result.RError →
      ceval (com.CSeq c1 c2) st result.RError
  | E_IfTrue : ∀ st r b c1 c2,
      beval st b = true →
      ceval c1 st r →
      ceval (com.CIf b c1 c2) st r
  | E_IfFalse : ∀ st r b c1 c2,
      beval st b = false →
      ceval c2 st r →
      ceval (com.CIf b c1 c2) st r
  | E_WhileFalse : ∀ b st c,
      beval st b = false →
      ceval (com.CWhile b c) st (result.RNormal st)
  | E_WhileTrueNormal : ∀ st st' r b c,
      beval st b = true →
      ceval c st (result.RNormal st') →
      ceval (com.CWhile b c) st' r →
      ceval (com.CWhile b c) st r
  | E_WhileTrueError : ∀ st b c,
      beval st b = true →
      ceval c st result.RError →
      ceval (com.CWhile b c) st result.RError
  | E_AssertTrue : ∀ st b,
      beval st b = true →
      ceval (com.CAssert b) st (result.RNormal st)
  | E_AssertFalse : ∀ st b,
      beval st b = false →
      ceval (com.CAssert b) st result.RError
  | E_Assume : ∀ st b,
      beval st b = true →
      ceval (com.CAssume b) st (result.RNormal st)

def valid_hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  ∀ st r, ceval c st r → P st → ∃ st', r = result.RNormal st' ∧ Q st'
```

**** 练习: 4 星, standard (assert_vs_assume)

```lean
theorem assert_assume_differ : ∃ (P : Assertion) (b : bexp) (Q : Assertion),
  valid_hoare_triple P (com.CAssume b) Q ∧
  ¬ valid_hoare_triple P (com.CAssert b) Q := by
  sorry

theorem assert_implies_assume : ∀ P b Q,
  valid_hoare_triple P (com.CAssert b) Q →
  valid_hoare_triple P (com.CAssume b) Q := by
  sorry

theorem hoare_asgn : ∀ Q X a,
  valid_hoare_triple (assertion_sub X a Q) (com.CAsgn X a) Q := by
  intro Q X a st r HE HQ
  cases HE
  rename_i n heq
  dsimp [assertion_sub] at HQ
  subst heq
  exact ⟨t_update st X (aeval st a), rfl, HQ⟩

theorem hoare_consequence_pre : ∀ (P P' Q : Assertion) c,
  valid_hoare_triple P' c Q →
  (P ->> P') →
  valid_hoare_triple P c Q := by
  intro P P' Q c Hhoare Himp st r Hc HP
  exact Hhoare st r Hc (Himp st HP)

theorem hoare_consequence_post : ∀ (P Q Q' : Assertion) c,
  valid_hoare_triple P c Q' →
  (Q' ->> Q) →
  valid_hoare_triple P c Q := by
  intro P Q Q' c Hhoare Himp st r Hc HP
  obtain ⟨st', hr, hq'⟩ := Hhoare st r Hc HP
  exact ⟨st', hr, Himp st' hq'⟩

theorem hoare_seq : ∀ P Q R c1 c2,
  valid_hoare_triple Q c2 R →
  valid_hoare_triple P c1 Q →
  valid_hoare_triple P (com.CSeq c1 c2) R := by
  intro P Q R c1 c2 H2 H1 st r H12 HP
  cases H12 with
  | E_SeqNormal _ _ _ st_mid _ h1 h2 =>
    obtain ⟨st'1, heq1, hq⟩ := H1 st (result.RNormal st_mid) h1 HP
    cases heq1
    exact H2 st_mid r h2 hq
  | E_SeqError _ _ _ h1 =>
    obtain ⟨st'1, heq1, _⟩ := H1 st result.RError h1 HP
    contradiction

theorem hoare_skip : ∀ P,
  valid_hoare_triple P com.CSkip P := by
  intro P st r H HP
  cases H
  exact ⟨st, rfl, HP⟩

theorem hoare_if : ∀ P Q (b : bexp) c1 c2,
  valid_hoare_triple (fun st => P st ∧ beval st b = true) c1 Q →
  valid_hoare_triple (fun st => P st ∧ beval st b ≠ true) c2 Q →
  valid_hoare_triple P (com.CIf b c1 c2) Q := by
  intro P Q b c1 c2 HTrue HFalse st r HE HP
  cases HE with
  | E_IfTrue _ _ _ _ _ htrue hc1 =>
    exact HTrue st r hc1 ⟨HP, htrue⟩
  | E_IfFalse _ _ _ _ _ hfalse hc2 =>
    apply HFalse st r hc2
    refine ⟨HP, ?_⟩
    intro contra
    rw [contra] at hfalse
    cases hfalse

theorem hoare_while : ∀ P (b : bexp) c,
  valid_hoare_triple (fun st => P st ∧ beval st b = true) c P →
  valid_hoare_triple P (com.CWhile b c) (fun st => P st ∧ beval st b ≠ true) := by
  intro P b c Hhoare st r He HP
  have H : ∀ cw, ceval cw st r → cw = (com.CWhile b c) → P st → ∃ st', r = result.RNormal st' ∧ P st' ∧ beval st' b ≠ true := by
    intro cw Hc
    induction Hc with
    | E_WhileFalse _ st_f _ hfalse =>
      intro hcw HP
      injection hcw with eq1 eq2
      subst eq1 eq2
      refine ⟨st_f, rfl, HP, ?_⟩
      intro contra
      rw [contra] at hfalse
      cases hfalse
    | E_WhileTrueNormal st1 st_mid r_end b' c' htrue hc1 hcw_loop ih_c ih_loop =>
      intro hcw HP
      injection hcw with eq1 eq2
      subst eq1 eq2
      obtain ⟨st'1, heq1, hp_mid⟩ := Hhoare st1 (result.RNormal st_mid) hc1 ⟨HP, htrue⟩
      cases heq1
      exact ih_loop hcw_loop hp_mid rfl hp_mid
    | E_WhileTrueError st1 b' c' htrue hc1 =>
      intro hcw HP
      injection hcw with eq1 eq2
      subst eq1 eq2
      obtain ⟨st'1, heq1, _⟩ := Hhoare st1 result.RError hc1 ⟨HP, htrue⟩
      contradiction
    | _ =>
      intro hcw _
      contradiction
  exact H (com.CWhile b c) He rfl HP

theorem hoare_assert : ∀ P (b : bexp),
  valid_hoare_triple (fun st => P st ∧ beval st b = true) (com.CAssert b) P := by
  sorry

theorem hoare_assume : ∀ P (b : bexp),
  valid_hoare_triple P (com.CAssume b) (fun st => P st ∧ beval st b = true) := by
  sorry

theorem assert_assume_example :
  valid_hoare_triple
    (fun _ => True)
    (com.CSeq (com.CAssume (BEq (AId X) (ANum 1)))
      (com.CSeq (com.CAsgn X (AId X + ANum 1))
        (com.CAssert (BEq (AId X) (ANum 2)))))
    (fun _ => True) := by
  sorry

end HoareAssertAssume

end PLF.Hoare
```
