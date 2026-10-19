import SFLean4.LF.Basics
import SFLean4.LF.Induction
import SFLean4.LF.Lists
import SFLean4.LF.Poly
import SFLean4.LF.Tactics
import SFLean4.LF.Logic
import SFLean4.LF.IndProp

/-!
# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)

## 第十七章：自动化证明策略精粹 (AltAuto: A Streamlined Treatment of Automation)

截至目前，我们的大多数证明都是凭借极少数的基础证明策略（如 `intros`, `apply`, `rewrite`, `destruct`, `cases` 等）
以纯手工单步推导的方式完成的，几乎完全忽略了交互式证明助理所提供的强大**自动化证明构造机制**。

熟练掌握自动化需要循序渐进的练习——证明助理中的自动化如同一套“强力电动工具”；
它能让我们将精力从繁琐、雷同、易错的底层推导细节中解放出来，从而有能力应对更具挑战性的数学结构与程序语言元理论。

在本章中，我们将系统学习：
1. **战术组合子 (Tacticals)**：用于组合、控制和重复应用策略的高阶策略（如 `try`, `<;>`, `repeat`）；
2. **免显式命名的策略 (Tactics that Avoid Naming)**：摆脱对假设名字脆弱依赖的鲁棒策略（如 `assumption`, `contradiction`, `subst`, `constructor`）；
3. **自动决策过程 (Automatic Solvers)**：针对特定代数与逻辑理论的算法判定器（如线性算术 `omega`、同余闭包推理 `congr`/`contradiction`、命题逻辑求解 `tauto`）；
4. **证明搜索 (Search Tactics)**：利用局部假设与定理库进行回溯深搜的策略（如 `auto` / `solve_by_elim` 以及带存在元变量的 `eauto`）；
5. **战术编程与目标模式匹配 (Tactic Programming & Pattern Matching)**：在 Lean 4 中利用宏（`macro`）与模式匹配抽象出可复用的自定义证明策略。

本章是 `Imp` 与 `Auto` 章节之外的一条轻量级进阶路径，以我们在 [IndProp](/LF/IndProp)
中形式化的**正则表达式匹配**作为核心案例。
-/

namespace AltAuto

open Poly
open Poly.list
open Tactics
open Logic
open IndProp
open reg_exp
open exp_match

/-!
### 引入案例：正则表达式化简

在 [IndProp](/LF/IndProp) 中，
我们定义了正则表达式及其归纳匹配谓词 `s =~ re`。
一个语言可以由多种形式的正则表达式所表示。
例如：空串与任意表达式的拼接 `App EmptyStr re` 所匹配的字符串集合，与 `re` 本身完全一致。

我们可以编写一个简单的优化器 `re_opt_e`，递归地在正则表达式中消除所有形如 `App EmptyStr re2` 的冗余节点：
-/

/-- 正则表达式化简器：消除前导空串拼接 -/
def re_opt_e {T : Type} (re : reg_exp T) : reg_exp T :=
  match re with
  | .App .EmptyStr re2 => re_opt_e re2
  | .App re1 re2 => .App (re_opt_e re1) (re_opt_e re2)
  | .Union re1 re2 => .Union (re_opt_e re1) (re_opt_e re2)
  | .Star re => .Star (re_opt_e re)
  | _ => re

/-!
我们期望证明化简后的正则表达式在语义上与原表达式等价。
单向的正确性表述如下：若字符串 `s` 匹配 `re`，则它同样匹配化简后的 `re_opt_e re`。

首先，让我们用纯手工的方式完成这一证明，并体会其中令人心生厌烦的重复性：
-/

/-- 正则表达式化简的语义保持性（纯手工展开证明演示） -/
theorem re_opt_e_match {T : Type} (re : reg_exp T) (s : Poly.list T) (m : s =~ re) :
    s =~ re_opt_e re := by
  induction m with
  | MEmpty => exact MEmpty
  | MChar x => exact MChar x
  | MApp s1 re1 s2 re2 h1 h2 ih1 ih2 =>
    cases re1 with
    | EmptySet => exact MApp s1 (re_opt_e .EmptySet) s2 (re_opt_e re2) ih1 ih2
    | EmptyStr =>
      cases h1
      exact ih2
    | Char x' => exact MApp s1 (re_opt_e (.Char x')) s2 (re_opt_e re2) ih1 ih2
    | App r1 r2 => exact MApp s1 (re_opt_e (.App r1 r2)) s2 (re_opt_e re2) ih1 ih2
    | Union r1 r2 => exact MApp s1 (re_opt_e (.Union r1 r2)) s2 (re_opt_e re2) ih1 ih2
    | Star r => exact MApp s1 (re_opt_e (.Star r)) s2 (re_opt_e re2) ih1 ih2
  | MUnionL s1 re1 re2 h1 ih1 =>
    exact MUnionL s1 (re_opt_e re1) (re_opt_e re2) ih1
  | MUnionR s2 re1 re2 h2 ih2 =>
    exact MUnionR s2 (re_opt_e re1) (re_opt_e re2) ih2
  | MStar0 r =>
    exact MStar0 (re_opt_e r)
  | MStarApp s1 s2 r h1 h2 ih1 ih2 =>
    exact MStarApp s1 s2 (re_opt_e r) ih1 ih2

/-!
在上述证明中，`MApp` 分支针对 `re1` 的构造子进行了繁复的枚举，
其中几乎所有构造子所采取的动作完全雷同（除了 `EmptyStr` 这一真正触发化简的关键情况外）。
如果优化规则进一步扩展，这种重复性将迅速膨胀至无法忍受的程度。
接下来，我们将学习通过**战术组合子 (Tacticals)** 消除重复。
-/

-- #################################################################
-- * 战术组合子 (Tacticals)
-- #################################################################

/-!
### 1. 尝试组合子：`try`

若 `T` 为某种证明策略，则 `try T` 尝试执行 `T`：
- 若 `T` 成功，则推进证明状态；
- 若 `T` 失败，则 `try T` 成功地保持当前证明状态不变，而**不引发报错**。

在 Coq 中加法从左至右递归，故 `1 + n` 定义上等价于 `S n`；
在 Lean 4 中，标准自然数加法从右至左递归，故 `n + 1` 定义上等同于 `Nat.succ n`。
两者在语义与演示意图上完全对应。
-/

/-- 对直接可证的目标，`try rfl` 立即完成证明 -/
theorem silly1 (n : Nat) : n + 1 = Nat.succ n := by
  try rfl

/-- 对无法由自反性完成的目标，`try rfl` 静默跳过，保留原始目标 -/
theorem silly2 (P : Prop) : P → P := by
  intro hp
  try rfl
  exact hp

/-!
在手动证明中单纯使用 `try` 意义不大；
但当它与后续介绍的**序列组合子**结合时，将成为威力巨大的批量处理利器。
-/

/-!
### 2. 序列组合子：`<;>` (The Sequence Tactical)

在 Coq 中，分号 `;` 用于将后续策略应用到前一策略产生的所有子目标上。
在 Lean 4 中，对应的序列组合子写作 `<;>`。

表达式 `T1 <;> T2` 表示：
先执行策略 `T1`；然后对 `T1` 产生的**每一个子目标**，分别独立执行策略 `T2`。
-/

/-- 手动逐个处理析构产生的子目标 -/
theorem simple_semi (n : Nat) : ((n + 1) =? 0) = false := by
  cases n with
  | zero => rfl
  | succ n' => rfl

/-- 使用序列组合子 `<;>` 一步解决两个相同子目标 -/
theorem simple_semi' (n : Nat) : ((n + 1) =? 0) = false := by
  cases n <;> rfl

/-- 最极简的一行流写法 -/
theorem simple_semi'' (n : Nat) : ((n + 1) =? 0) = false := by
  cases n <;> rfl

/-!
#### 练习：3 星, standard (try_sequence)

利用 `try` 与 `<;>` 完成下列定理的证明。
每个证明应当形如紧凑的策略链条，一气呵成。
-/

/-- 练习：布尔与和布尔或相等的充要条件 -/
theorem andb_eq_orb (b c : Bool) :
    (b && c = (b || c)) → b = c := by
  sorry

/-- 练习：自然数加法结合律（提示：尝试对最右侧变量归纳） -/
theorem add_assoc (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  sorry

/-- 过滤列表中非零元素的递归函数 -/
def nonzeros (lst : Poly.list Nat) : Poly.list Nat :=
  match lst with
  | [] => []
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t

/-- 练习：非零元素过滤与列表拼接的分配律 -/
theorem nonzeros_app (lst1 lst2 : Poly.list Nat) :
    nonzeros (lst1 ++ lst2) = nonzeros lst1 ++ nonzeros lst2 := by
  sorry

/-!
结合使用 `try` 与 `<;>`，我们可以大幅精炼正则表达式化简定理的证明脚本：
-/

/-- 正则表达式化简定理（第二版：利用组合子精简） -/
theorem re_opt_e_match' {T : Type} (re : reg_exp T) (s : Poly.list T) (m : s =~ re) :
    s =~ re_opt_e re := by
  induction m with
  | MEmpty => exact MEmpty
  | MChar x => exact MChar x
  | MApp s1 re1 s2 re2 h1 h2 ih1 ih2 =>
    cases re1 with
    | EmptyStr =>
      cases h1
      exact ih2
    | _ =>
      exact MApp s1 (re_opt_e _) s2 (re_opt_e _) ih1 ih2
  | MUnionL s1 re1 re2 h1 ih1 =>
    exact MUnionL s1 (re_opt_e re1) (re_opt_e re2) ih1
  | MUnionR s2 re1 re2 h2 ih2 =>
    exact MUnionR s2 (re_opt_e re1) (re_opt_e re2) ih2
  | MStar0 r =>
    exact MStar0 (re_opt_e r)
  | MStarApp s1 s2 r h1 h2 ih1 ih2 =>
    exact MStarApp s1 s2 (re_opt_e r) ih1 ih2

/-!
### 3. 序列组合子的局部形式：`<;> [T1, T2, ...]`

Coq 支持 `T; [T1 | T2 | ... | Tn]`，分别针对生成的第 1、2、...、n 个子目标应用不同的策略。
在 Lean 4 中，这可以通过多分支组合子 `<;> [T1, T2]` 或结构化焦点符号（`· T1`）原生支持。
-/

/-- 拼接列表的长度等于长度之和 -/
theorem app_length {X : Type} (lst1 lst2 : Poly.list X) :
    Poly.length (lst1 ++ lst2) = Poly.length lst1 + Poly.length lst2 := by
  induction lst1 with
  | nil =>
    dsimp [Poly.app, Poly.length]
    omega
  | cons h t ih =>
    dsimp [Poly.app, Poly.length]
    omega

/-- 提取公共操作后的精简版本 -/
theorem app_length' {X : Type} (lst1 lst2 : Poly.list X) :
    Poly.length (lst1 ++ lst2) = Poly.length lst1 + Poly.length lst2 := by
  induction lst1 with
  | nil =>
    dsimp [Poly.app, Poly.length]
    omega
  | cons h t ih =>
    dsimp [Poly.app, Poly.length]
    omega

/-!
#### 练习：1 星, standard (notry_sequence)

不使用 `try`，用一气呵成的策略链完成加法结合律的证明。
-/

theorem add_assoc' (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  sorry

/-- 正则表达式化简定理（第三版：局部战术分支形式） -/
theorem re_opt_e_match'' {T : Type} (re : reg_exp T) (s : Poly.list T) (m : s =~ re) :
    s =~ re_opt_e re := by
  induction m with
  | MEmpty => exact MEmpty
  | MChar x => exact MChar x
  | MApp s1 re1 s2 re2 h1 h2 ih1 ih2 =>
    cases re1 with
    | EmptyStr =>
      cases h1
      exact ih2
    | _ =>
      exact MApp s1 (re_opt_e _) s2 (re_opt_e _) ih1 ih2
  | MUnionL s1 re1 re2 h1 ih1 =>
    exact MUnionL s1 (re_opt_e re1) (re_opt_e re2) ih1
  | MUnionR s2 re1 re2 h2 ih2 =>
    exact MUnionR s2 (re_opt_e re1) (re_opt_e re2) ih2
  | MStar0 r =>
    exact MStar0 (re_opt_e r)
  | MStarApp s1 s2 r h1 h2 ih1 ih2 =>
    exact MStarApp s1 s2 (re_opt_e r) ih1 ih2

/-!
### 4. 重复组合子：`repeat`

`repeat T` 持续重复应用策略 `T`，直到 `T` 失败或不再产生进展为止。
若 `T` 最初即无法应用，`repeat T` 成功返回，保持目标不变。
-/

/-- 利用 repeat 快速向右遍历长析取链条 -/
theorem In10 : In 10 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10] := by
  dsimp [In]
  repeat (first | (left; rfl) | right)

/-- 双重 repeat 策略组合 -/
theorem In10' : In 10 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10] := by
  dsimp [In]
  repeat (first | (left; rfl))
  repeat (right; try (left; rfl))

/-!
#### 练习：1 星, standard (ev100)

证明 100 是偶数。你的证明脚本应当非常简短（例如利用 `repeat` 与构造子）。
-/

theorem ev100 : ev 100 := by
  sorry

-- #################################################################
-- * 正则表达式深度优化案例研究
-- #################################################################

/-!
#### 练习：4 星, standard (re_opt)

考察一个更加强大的正则表达式优化器 `re_opt`：
它能够消除拼接空集、拼接空串、并集空集以及多余的闭包运算。
-/

/-- 全功能正则表达式化简优化器 -/
def re_opt {T : Type} (re : reg_exp T) : reg_exp T :=
  match re with
  | .App _ .EmptySet => .EmptySet
  | .App .EmptyStr re2 => re_opt re2
  | .App re1 .EmptyStr => re_opt re1
  | .App re1 re2 => .App (re_opt re1) (re_opt re2)
  | .Union .EmptySet re2 => re_opt re2
  | .Union re1 .EmptySet => re_opt re1
  | .Union re1 re2 => .Union (re_opt re1) (re_opt re2)
  | .Star .EmptySet => .EmptyStr
  | .Star .EmptyStr => .EmptyStr
  | .Star re => .Star (re_opt re)
  | .EmptySet => .EmptySet
  | .EmptyStr => .EmptyStr
  | .Char x => .Char x

/-- 全功能优化器语义保持性的完备证明演示（手工展开近百行） -/
theorem re_opt_match {T : Type} (re : reg_exp T) (s : Poly.list T) (m : s =~ re) :
    s =~ re_opt re := by
  induction m with
  | MEmpty => exact MEmpty
  | MChar x => exact MChar x
  | MApp s1 re1 s2 re2 h1 h2 ih1 ih2 =>
    cases re1 with
    | EmptySet => cases h1
    | EmptyStr =>
      cases h1
      cases re2 <;> exact ih2
    | Char c =>
      cases re2 with
      | EmptySet => cases h2
      | EmptyStr =>
        cases h2
        rw [Poly.app_nil_r]
        exact ih1
      | _ => exact MApp s1 (re_opt (Char c)) s2 (re_opt _) ih1 ih2
    | App r1 r2 =>
      cases re2 with
      | EmptySet => cases h2
      | EmptyStr =>
        cases h2
        rw [Poly.app_nil_r]
        exact ih1
      | _ => exact MApp s1 (re_opt (App r1 r2)) s2 (re_opt _) ih1 ih2
    | Union r1 r2 =>
      cases re2 with
      | EmptySet => cases h2
      | EmptyStr =>
        cases h2
        rw [Poly.app_nil_r]
        exact ih1
      | _ => exact MApp s1 (re_opt (Union r1 r2)) s2 (re_opt _) ih1 ih2
    | Star r =>
      cases re2 with
      | EmptySet => cases h2
      | EmptyStr =>
        cases h2
        rw [Poly.app_nil_r]
        exact ih1
      | _ => exact MApp s1 (re_opt (Star r)) s2 (re_opt _) ih1 ih2
  | MUnionL s1 re1 re2 h1 ih1 =>
    cases re1 with
    | EmptySet => cases h1
    | EmptyStr =>
      cases re2 with
      | EmptySet => exact ih1
      | _ => exact MUnionL s1 _ _ ih1
    | _ =>
      cases re2 with
      | EmptySet => exact ih1
      | _ => exact MUnionL s1 _ _ ih1
  | MUnionR s2 re1 re2 h2 ih2 =>
    cases re1 with
    | EmptySet => exact ih2
    | _ =>
      cases re2 with
      | EmptySet => cases h2
      | _ => exact MUnionR s2 _ _ ih2
  | MStar0 r =>
    cases r with
    | EmptySet => exact MEmpty
    | EmptyStr => exact MEmpty
    | _ => exact MStar0 _
  | MStarApp s1 s2 r h1 h2 ih1 ih2 =>
    cases r with
    | EmptySet => cases h1
    | EmptyStr =>
      cases ih1
      cases ih2
      exact MEmpty
    | _ =>
      exact star_app s1 s2 _ (MStar1 s1 _ ih1) ih2

/-- 练习：利用组合子大幅精简 `re_opt_match` 的证明脚本 -/
theorem re_opt_match' {T : Type} (re : reg_exp T) (s : Poly.list T) (m : s =~ re) :
    s =~ re_opt re := by
  sorry

def manual_grade_for_re_opt : Option (Nat × String) := none

-- #################################################################
-- * 摆脱显式命名假说的策略
-- #################################################################

/-!
### 1. 显式命名的局限性与维护负担

在手工证明中，我们频繁给引入的假设人工命名（例如 `HP`, `Hnm` 等）。
若定理引理接口变更、参数顺序调整或前置步骤改动，硬编码的假说名字极易导致后续脚本大面积破碎。
证明助理提供了数种不依赖名字的鲁棒策略。
-/

/-- 硬编码假说名字的脆弱写法 -/
theorem hyp_name (P : Prop) : P → P := by
  intro HP
  exact HP

/-- 策略 1：`assumption`
    自动在当前假说上下文中检索，若存在类型与当前目标完全一致的假设，则直接封闭目标。 -/
theorem no_hyp_name (P : Prop) : P → P := by
  intros
  assumption

/-!
### 2. 矛盾闭合策略：`contradiction`

若上下文中直接包含 `False`，或存在互斥的假设（如 `h : P` 与 `hn : ¬P`），
或等式两端由互异的构造子构成（如 `0 = 1`），`contradiction` 立即证毕目标。
-/

/-- 手动解构 False 假设 -/
theorem false_assumed : False → 0 = 1 := by
  intro h
  cases h

/-- 利用 contradiction 自动排除 False -/
theorem false_assumed' : False → 0 = 1 := by
  intros
  contradiction

/-- 手动导出矛盾 -/
theorem contras (P : Prop) : P → ¬P → 0 = 1 := by
  intro hp hnp
  exfalso
  exact hnp hp

/-- 利用 contradiction 自动检测互斥假设 -/
theorem contras' (P : Prop) : P → ¬P → 0 = 1 := by
  intros
  contradiction

/-!
### 3. 等式消去策略：`subst`

`subst` 策略检测上下文中形如 `x = e` 或 `e = x` 的假设（其中 `x` 为局部变量），
在目标和所有其他假设中用 `e` 全局替换 `x`，并从上下文中自动清除该变量与等式假设。
在 Lean 4 中，可使用 `subst <var>` 或全局消去策略 `subst_vars`。
-/

/-- 手动逐个重写等式 -/
theorem many_eq (n m o p : Nat) :
    n = m → o = p → [n; o] = [m; p] := by
  intro hnm hop
  rw [hnm, hop]

/-- 利用 subst_vars 自动消去等式变量 -/
theorem many_eq' (n m o p : Nat) :
    n = m → o = p → [n; o] = [m; p] := by
  intros
  subst_vars
  rfl

/-!
### 4. 构造子自动选择策略：`constructor`

`constructor` 尝试在当前归纳类型的构造子列表中匹配第一个能够统一当前目标的构造子，并将其 `apply` 到目标上。
-/

/-- 使用 constructor 自动应用归纳谓词的构造子 -/
theorem constructor_example (n : Nat) : ev (n + n) := by
  induction n with
  | zero =>
    dsimp
    constructor
  | succ n' ih =>
    have h_eq : Nat.succ n' + Nat.succ n' = (n' + n') + 2 := by omega
    rw [h_eq]
    constructor
    assumption

-- #################################################################
-- * 自动求解器 (Automatic Solvers)
-- #################################################################

/-!
### 1. 线性整数算术：`omega` (对应 Coq 的 `lia`)

线性整数算术是命题逻辑与一阶线性算术（加法、减法、常数倍乘法、整数大小比较）的判定问题。
Presburger 算术是可判定的。
在 Lean 4 中，内置的核心算法为 `omega`（在 Coq 中为 `lia`）。
-/

/-- 线性不等式自动求解 -/
theorem lia_succeed1 (n : Nat) : n > 0 → n * 2 > n := by
  omega

/-- 线性结合律与交换律判定 -/
theorem lia_succeed2 (n m : Nat) : n + m = m + n := by
  omega

/-!
对于超出线性算术范畴的目标（例如包含高阶非线性运算 `2 ^ n`），
求解器若失败并不意味着命题假，而是超出决策过程的判定能力界限。
例如：
- `0 = 1` 为假目标，`omega` 必定报错；
- `n ≥ 1 → 2 ^ n = 2 * 2 ^ (n - 1)` 为真命题，但因含指数运算而无法由 `omega` 直接闭合。
-/

/-- 乘法交换律（直接由标准库 Nat.mul_comm 给出） -/
theorem mult_comm (n m : Nat) : n * m = m * n := by
  exact Nat.mul_comm n m

/-!
### 2. 同余与无解释函数等式：`congr` (对应 Coq 的 `congruence`)

若将等式中的所有函数视作“黑盒”（不展开其定义），仅依据等式的自反性、对称性、传递性以及**同余性**（即 $x = y \implies f(x) = f(y)$），
许多等式命题依然可以完全自动获证。
在 Lean 4 中，`congr`、`contradiction` 与注入性推理承担了这一职责。
-/

/-- 手动重写函数应用等式 -/
theorem eq_example1 (A B C : Type) (f : A → B) (g : B → C) (x : A) (y : B) :
    y = f x → g y = g (f x) := by
  intro h
  rw [h]

/-- 利用同余策略自动完成函数等式传递 -/
theorem eq_example1' (A B C : Type) (f : A → B) (g : B → C) (x : A) (y : B) :
    y = f x → g y = g (f x) := by
  intro h
  congr

/-- 构造子注入性与同余性质组合 -/
theorem eq_example2 (n m o p : Nat) :
    n = m → o = p → (n, o) = (m, p) := by
  intro h1 h2
  congr

/-- 构造子互异性自动否定 -/
theorem eq_example3 (X : Type) (h : X) (t : Poly.list X) :
    nil ≠ h :: t := by
  intro hc
  contradiction

/-!
### 3. 直觉主义命题重言式：`tauto` (对应 Coq 的 `intuition`)

`tauto` 实现了直觉主义一阶命题逻辑（不含待实例化的全称量词）的完全自动判定。
-/

/-- 命题逻辑同一律 -/
theorem intuition_succeed1 (P : Prop) : P → P := by
  intro h; exact h

/-- 德摩根定律单向判定 -/
theorem intuition_succeed2 (P Q : Prop) : ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  intro h
  constructor
  · intro hp; exact h (Or.inl hp)
  · intro hq; exact h (Or.inr hq)

/-!
注意：双重否定消除律 `¬¬P → P` 在构造性直觉逻辑中不可证，故 `tauto` 无法闭合它。
-/

/-- 命题逻辑与等式同余混合判定 -/
theorem intuition_simplify2 (x y : Nat) (P Q : Nat → Prop) :
    x = y ∧ (P x → Q x) ∧ P x → Q y := by
  intro ⟨hxy, hpq, hp⟩
  subst hxy
  exact hpq hp

/-- 配合自动化求解策略一行证明 -/
theorem intuition_simplify2' (x y : Nat) (P Q : Nat → Prop) :
    x = y ∧ (P x → Q x) ∧ P x → Q y := by
  intro ⟨hxy, hpq, hp⟩
  subst hxy
  solve_by_elim

/-!
#### 练习：2 星, standard (automatic_solvers)

以下定理来自前面章节，曾需要繁琐的手工证明。
现在请使用自动求解器（如 `omega`, `congr`, `solve_by_elim` 等）一行完成证明。
-/

theorem plus_id_exercise_from_basics (n m o : Nat) :
    n = m → m = o → n + m = m + o := by
  sorry

theorem add_assoc_from_induction (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  sorry

theorem S_injective_from_tactics (n m : Nat) :
    Nat.succ n = Nat.succ m → n = m := by
  sorry

theorem or_distributes_over_and_from_logic (P Q R : Prop) :
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry

-- #################################################################
-- * 自动证明搜索 (Search Tactics)
-- #################################################################

/-!
### 1. `auto` 与 `solve_by_elim`

前面的特定领域求解器无法利用我们自定义的引理与数据类型构造子。
`solve_by_elim`（以及我们在 Lean 4 中封装的 `auto`）通过深度优先搜索与回溯，
自动尝试将局部假设和知识库中的定理应用到目标上。
-/

/-- 定义 Lean 4 语义对齐的 `auto` 策略宏 -/
macro "auto" : tactic => `(tactic| (intros; solve_by_elim))

/-- 手工单步应用 -/
theorem auto_example_1 (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by
  intro H1 H2 H3
  exact H2 (H1 H3)

/-- 自动证明搜索 -/
theorem auto_example_1' (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by
  auto

/-- 深度多层蕴含传递自动搜索 -/
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

/-- 超过默认搜索深度的链条 -/
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

/-- 自动搜索合取与析取组合 -/
theorem auto_example_4 (P Q R : Prop) :
    Q →
    (Q → R) →
    P ∨ (Q ∧ R) := by
  intro hq hqr
  right
  exact ⟨hq, hqr hq⟩

/-- 恒等关系自动闭合 -/
theorem auto_example_5 : 2 = 2 := by
  rfl

/-- 自然数反对称引理 -/
theorem le_antisym (n m : Nat) : (n ≤ m ∧ m ≤ n) → n = m := by
  omega

/-- 传入额外引理进行搜索：`solve_by_elim [...]` (对应 Coq 的 `auto using ...`) -/
theorem auto_example_6 (n m p : Nat) :
    (n ≤ p → (n ≤ m ∧ m ≤ n)) →
    n ≤ p →
    n = m := by
  intro h1 h2
  have h := h1 h2
  exact le_antisym n m h

theorem auto_example_6' (n m p : Nat) :
    (n ≤ p → (n ≤ m ∧ m ≤ n)) →
    n ≤ p →
    n = m := by
  intro h1 h2
  have h := h1 h2
  exact le_antisym n m h

/-- 自定义谓词符号展开 -/
def is_fortytwo (x : Nat) : Prop := (x = 42)

/-!
在 Coq 中，`auto_example_7` 展示了若不展开 `is_fortytwo`，`auto` 毫无进展（因而被 `Abort`）。
通过向提示库声明 `Hint Unfold is_fortytwo`，`auto with le_db` 才能获证。
在 Lean 4 中，展开定义配合算术决策过程即可顺利完成：
-/

/-- 在展开自定义谓词后，自动化策略即可闭合目标 -/
theorem auto_example_7 (x : Nat) :
    (x ≤ 42 ∧ 42 ≤ x) → is_fortytwo x := by
  intro ⟨h1, h2⟩
  dsimp [is_fortytwo]
  omega

theorem auto_example_7' (x : Nat) :
    (x ≤ 42 ∧ 42 ≤ x) → is_fortytwo x := by
  intro ⟨h1, h2⟩
  dsimp [is_fortytwo]
  omega

theorem auto_example_8 (n m : Nat) : n + m = m + n := by
  omega

/-!
#### 练习：3 星, standard (re_opt_match_auto)

利用自动化搜索与构造子策略，进一步精简 `re_opt_match` 的证明。
-/

theorem re_opt_match'' {T : Type} (re : reg_exp T) (s : Poly.list T) (m : s =~ re) :
    s =~ re_opt re := by
  sorry

def manual_grade_for_re_opt_match'' : Option (Nat × String) := none

/-!
#### 练习：3 星, advanced, optional (pumping_redux)

利用 `auto`、`omega` 等自动化策略重构 [IndProp](/LF/IndProp)
中的弱泵引理（Weak Pumping Lemma）。
-/

theorem weak_pumping {T : Type} (re : reg_exp T) (s : Poly.list T)
    (hm : s =~ re) (hl : pumping_constant re ≤ length s) :
    ∃ s1 s2 s3 : Poly.list T,
      s = s1 ++ s2 ++ s3 ∧
      s2 ≠ nil ∧
      ∀ m : Nat, s1 ++ napp m s2 ++ s3 =~ re := by
  sorry

def manual_grade_for_pumping_redux : Option (Nat × String) := none

/-!
#### 练习：3 星, advanced, optional (pumping_redux_strong)

类似地，重构强化版泵引理（Strong Pumping Lemma）。
-/

theorem pumping {T : Type} (re : reg_exp T) (s : Poly.list T)
    (hm : s =~ re) (hl : pumping_constant re ≤ length s) :
    ∃ s1 s2 s3 : Poly.list T,
      s = s1 ++ s2 ++ s3 ∧
      s2 ≠ nil ∧
      length s1 + length s2 ≤ pumping_constant re ∧
      ∀ m : Nat, s1 ++ napp m s2 ++ s3 =~ re := by
  sorry

def manual_grade_for_pumping_redux_strong : Option (Nat × String) := none

/-!
### 2. 延迟实例化与存在元变量：`apply` 与 `eauto`

在 Coq 中，`apply` 若遇到结论中未出现的中间变量（例如传递性定理中的中间项），会因为无法统合而直接报错，
必须显式写出 `apply ... with ...` 或改用带有存在元变量机制的 `eapply` 与 `eauto`。

在 Lean 4 中，元变量（Metavariables，形如 `?m`）被设计为系统的**一等公民**。
普通的 `apply` 会自动生成未约束的元变量子目标，不需要记忆特殊的 `eapply`！
-/

/-- 显式提供中间项的传递性应用 -/
theorem trans_example1 (a b c d : Nat) :
    a ≤ b + b * c →
    (1 + c) * b ≤ d →
    a ≤ d := by
  intro h1 h2
  apply Nat.le_trans (m := b + b * c)
  · exact h1
  · have h_eq : (1 + c) * b = b + b * c := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm c b]
    rw [h_eq] at h2
    exact h2

/-- 不显式提供中间项：Lean 4 的 `apply` 原生支持未决元变量 -/
theorem trans_example1' (a b c d : Nat) :
    a ≤ b + b * c →
    (1 + c) * b ≤ d →
    a ≤ d := by
  intro h1 h2
  apply Nat.le_trans
  · exact h1
  · have h_eq : (1 + c) * b = b + b * c := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm c b]
    rw [h_eq] at h2
    exact h2

/-- 直接由传递性函数构造复合证据 -/
theorem trans_example2 (a b c d : Nat) :
    a ≤ b + b * c →
    b + b * c ≤ d →
    a ≤ d := by
  intro h1 h2
  exact Nat.le_trans h1 h2

-- #################################################################
-- * 战术语言与元编程 (Tactic Metaprogramming)
-- #################################################################

/-!
### 1. 战术宏 (Tactic Macros)

在 Coq 中，用户使用 `Ltac` 编写新的战术函数；
在 Lean 4 中，我们使用宏系统（`macro` 或 `syntax` + `macro_rules`）轻松扩展证明指令集。
-/

/-- 定义复合战术宏：化简并尝试运行传入的策略 -/
syntax "simpl_and_try " tacticSeq : tactic
macro_rules
  | `(tactic| simpl_and_try $tac:tacticSeq) =>
    `(tactic| (dsimp; try ($tac)))

theorem sat_ex1 : 1 + 1 = 2 := by
  simpl_and_try rfl

theorem sat_ex2 (n : Nat) : 1 - 1 + n + 1 = 1 + n := by
  simpl_and_try rfl
  omega

/-!
考察下列三个结构高度相似的布尔与自然数定理：
-/

theorem plus_1_neq_0 (n : Nat) :
    ((n + 1) =? 0) = false := by
  cases n <;> rfl

theorem negb_involutive (b : Bool) :
    (!(!b)) = b := by
  cases b <;> rfl

theorem andb_commutative (b c : Bool) :
    (b && c) = (c && b) := by
  cases b
  · cases c <;> rfl
  · cases c <;> rfl

/-!
我们可以将这种“析构变量并在每个分支尝试 `rfl`”的证明模式抽象为宏 `destructpf`：
-/

/-- 自定义战术宏：析构目标并在各分支尝试自反性闭合 -/
syntax "destructpf " Lean.Parser.Tactic.elimTarget : tactic
macro_rules
  | `(tactic| destructpf $x) =>
    `(tactic| (cases $x <;> try rfl))

theorem plus_1_neq_0' (n : Nat) :
    ((n + 1) =? 0) = false := by
  destructpf n

theorem negb_involutive' (b : Bool) :
    (!(!b)) = b := by
  destructpf b

theorem andb_commutative' (b c : Bool) :
    (b && c) = (c && b) := by
  destructpf b <;> destructpf c

/-!
#### 练习：1 星, standard (andb3_exchange)

仅使用 `destructpf` 与结合子完成三元布尔与交换律的证明。
-/

theorem andb3_exchange (b c d : Bool) :
    (b && c) && d = (b && d) && c := by
  sorry

/-!
#### 练习：2 星, standard (andb_true_elim2)

以下定理无法单纯由基础 `destructpf` 解决：
-/

theorem andb_true_elim2 (b c : Bool) :
    (b && c) = true → c = true := by
  intro h
  cases b
  · contradiction
  · exact h

/-- 增强型战术宏定义骨架 -/
syntax "destructpf' " Lean.Parser.Tactic.elimTarget : tactic
macro_rules
  | `(tactic| destructpf' $x) =>
    `(tactic| (cases $x <;> try rfl <;> try (intro h; cases h; try rfl)))

/-- 练习：使用改进后的宏证明 andb_true_elim2' -/
theorem andb_true_elim2' (b c : Bool) :
    (b && c) = true → c = true := by
  sorry

/-- 练习：验证新宏对先前的交换律依然通用 -/
theorem andb3_exchange' (b c d : Bool) :
    (b && c) && d = (b && d) && c := by
  sorry

-- #################################################################
-- * 目标模式匹配 (Pattern Matching on Proof State)
-- #################################################################

/-!
### 2. 匹配证明状态：Coq 的 `match goal` 与 Lean 4 的宏匹配

在归纳证明中，常见的后续步骤为：
化简当前目标，检索出形状如 `_ = _` 的归纳假设，并在目标中执行重写。
在 Coq 中，这由 `match goal with ...` 实现；
在 Lean 4 中，我们可以通过 `first | ...` 或类型导向的重写 `rw [‹_ = _›]` 完成。
-/

/-- 手动归纳并利用归纳假设重写 -/
theorem app_nil_r {X : Type} (lst : Poly.list X) :
    lst ++ nil = lst := by
  induction lst with
  | nil => rfl
  | cons h t ih =>
    dsimp [Poly.app]
    rw [ih]

/-- 模式匹配演练 1：匹配平凡目标 -/
theorem match_ex1 : True := by
  trivial

/-- 模式匹配演练 2：匹配复合合取目标 -/
theorem match_ex2 : True ∧ True := by
  exact ⟨trivial, trivial⟩

theorem match_ex2' : True ∧ True := by
  exact ⟨trivial, trivial⟩

theorem match_ex2'' : True ∧ True := by
  exact ⟨trivial, trivial⟩

/-- 模式匹配演练 3：检索假设类型与目标完全匹配的项 -/
theorem match_ex3 (P : Prop) : P → P := by
  intro hp
  exact hp

theorem match_ex3' (P : Prop) : P → P := by
  intro hp
  exact hp

/-- 模式匹配演练 4：在多个假设中回溯匹配目标 -/
theorem match_ex4 (P Q : Prop) : P → Q → P := by
  intro hp _
  exact hp

/-- 模式匹配演练 5：非线性模式变量（假设类型与结论严格同一） -/
theorem match_ex5 (P Q : Prop) : P → Q → P := by
  intro hp _
  exact hp

/-!
### 非线性模式匹配的约束

在常规的项级模式匹配中（无论在 Coq 还是 Lean 4），
同一个模式变量不能在一个模式分支中出现两次（即**线性模式要求**）。
例如：`| x :: x :: _ => true` 会引发编译报错。
而在证明状态的元层级模式匹配中，求解器允许匹配具有相同类型的两项。
-/

/-- 再次观察常规列表拼接定理 -/
theorem app_nil_r' {X : Type} (lst : Poly.list X) :
    lst ++ nil = lst := by
  induction lst with
  | nil => rfl
  | cons h t ih =>
    dsimp [Poly.app]
    rw [ih]

/-- 自定义简单归纳宏：归纳后自动尝试化简与假说重写 -/
syntax "simple_induction " Lean.Parser.Tactic.elimTarget : tactic
macro_rules
  | `(tactic| simple_induction $x) =>
    `(tactic| (
      induction $x <;>
        (try (first | rfl | (dsimp [Poly.app]; simp_all; try rfl)))
    ))

/-- 自动化简单归纳应用示例 -/
theorem app_nil_r'' {X : Type} (lst : Poly.list X) :
    lst ++ nil = lst := by
  simple_induction lst

/-- 加法结合律（对最右侧变量归纳） -/
theorem add_assoc'' (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  omega

theorem add_assoc''' (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  omega

/-- 自然数加法后继外提性质 -/
theorem plus_n_Sm (n m : Nat) :
    Nat.succ (n + m) = n + Nat.succ m := by
  omega

theorem plus_n_Sm' (n m : Nat) :
    Nat.succ (n + m) = n + Nat.succ m := by
  omega

-- #################################################################
-- * 自定义命题重言式求解器
-- #################################################################

/-!
### 3. 实现极简蕴含重言式判定宏：`imp_intuition`
-/

/-- 自动引入假设并利用假说网络回溯搜索 -/
macro "imp_intuition" : tactic => `(tactic| (intros; solve_by_elim))

theorem imp1 (P : Prop) : P → P := by
  imp_intuition

theorem imp2 (P Q : Prop) : P → (P → Q) → Q := by
  imp_intuition

theorem imp3 (P Q R : Prop) : (P → Q → R) → (Q → P → R) := by
  imp_intuition

/-!
### 4. 扩展逻辑联结词：`nor` (或非 / Pierce 箭头)

考察逻辑联结词 `nor P Q`（即 $\neg(P \lor Q)$ 的构造性形式）：
两个命题皆为假。
-/

/-- 逻辑“或非”归纳定义 -/
inductive nor (P Q : Prop) : Prop where
  | stroke : ¬P → ¬Q → nor P Q

open nor

/-- nor 蕴含非析取 -/
theorem nor_not_or (P Q : Prop) :
    nor P Q → ¬(P ∨ Q) := by
  intro (stroke np nq) h
  cases h with
  | inl hp => exact np hp
  | inr hq => exact nq hq

/-- nor 的交换律 -/
theorem nor_comm (P Q : Prop) :
    nor P Q ↔ nor Q P := by
  constructor
  · intro (stroke np nq)
    exact stroke nq np
  · intro (stroke nq np)
    exact stroke np nq

/-- nor 自同一与否定的等价性 -/
theorem nor_not (P : Prop) :
    nor P P ↔ ¬P := by
  constructor
  · intro (stroke np _)
    exact np
  · intro np
    exact stroke np np

/-!
#### 练习：4 星, advanced (nor_intuition)

构造能够全自动处理包含 `nor`、合取、析取与否定命题的判定策略。
在下列三个定理的证明中，每个都应当能够一键证毕。
-/

/-- 练习：nor 交换律重构 -/
theorem nor_comm' (P Q : Prop) :
    nor P Q ↔ nor Q P := by
  sorry

/-- 练习：nor 与否定等价性重构 -/
theorem nor_not' (P : Prop) :
    nor P P ↔ ¬P := by
  sorry

/-- 练习：nor 蕴含非合取 -/
theorem nor_not_and' (P Q : Prop) :
    nor P Q → ¬(P ∧ Q) := by
  sorry

def manual_grade_for_nor_intuition : Option (Nat × String) := none

-- #################################################################
-- * 章节全景回顾 (Review)
-- #################################################################

/-!
在本章中，我们系统学习了现代证明助理中构建高效、健壮证明的关键技术：

1. **组合子 (Tacticals)**：
   - `try`: 尝试执行，失败时安全静默返回；
   - `<;>`: 将后续操作批量派发到每一个衍生子目标；
   - `repeat`: 迭代执行直到不动点；
2. **免显式命名策略**：
   - `assumption`: 依据目标类型自动闭合；
   - `contradiction`: 自动识别矛盾上下文；
   - `subst` / `subst_vars`: 批量消去等式变量；
   - `constructor`: 自动选择适用的构造子；
3. **领域决策过程 (Decision Procedures)**：
   - 线性整数算术：Lean 4 的 `omega`（对应 Coq 的 `lia`）；
   - 同余闭包：`congr` 与构造子互异性；
   - 命题重言式：`tauto`；
4. **证明搜索**：
   - `solve_by_elim` / `auto`: 基于深度优先回溯的假说网络推导；
   - 存在元变量（Metavariables）的灵活推迟实例化；
5. **战术宏与元编程**：
   - 利用 `syntax` 与 `macro_rules` 抽象常见归纳重写范式。

掌握这些工具之后，我们便拥有了形式化更具挑战性的数学概念与软件系统语义的利刃！
-/

end AltAuto
