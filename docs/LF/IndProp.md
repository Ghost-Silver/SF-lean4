---
title: "IndProp: 归纳命题与关系：置换、泵引理与正则导数"
---

```lean
import SFLean4.LF.Basics
import SFLean4.LF.Induction
import SFLean4.LF.Lists
import SFLean4.LF.Poly
import SFLean4.LF.Tactics
import SFLean4.LF.Logic
```

# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)

## 第七章：归纳命题与关系 (IndProp: Inductively Defined Propositions)

在前几章中，我们学习了构造命题的多种核心方式：
- 等式命题（`e1 = e2`）；
- 全称与蕴含命题（`∀ x, P x` 与 `P → Q`）；
- 命题逻辑联结词（`∧`, `∨`, `¬`, `False`, `True`, `↔`, `∃`）。

然而，现实计算机科学中存在大量错综复杂、具有无限展开潜力的断言与关系——
例如：
- 形式语言与操作语义中的**转移系统**与多步归约（Small-Step / Big-Step Semantics）；
- 正则表达式匹配器中字符串与模式的**生成判定**；
- 列表中元素的**排列 (Permutation)**、**无重复性 (NoDup)** 与**子序列 (Subsequence)** 关系；
- 图论与有限状态机中的**传递闭包**与**可达性**。

面对这类问题，仅凭普通函数或简单逻辑联结词往往难以表达（可能受限于停机检查或算法复杂性）。
为此，本章将引入依赖类型论中最强大、最核心的建模工具：**归纳定义的命题（Inductively Defined Propositions / Inductive Predicates）**！

### 本章核心学习目标：
1. **归纳命题的定义机制**：
   - 掌握通过推理规则（Inference Rules）声明归纳谓词，理解参数（Parameters）与索引（Indices）的根本区别；
   - 学习柯拉茨猜想（Collatz Conjecture）、偶数谓词 `ev` 与排列关系 `Perm3` 的直观定义。
2. **在证明中解构与使用归纳证据**：
   - **反演 (Inversion / `cases`)**：学会根据给定的归纳证据，反向枚举并穷尽所有可能生成它的前置条件；
   - **在证据上进行归纳 (Induction on Evidence)**：深入理解何时不能对普通数据归纳，而必须直接对**命题证据本身**进行结构归纳；
3. **案例研究：正则表达式的形式化验证**：
   - 将语法结构 `reg_exp` 与匹配谓词 `exp_match`（记作 `s =~ re`）形式化；
   - 证明形式语言领域的重磅定理：**泵引理 (Pumping Lemma)**；
4. **布尔反射与元逻辑深化**：
   - 探究 `reflect` 归纳结构，建立布尔测试与形式化证据间的无缝跳转；
   - 证明鸽巢原理（Pigeonhole Principle）与非停滞列表判定；
5. **扩展案例：经过验证的正则表达式导数匹配器**：
   - 形式化验证布尔佐夫斯基导数（Brzozowski Derivatives）与正则表达式匹配算法的正确性。

```lean
namespace IndProp

open Poly
open Poly.list
open Poly.prod
open Poly.option
open Tactics
open Logic

/-- 皮亚诺后继记号别名，对齐原版 Coq 的 `S` -/
abbrev S := Nat.succ

/-- 自然数零记号别名，对齐原版 Coq 的 `O` -/
abbrev O := 0

/-- 自然数前驱函数别名，对齐原版 Coq 的 `pred` -/
abbrev pred := Nat.pred
```

## 1. 归纳定义的命题 (Inductively Defined Propositions)

### 1.1 柯拉茨猜想 (The Collatz Conjecture)

著名的柯拉茨猜想（3n + 1 猜想）指出：任取一个正整数 $n$，若为偶数则除以 2，若为奇数则乘以 3 加 1，
反复迭代此操作，最终必然抵达 1。

我们首先定义单步计算函数 `csf`（Collatz Step Function）：

```lean
/-- 自然数除以 2 的递归实现 -/
def div2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => div2 n + 1

/-- 柯拉茨单步步进函数 -/
def csf (n : Nat) : Nat :=
  if even n then div2 n
  else (3 * n) + 1
```

如果我们试图编写一个递归函数 `reaches1_in n` 来计算步数，或定义递归谓词 `Collatz_holds_for n : Prop`，
编译器会断然拒绝——因为 $(3n + 1)$ 并不比 $n$ 小，无法通过停机性检查器（Termination Checker）。

然而，借由**归纳命题**，我们可以将“最终抵达 1”表述为由三条推理规则生成的证据系统：
- 规则一（基步）：1 必定抵达 1；
- 规则二（偶数步）：若 $n$ 为偶数且 `div2 n` 抵达 1，则 $n$ 抵达 1；
- 规则三（奇数步）：若 $n$ 为奇数且 `3n + 1` 抵达 1，则 $n$ 抵达 1。

```lean
/-- 柯拉茨性质的归纳谓词定义 -/
inductive Collatz_holds_for : Nat → Prop where
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n : Nat) : even n = true → Collatz_holds_for (div2 n) → Collatz_holds_for n
  | Chf_odd (n : Nat) : even n = false → Collatz_holds_for ((3 * n) + 1) → Collatz_holds_for n

/-- 证明 12 满足柯拉茨猜想：构造自下而上的有限推导树证据 -/
theorem Collatz_holds_for_12 : Collatz_holds_for 12 := by
  apply Collatz_holds_for.Chf_even (n := 12) <;> try rfl
  apply Collatz_holds_for.Chf_even (n := 6) <;> try rfl
  apply Collatz_holds_for.Chf_odd (n := 3) <;> try rfl
  apply Collatz_holds_for.Chf_even (n := 10) <;> try rfl
  apply Collatz_holds_for.Chf_odd (n := 5) <;> try rfl
  apply Collatz_holds_for.Chf_even (n := 16) <;> try rfl
  apply Collatz_holds_for.Chf_even (n := 8) <;> try rfl
  apply Collatz_holds_for.Chf_even (n := 4) <;> try rfl
  apply Collatz_holds_for.Chf_even (n := 2) <;> try rfl
  exact Collatz_holds_for.Chf_one

/-- 柯拉茨猜想公理陈述：所有非零自然数均满足 Collatz_holds_for -/
axiom collatz : ∀ n : Nat, n ≠ 0 → Collatz_holds_for n
```

### 1.2 自然数大小比较的二元关系 (Binary Relation for Comparing Numbers)

```lean
namespace LePlayground

/-- 自然数小于等于关系的归纳定义 -/
inductive le : Nat → Nat → Prop where
  | le_n (n : Nat) : le n n
  | le_S (n m : Nat) : le n m → le n (m + 1)

/-- 3 <= 5 的构造性证据示例 -/
theorem le_3_5 : le 3 5 :=
  le.le_S 3 4 (le.le_S 3 3 (le.le_n 3))

end LePlayground
```

### 1.3 传递闭包 (Transitive Closure)

给定任意二元关系 $R$，其传递闭包 `clos_trans R` 是包含 $R$ 的最小传递关系。

```lean
/-- 二元关系的传递闭包 -/
inductive clos_trans {X : Type} (R : X → X → Prop) : X → X → Prop where
  | t_step (x y : X) : R x y → clos_trans R x y
  | t_trans (x y z : X) : clos_trans R x y → clos_trans R y z → clos_trans R x z

/-- 人物类型 -/
inductive Person : Type where
  | Sage : Person
  | Cleo : Person
  | Ridley : Person
  | Moss : Person

/-- 父母关系 -/
inductive parent_of : Person → Person → Prop where
  | po_SC : parent_of Person.Sage Person.Cleo
  | po_SR : parent_of Person.Sage Person.Ridley
  | po_CM : parent_of Person.Cleo Person.Moss

/-- 祖先关系：父母关系的传递闭包 -/
def ancestor_of : Person → Person → Prop :=
  clos_trans parent_of

/-- 证明 Sage 是 Moss 的祖先 -/
theorem ancestor_of_ex : ancestor_of Person.Sage Person.Moss := by
  dsimp [ancestor_of]
  apply clos_trans.t_trans Person.Sage Person.Cleo Person.Moss
  · exact clos_trans.t_step _ _ parent_of.po_SC
  · exact clos_trans.t_step _ _ parent_of.po_CM
```

### 1.4 自反传递闭包 (Reflexive and Transitive Closure)

```lean
/-- 自反传递闭包 -/
inductive clos_refl_trans {X : Type} (R : X → X → Prop) : X → X → Prop where
  | rt_step (x y : X) : R x y → clos_refl_trans R x y
  | rt_refl (x : X) : clos_refl_trans R x x
  | rt_trans (x y z : X) : clos_refl_trans R x y → clos_refl_trans R y z → clos_refl_trans R x z

/-- 柯拉茨单步转移关系 -/
def cs (n m : Nat) : Prop := csf n = m

/-- 柯拉茨多步转移关系：单步转移关系的自反传递闭包 -/
def cms (n m : Nat) : Prop := clos_refl_trans cs n m

/-- 柯拉茨猜想的等价闭包表述 -/
axiom collatz' : ∀ n : Nat, n ≠ 0 → cms n 1
```

### 🎯 练习：`clos_refl_trans_sym` <Badge type="tip" text="1 星 · standard, optional" />

```lean
/-- 自反、对称且传递闭包 -/
inductive clos_refl_trans_sym {X : Type} (R : X → X → Prop) : X → X → Prop where
  | rts_step (x y : X) : R x y → clos_refl_trans_sym R x y
  | rts_refl (x : X) : clos_refl_trans_sym R x x
  | rts_trans (x y z : X) : clos_refl_trans_sym R x y → clos_refl_trans_sym R y z → clos_refl_trans_sym R x z
  | rts_sym (x y : X) : clos_refl_trans_sym R x y → clos_refl_trans_sym R y x
```

### 1.5 排列关系 (Permutations)

三元素列表置换关系的归纳定义：

```lean
/-- 三元素列表的置换关系谓词 -/
inductive Perm3 {X : Type} : list X → list X → Prop where
  | perm3_swap12 (a b c : X) : Perm3 [a; b; c] [b; a; c]
  | perm3_swap23 (a b c : X) : Perm3 [a; b; c] [a; c; b]
  | perm3_trans (l1 l2 l3 : list X) : Perm3 l1 l2 → Perm3 l2 l3 → Perm3 l1 l3
```

### 🎯 练习：`perm` <Badge type="tip" text="1 星 · standard, optional" />

根据上述定义，`[1; 2; 3]` 是否为其自身的置换？
**答**：是的。因为可通过两次对合交换得到：
`Perm3 [1; 2; 3] [2; 1; 3]` 与 `Perm3 [2; 1; 3] [1; 2; 3]`，
结合 `perm3_trans` 即可推导 `Perm3 [1; 2; 3] [1; 2; 3]`。

### 1.6 偶数命题（第三次相遇） (Evenness yet again)

在前面章节中，我们已经见过了偶数的两种形式化：
1. 布尔计算：`even n = true`；
2. 存在量词命题：`Even n ≜ ∃ k, n = double k`。

现在，我们给出偶数的**归纳谓词**定义：
- 0 是偶数（`ev_0`）；
- 若 $n$ 是偶数，则 $n + 2$ 也是偶数（`ev_SS`）。

```lean
/-- 偶数的归纳谓词定义 -/
inductive ev : Nat → Prop where
  | ev_0 : ev 0
  | ev_SS (n : Nat) (h : ev n) : ev (n + 2)

namespace EvPlayground

inductive ev : Nat → Prop where
  | ev_0 : ev 0
  | ev_SS : ∀ n : Nat, ev n → ev (n + 2)

end EvPlayground

/-- 证明 4 是偶数 -/
theorem ev_4 : ev 4 := by
  apply ev.ev_SS
  apply ev.ev_SS
  exact ev.ev_0

/-- 通过显式函数项组合证据证明 4 是偶数 -/
theorem ev_4' : ev 4 :=
  ev.ev_SS 2 (ev.ev_SS 0 ev.ev_0)

/-- 若 n 是偶数，则 n + 4 亦为偶数 -/
theorem ev_plus4 (n : Nat) (hn : ev n) : ev (4 + n) := by
  rw [Nat.add_comm]
  apply ev.ev_SS
  apply ev.ev_SS
  exact hn
```

### 🎯 练习：`ev_double` <Badge type="tip" text="1 星 · standard" />

```lean
/-- 任意自然数翻倍后均为归纳偶数 -/
theorem ev_double (n : Nat) : ev (double n) := by
  sorry
```

### 1.7 构造排列证据 (Constructing Evidence for Permutations)

```lean
/-- 证明 [1; 2; 3] 与其逆序 [3; 2; 1] 互为置换 -/
theorem Perm3_rev : Perm3 [1; 2; 3] [3; 2; 1] := by
  apply Perm3.perm3_trans (l2 := [2; 3; 1])
  · apply Perm3.perm3_trans (l2 := [2; 1; 3])
    · exact Perm3.perm3_swap12 1 2 3
    · exact Perm3.perm3_swap23 2 1 3
  · exact Perm3.perm3_swap12 2 3 1

/-- 函数项构造证明 Perm3_rev' -/
theorem Perm3_rev' : Perm3 [1; 2; 3] [3; 2; 1] :=
  Perm3.perm3_trans [1; 2; 3] [2; 3; 1] [3; 2; 1]
    (Perm3.perm3_trans [1; 2; 3] [2; 1; 3] [2; 3; 1]
      (Perm3.perm3_swap12 1 2 3)
      (Perm3.perm3_swap23 2 1 3))
    (Perm3.perm3_swap12 2 3 1)
```

### 🎯 练习：`Perm3` <Badge type="tip" text="1 星 · standard" />

```lean
/-- 置换示例一 -/
theorem Perm3_ex1 : Perm3 [1; 2; 3] [2; 3; 1] := by
  sorry

/-- 置换关系的自反性 -/
theorem Perm3_refl (X : Type) (a b c : X) : Perm3 [a; b; c] [a; b; c] := by
  sorry
```

## 2. 在证明中使用证据 (Using Evidence in Proofs)

### 2.1 解构与反演证据 (Destructing and Inverting Evidence)

归纳定义不仅为我们提供了构造证据的手段，更宣告了这些构造子是**生成证据的仅有方式**！
因此，当假设中包含 `ev n` 时，我们可以反向推导其来源：
要么 `n = 0`，要么存在 `n'` 使得 `n = n' + 2` 且 `ev n'`。

```lean
/-- 偶数反演引理 -/
theorem ev_inversion (n : Nat) (h : ev n) :
    n = 0 ∨ ∃ n', n = n' + 2 ∧ ev n' := by
  cases h with
  | ev_0 => left; rfl
  | ev_SS n' h' => right; exact ⟨n', rfl, h'⟩
```

### 🎯 练习：`le_inversion` <Badge type="tip" text="1 星 · standard" />

```lean
/-- 小于等于关系的反演引理 -/
theorem le_inversion (n m : Nat) (h : LePlayground.le n m) :
    n = m ∨ ∃ m', m = m' + 1 ∧ LePlayground.le n m' := by
  sorry

/-- 利用反演引理推导两步递减 -/
theorem evSS_ev (n : Nat) (h : ev (n + 2)) : ev n := by
  have h_inv := ev_inversion (n + 2) h
  rcases h_inv with h0 | ⟨n', hnm, hev⟩
  · contradiction
  · injection hnm with heq
    injection heq with heq'
    subst heq'
    exact hev

/-- 在 Lean 4 中，直接使用 cases 即可完成现代反演（免除繁琐的手动展开） -/
theorem evSS_ev' (n : Nat) (h : ev (n + 2)) : ev n := by
  cases h with
  | ev_SS _ h' => exact h'

/-- 1 绝非偶数（手动反演版） -/
theorem one_not_even : ¬(ev 1) := by
  intro h
  have h_inv := ev_inversion 1 h
  rcases h_inv with h0 | ⟨n', hnm, _⟩
  · contradiction
  · contradiction

/-- 1 绝非偶数（现代 cases 一行秒杀版） -/
theorem one_not_even' : ¬(ev 1) := by
  intro h
  cases h
```

### 🎯 练习：`inversion_practice` <Badge type="tip" text="1 星 · standard" />

```lean
/-- 连续四次后继偶数必定蕴含原数为偶数 -/
theorem SSSSev__even (n : Nat) (h : ev (n + 4)) : ev n := by
  sorry
```

### 🎯 练习：`ev5_nonsense` <Badge type="tip" text="1 星 · standard" />

```lean
/-- 从荒谬前提推导出任意结论 -/
theorem ev5_nonsense (h : ev 5) : 2 + 2 = 9 := by
  sorry

/-- 反演在等式假设上的应用示例 1 -/
theorem inversion_ex1 (n m o : Nat) (h : [n; m] = [o; o]) : (n :: nil) = (m :: nil) := by
  injection h with h1 h2
  injection h2 with h3
  rw [h1, h3]

/-- 反演在后继不相交等式上的应用示例 2 -/
theorem inversion_ex2 (n : Nat) (contra : n + 1 = 0) : 2 + 2 = 5 := by
  contradiction

/-- 尝试对证据执行普通分类讨论（展示归纳步缺乏归纳假设而卡住，原版 Coq 中以 Abort 演示） -/
theorem ev_Even_firsttry (n : Nat) (h : ev n) : Even n := by
  -- cases h 只能得到局部子证据，无法推演全称递归性质
  sorry
```

### 2.2 证据上的归纳 (Induction on Evidence)

当我们面对形如 `ev n` 的前提，并且需要证明关于 $n$ 的普遍性质时，
对数值 $n$ 进行归纳往往会受阻（因为 $n - 1$ 不是偶数！）；
正确的策略是：**直接对证据 `h : ev n` 进行结构归纳**！

```lean
/-- 归纳偶数蕴含存在量词翻倍偶数 -/
theorem ev_Even (n : Nat) (h : ev n) : Even n := by
  induction h with
  | ev_0 => exists 0
  | ev_SS n' h' ih =>
    rcases ih with ⟨k, hk⟩
    exists k + 1
    dsimp [double]
    rw [hk]

/-- 归纳偶数与存在量词偶数的充要等价性 -/
theorem ev_Even_iff (n : Nat) : ev n ↔ Even n := by
  constructor
  · exact ev_Even n
  · intro ⟨k, hk⟩
    rw [hk]
    exact ev_double k
```

### 🎯 练习：`ev_sum` <Badge type="info" text="2 星 · standard" />

```lean
/-- 两个偶数之和仍为偶数 -/
theorem ev_sum (n m : Nat) (hn : ev n) (hm : ev m) : ev (n + m) := by
  sorry
```

### 🎯 练习：`ev_ev__ev` <Badge type="warning" text="3 星 · advanced, especially useful" />

```lean
/-- 偶数减去偶数仍为偶数 -/
theorem ev_ev__ev (n m : Nat) (hnm : ev (n + m)) (hn : ev n) : ev m := by
  sorry
```

### 🎯 练习：`ev_plus_plus` <Badge type="warning" text="3 星 · standard, optional" />

```lean
/-- 偶数传递加法性质 -/
theorem ev_plus_plus (n m p : Nat) (h1 : ev (n + m)) (h2 : ev (n + p)) : ev (m + p) := by
  sorry
```

### 🎯 练习：`ev'_ev` <Badge type="danger" text="4 星 · advanced, optional" />

```lean
/-- 偶数的另一种双项归纳定义 -/
inductive ev' : Nat → Prop where
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum (n m : Nat) (hn : ev' n) (hm : ev' m) : ev' (n + m)

theorem ev'_ev (n : Nat) : ev' n ↔ ev n := by
  sorry

namespace Perm3Reminder

inductive Perm3 {X : Type} : list X → list X → Prop where
  | perm3_swap12 (a b c : X) : Perm3 [a; b; c] [b; a; c]
  | perm3_swap23 (a b c : X) : Perm3 [a; b; c] [a; c; b]
  | perm3_trans (l1 l2 l3 : list X) : Perm3 l1 l2 → Perm3 l2 l3 → Perm3 l1 l3

end Perm3Reminder

/-- 置换关系的对称性（对置换证据进行归纳） -/
theorem Perm3_symm (X : Type) (l1 l2 : list X) (h : Perm3 l1 l2) : Perm3 l2 l1 := by
  induction h with
  | perm3_swap12 a b c => exact Perm3.perm3_swap12 b a c
  | perm3_swap23 a b c => exact Perm3.perm3_swap23 a c b
  | perm3_trans _ _ _ _ _ ih1 ih2 => exact Perm3.perm3_trans _ _ _ ih2 ih1
```

### 🎯 练习：`Perm3_In` <Badge type="info" text="2 星 · standard" />

```lean
/-- 置换保持列表元素隶属度 -/
theorem Perm3_In (X : Type) (x : X) (l1 l2 : list X) (h : Perm3 l1 l2) (hin : In x l1) : In x l2 := by
  sorry
```

### 🎯 练习：`Perm3_NotIn` <Badge type="tip" text="1 星 · standard, optional" />

```lean
/-- 置换保持元素不隶属性质 -/
theorem Perm3_NotIn (X : Type) (x : X) (l1 l2 : list X) (h : Perm3 l1 l2) (hnin : ¬In x l1) : ¬In x l2 := by
  sorry
```

### 🎯 练习：`NotPerm3` <Badge type="info" text="2 星 · standard, optional" />

```lean
/-- 长度不一致的列表绝非置换 -/
theorem Perm3_example2 : ¬Perm3 [1; 2; 3] [1; 2] := by
  sorry
```

## 3. 归纳关系的综合练习 (Exercising with Inductive Relations)

```lean
namespace Playground

/-- 标准小于等于关系的归纳定义 -/
inductive le (n : Nat) : Nat → Prop where
  | le_n : le n n
  | le_S (m : Nat) (h : le n m) : le n (m + 1)

scoped notation:50 (priority := high) n:51 " <= " m:51 => le n m

theorem test_le1 : 3 <= 3 := le.le_n
theorem test_le2 : 3 <= 6 := le.le_S 5 (le.le_S 4 (le.le_S 3 le.le_n))
theorem test_le3 : (2 <= 1) → 2 + 2 = 5 := by
  intro h
  cases h with
  | le_S _ h' => cases h'

def lt (n m : Nat) : Prop := le (n + 1) m
def ge (n m : Nat) : Prop := le m n

scoped notation:50 (priority := high) n:51 " < " m:51 => lt n m
scoped notation:50 (priority := high) n:51 " >= " m:51 => ge n m
```

### 🎯 练习：`le_facts` <Badge type="warning" text="3 星 · standard, especially useful" />

```lean
theorem le_trans (m n o : Nat) (h1 : m <= n) (h2 : n <= o) : m <= o := by
  sorry

theorem O_le_n (n : Nat) : 0 <= n := by
  sorry

theorem n_le_m__Sn_le_Sm (n m : Nat) (h : n <= m) : (n + 1) <= (m + 1) := by
  sorry

theorem Sn_le_Sm__n_le_m (n m : Nat) (h : (n + 1) <= (m + 1)) : n <= m := by
  sorry

theorem le_plus_l (a b : Nat) : a <= a + b := by
  sorry
```

### 🎯 练习：`plus_le_facts1` <Badge type="info" text="2 星 · standard, especially useful" />

```lean
theorem plus_le (n1 n2 m : Nat) (h : n1 + n2 <= m) : n1 <= m ∧ n2 <= m := by
  sorry

theorem plus_le_cases (n m p q : Nat) (h : n + m <= p + q) : n <= p ∨ m <= q := by
  sorry
```

### 🎯 练习：`plus_le_facts2` <Badge type="info" text="2 星 · standard, especially useful" />

```lean
theorem plus_le_compat_l (n m p : Nat) (h : n <= m) : p + n <= p + m := by
  sorry

theorem plus_le_compat_r (n m p : Nat) (h : n <= m) : n + p <= m + p := by
  sorry

theorem le_plus_trans (n m p : Nat) (h : n <= m) : n <= m + p := by
  sorry
```

### 🎯 练习：`lt_facts` <Badge type="warning" text="3 星 · standard, optional" />

```lean
theorem lt_ge_cases (n m : Nat) : n < m ∨ n >= m := by
  sorry

theorem n_lt_m__n_le_m (n m : Nat) (h : n < m) : n <= m := by
  sorry

theorem plus_lt (n1 n2 m : Nat) (h : n1 + n2 < m) : n1 < m ∧ n2 < m := by
  sorry
```

### 🎯 练习：`leb_le` <Badge type="danger" text="4 星 · standard, optional" />

```lean
theorem leb_complete (n m : Nat) (h : (n <=? m) = true) : n <= m := by
  sorry

theorem leb_correct (n m : Nat) (h : n <= m) : (n <=? m) = true := by
  sorry

theorem leb_iff (n m : Nat) : (n <=? m) = true ↔ n <= m := by
  sorry

theorem leb_true_trans (n m o : Nat) (h1 : (n <=? m) = true) (h2 : (m <=? o) = true) :
    (n <=? o) = true := by
  sorry

end Playground

open Playground

namespace R

/-- #### 练习：3 星, standard, especially useful (R_provability) -/
inductive R : Nat → Nat → Nat → Prop where
  | c1 : R 0 0 0
  | c2 (m n o : Nat) (h : R m n o) : R (m + 1) n (o + 1)
  | c3 (m n o : Nat) (h : R m n o) : R m (n + 1) (o + 1)
  | c4 (m n o : Nat) (h : R (m + 1) (n + 1) (o + 2)) : R m n o
  | c5 (m n o : Nat) (h : R m n o) : R n m o
```

讨论命题 `R 1 1 2` 与 `R 2 2 6` 的可证性：
- `R 1 1 2` 是可证的（c1 → c2 → c3）；
- `R 2 2 6` 是不可证的（因为关系 R 本质上刻画了加法 m + n = o，而 2 + 2 ≠ 6）。

```lean
def manual_grade_for_R_provability : Option (Nat × String) := none

/-- #### 练习：3 星, standard, optional (R_fact) -/
def fR (m n : Nat) : Nat := m + n

theorem R_equiv_fR (m n o : Nat) : R m n o ↔ fR m n = o := by
  sorry

end R
```

### 🎯 练习：`subsequence` <Badge type="danger" text="4 星 · advanced" />

```lean
/-- 列表子序列关系的归纳定义 -/
inductive subseq : list Nat → list Nat → Prop where
  | subseq0 (l : list Nat) : subseq nil l
  | subseq1 (x : Nat) (l1 l2 : list Nat) (h : subseq l1 l2) : subseq (x :: l1) (x :: l2)
  | subseq2 (x : Nat) (l1 l2 : list Nat) (h : subseq l1 l2) : subseq l1 (x :: l2)

theorem subseq_refl (l : list Nat) : subseq l l := by
  sorry

theorem subseq_app (l1 l2 l3 : list Nat) (h : subseq l1 l2) : subseq l1 (l2 ++ l3) := by
  sorry

theorem subseq_trans (l1 l2 l3 : list Nat) (h1 : subseq l1 l2) (h2 : subseq l2 l3) : subseq l1 l3 := by
  sorry
```

### 🎯 练习：`R_provability2` <Badge type="info" text="2 星 · standard, optional" />
考虑归纳关系：
- c1 : R 0 []
- c2 : R (n+1) (n :: l) 由 R n l
- c3 : R n l 由 R (n+1) l

讨论：
- R 2 [1; 0] 可证；
- R 1 [1; 2; 1; 0] 可证；
- R 6 [3; 2; 1; 0] 不可证。

## 4. 案例研究：正则表达式 (Case Study: Regular Expressions)

```lean
/-- 多态正则表达式数据结构 -/
inductive reg_exp (T : Type) : Type where
  | EmptySet : reg_exp T
  | EmptyStr : reg_exp T
  | Char (t : T) : reg_exp T
  | App (r1 r2 : reg_exp T) : reg_exp T
  | Union (r1 r2 : reg_exp T) : reg_exp T
  | Star (r : reg_exp T) : reg_exp T

open reg_exp

/-- 正则表达式匹配归纳谓词 -/
inductive exp_match {T : Type} : list T → reg_exp T → Prop where
  | MEmpty : exp_match nil EmptyStr
  | MChar (x : T) : exp_match [x] (Char x)
  | MApp (s1 : list T) (re1 : reg_exp T) (s2 : list T) (re2 : reg_exp T)
      (h1 : exp_match s1 re1) (h2 : exp_match s2 re2) :
      exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL (s1 : list T) (re1 re2 : reg_exp T)
      (h1 : exp_match s1 re1) :
      exp_match s1 (Union re1 re2)
  | MUnionR (s2 : list T) (re1 re2 : reg_exp T)
      (h2 : exp_match s2 re2) :
      exp_match s2 (Union re1 re2)
  | MStar0 (re : reg_exp T) : exp_match nil (Star re)
  | MStarApp (s1 s2 : list T) (re : reg_exp T)
      (h1 : exp_match s1 re) (h2 : exp_match s2 (Star re)) :
      exp_match (s1 ++ s2) (Star re)

scoped notation:50 (priority := high) s:51 " =~ " re:51 => exp_match s re

open exp_match

theorem reg_exp_ex1 : [1] =~ Char 1 := by
  exact MChar 1

theorem reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2) := by
  have h := @MApp Nat [1] (Char 1) [2] (Char 2) (MChar 1) (MChar 2)
  exact h

theorem reg_exp_ex3 : ¬([1; 2] =~ Char 1) := by
  intro h
  generalize hs : ([1; 2] : list Nat) = s at h
  cases h
  injection hs
  contradiction

/-- 从列表构造精确匹配该列表的正则表达式 -/
def reg_exp_of_list {T : Type} : list T → reg_exp T
  | nil => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')

theorem reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3] := by
  dsimp [reg_exp_of_list]
  have h1 := @MApp Nat [1] (Char 1) [2; 3] (App (Char 2) (App (Char 3) EmptyStr))
  apply h1
  · exact MChar 1
  · have h2 := @MApp Nat [2] (Char 2) [3] (App (Char 3) EmptyStr)
    apply h2
    · exact MChar 2
    · have h3 := @MApp Nat [3] (Char 3) nil EmptyStr
      apply h3
      · exact MChar 3
      · exact MEmpty

/-- 单项匹配直接提升至 Star 匹配 -/
theorem MStar1 {T : Type} (s : list T) (re : reg_exp T) (h : s =~ re) : s =~ Star re := by
  have h' : s = s ++ nil := by rw [Poly.app_nil_r]
  rw [h']
  exact MStarApp s nil re h (MStar0 re)
```

### 🎯 练习：`exp_match_ex1` <Badge type="warning" text="3 星 · standard" />

```lean
theorem EmptySet_is_empty (T : Type) (s : list T) : ¬(s =~ EmptySet) := by
  sorry

theorem MUnion' (T : Type) (s : list T) (re1 re2 : reg_exp T)
    (h : s =~ re1 ∨ s =~ re2) : s =~ Union re1 re2 := by
  sorry

theorem MStar' (T : Type) (ss : list (list T)) (re : reg_exp T)
    (h : ∀ s, In s ss → s =~ re) : fold app ss nil =~ Star re := by
  sorry
```

### 🎯 练习：`EmptyStr_not_needed` <Badge type="info" text="2 星 · standard, optional" />

```lean
def EmptyStr' {T : Type} : reg_exp T := Star EmptySet

theorem EmptyStr_not_needed (T : Type) (s : list T) :
    s =~ EmptyStr ↔ s =~ EmptyStr' := by
  sorry

/-- 提取正则表达式中出现的所有字符 -/
def re_chars {T : Type} : reg_exp T → list T
  | .EmptySet => nil
  | .EmptyStr => nil
  | .Char x => x :: nil
  | .App re1 re2 => re_chars re1 ++ re_chars re2
  | .Union re1 re2 => re_chars re1 ++ re_chars re2
  | .Star re => re_chars re

theorem in_re_match (T : Type) (s : list T) (re : reg_exp T) (x : T)
    (h : s =~ re) (hin : In x s) : In x (re_chars re) := by
  sorry
```

### 🎯 练习：`re_not_empty` <Badge type="danger" text="4 星 · standard" />

```lean
def re_not_empty {T : Type} : reg_exp T → Bool
  | .EmptySet => false
  | .EmptyStr => true
  | .Char _ => true
  | .App re1 re2 => re_not_empty re1 && re_not_empty re2
  | .Union re1 re2 => re_not_empty re1 || re_not_empty re2
  | .Star _ => true

theorem re_not_empty_correct (T : Type) (re : reg_exp T) :
    (∃ s : list T, s =~ re) ↔ re_not_empty re = true := by
  sorry

/-- Star 构造下的拼接封闭引理（首次受阻尝试） -/
theorem star_app_firsttry {T : Type} (s1 s2 : list T) (re : reg_exp T)
    (h1 : s1 =~ Star re) (h2 : s2 =~ Star re) : s1 ++ s2 =~ Star re := by
  sorry

theorem star_app {T : Type} (s1 s2 : list T) (re : reg_exp T)
    (h1 : s1 =~ Star re) (h2 : s2 =~ Star re) : s1 ++ s2 =~ Star re := by
  sorry
```

### 🎯 练习：`exp_match_ex2` <Badge type="danger" text="4 星 · standard, optional" />

```lean
theorem MStar'' (T : Type) (s : list T) (re : reg_exp T) (h : s =~ Star re) :
    ∃ ss : list (list T), s = fold app ss nil ∧ ∀ s', In s' ss → s' =~ re := by
  sorry

/-- 泵引理常数计算函数 -/
def pumping_constant {T : Type} : reg_exp T → Nat
  | .EmptySet => 1
  | .EmptyStr => 1
  | .Char _ => 2
  | .App re1 re2 => pumping_constant re1 + pumping_constant re2
  | .Union re1 re2 => pumping_constant re1 + pumping_constant re2
  | .Star r => pumping_constant r

theorem pumping_constant_ge_1 (T : Type) (re : reg_exp T) :
    pumping_constant re >= 1 := by
  sorry

theorem pumping_constant_0_false (T : Type) (re : reg_exp T)
    (h : pumping_constant re = 0) : False := by
  sorry

/-- 字符串的 n 次自拼接重复 -/
def napp {T : Type} : Nat → list T → list T
  | 0, _ => nil
  | n' + 1, l => l ++ napp n' l

theorem napp_plus (T : Type) (n m : Nat) (l : list T) :
    napp (n + m) l = napp n l ++ napp m l := by
  sorry

theorem napp_star (T : Type) (m : Nat) (s1 s2 : list T) (re : reg_exp T)
    (hs1 : s1 =~ re) (hs2 : s2 =~ Star re) :
    napp m s1 ++ s2 =~ Star re := by
  sorry
```

### 🎯 练习：`weak_pumping` <Badge type="danger" text="5 星 · advanced" />

```lean
theorem weak_pumping {T : Type} (re : reg_exp T) (s : list T)
    (hm : s =~ re) (hl : pumping_constant re <= length s) :
    ∃ s1 s2 s3 : list T,
      s = s1 ++ s2 ++ s3 ∧
      s2 ≠ nil ∧
      ∀ m : Nat, s1 ++ napp m s2 ++ s3 =~ re := by
  sorry
```

### 🎯 练习：`pumping` <Badge type="danger" text="5 星 · advanced, optional" />

```lean
theorem pumping {T : Type} (re : reg_exp T) (s : list T)
    (hm : s =~ re) (hl : pumping_constant re <= length s) :
    ∃ s1 s2 s3 : list T,
      s = s1 ++ s2 ++ s3 ∧
      s2 ≠ nil ∧
      Playground.le (length s1 + length s2) (pumping_constant re) ∧
      ∀ m : Nat, s1 ++ napp m s2 ++ s3 =~ re := by
  sorry
```

## 5. 案例研究：深化布尔反射 (Case Study: Improving Reflection)

```lean
theorem filter_not_empty_In (n : Nat) (l : list Nat)
    (h : filter (fun x => (n =? x)) l ≠ nil) : In n l := by
  sorry

/-- 反射归纳谓词：将命题证据与布尔判定紧密关联 -/
inductive reflect (P : Prop) : Bool → Prop where
  | ReflectT (h : P) : reflect P true
  | ReflectF (h : ¬P) : reflect P false

theorem iff_reflect (P : Prop) (b : Bool) (h : P ↔ b = true) : reflect P b := by
  cases b with
  | true =>
    apply reflect.ReflectT
    exact h.mpr rfl
  | false =>
    apply reflect.ReflectF
    intro hp
    have hb := h.mp hp
    contradiction
```

### 🎯 练习：`reflect_iff` <Badge type="info" text="2 星 · standard, especially useful" />

```lean
theorem reflect_iff (P : Prop) (b : Bool) (h : reflect P b) : P ↔ b = true := by
  sorry

theorem eqbP (n m : Nat) : reflect (n = m) (n =? m) := by
  apply iff_reflect
  exact (eqb_eq n m).symm

theorem filter_not_empty_In' (n : Nat) (l : list Nat)
    (h : filter (fun x => (n =? x)) l ≠ nil) : In n l := by
  sorry

/-- 计数函数 -/
def count (n : Nat) : list Nat → Nat
  | nil => 0
  | x :: l' => (if (n =? x) then 1 else 0) + count n l'
```

### 🎯 练习：`eqbP_practice` <Badge type="warning" text="3 星 · standard, especially useful" />

```lean
theorem eqbP_practice (n : Nat) (l : list Nat) (h : count n l = 0) : ¬(In n l) := by
  sorry
```

## 6. 进阶综合练习 (Additional Exercises)

### 🎯 练习：`nostutter_defn` <Badge type="warning" text="3 星 · standard, especially useful" />

```lean
/-- 无连续重复项（非停滞）列表谓词 -/
inductive nostutter {X : Type} : list X → Prop where
  | nostutter_nil : nostutter nil
  | nostutter_one (x : X) : nostutter [x]
  | nostutter_cons (x y : X) (l : list X) (h1 : x ≠ y) (h2 : nostutter (y :: l)) :
      nostutter (x :: y :: l)

theorem test_nostutter_1 : nostutter [3; 1; 4; 1; 5; 6] := by
  sorry

theorem test_nostutter_2 : nostutter (@nil Nat) := by
  sorry

theorem test_nostutter_3 : nostutter [5] := by
  sorry

theorem test_nostutter_4 : ¬(nostutter [3; 1; 1; 4]) := by
  sorry

def manual_grade_for_nostutter : Option (Nat × String) := none
```

### 🎯 练习：`filter_challenge` <Badge type="danger" text="4 星 · advanced" />

```lean
/-- 两个列表归并交错生成第三个列表的归纳关系 -/
inductive merge {X : Type} : list X → list X → list X → Prop where
  | merge_nil : merge nil nil nil
  | merge_l (x : X) (l1 l2 l : list X) (h : merge l1 l2 l) : merge (x :: l1) l2 (x :: l)
  | merge_r (y : X) (l1 l2 l : list X) (h : merge l1 l2 l) : merge l1 (y :: l2) (y :: l)

theorem merge_filter (X : Type) (test : X → Bool) (l l1 l2 : list X)
    (hm : merge l1 l2 l)
    (h1 : All (fun n => test n = true) l1)
    (h2 : All (fun n => test n = false) l2) :
    filter test l = l1 := by
  sorry
```

### 🎯 练习：`filter_challenge_2` <Badge type="danger" text="5 星 · advanced, optional" />

```lean
theorem subs_filter (test : Nat → Bool) (l1 l2 : list Nat)
    (hsub : subseq l1 l2)
    (hall : All (fun x => test x = true) l1) :
    Playground.le (length l1) (length (filter test l2)) := by
  sorry
```

### 🎯 练习：`palindromes` <Badge type="danger" text="4 星 · standard, optional" />

```lean
/-- 回文列表归纳谓词 -/
inductive pal {X : Type} : list X → Prop where
  | pal_nil : pal nil
  | pal_one (x : X) : pal [x]
  | pal_cons (x : X) (l : list X) (h : pal l) : pal (x :: l ++ [x])

theorem pal_app_rev (X : Type) (l : list X) : pal (l ++ rev l) := by
  sorry

theorem pal_rev (X : Type) (l : list X) (h : pal l) : l = rev l := by
  sorry
```

### 🎯 练习：`palindrome_converse` <Badge type="danger" text="5 星 · standard, optional" />

```lean
theorem palindrome_converse {X : Type} (l : list X) (h : l = rev l) : pal l := by
  sorry
```

### 🎯 练习：`NoDup` <Badge type="danger" text="4 星 · advanced, optional" />

```lean
/-- 两个列表无交集 -/
inductive disjoint {X : Type} : list X → list X → Prop where
  | disjoint0 (l2 : list X) : disjoint nil l2
  | disjoint1 (x : X) (l1 l2 : list X) (h1 : ¬In x l2) (h2 : disjoint l1 l2) :
      disjoint (x :: l1) l2

/-- 列表中无任何重复元素 -/
inductive NoDup {X : Type} : list X → Prop where
  | NoDup0 : NoDup nil
  | NoDup1 (x : X) (l : list X) (h1 : ¬In x l) (h2 : NoDup l) :
      NoDup (x :: l)

theorem disjoint_NoDup_app (X : Type) (l1 l2 : list X)
    (h1 : NoDup l1) (h2 : NoDup l2) (hd : disjoint l1 l2) :
    NoDup (l1 ++ l2) := by
  sorry

theorem NoDup_app (X : Type) (l1 l2 : list X) (h : NoDup (l1 ++ l2)) :
    NoDup l1 ∧ NoDup l2 := by
  sorry

theorem NoDup_app_disjoint (X : Type) (l1 l2 : list X) (h : NoDup (l1 ++ l2)) :
    disjoint l1 l2 := by
  sorry

def manual_grade_for_NoDup_disjoint_etc : Option (Nat × String) := none
```

### 🎯 练习：`pigeonhole_principle` <Badge type="danger" text="4 星 · advanced, optional" />

```lean
theorem in_split (X : Type) (x : X) (l : list X) (h : In x l) :
    ∃ l1 l2 : list X, l = l1 ++ x :: l2 := by
  sorry

/-- 列表包含重复元素归纳谓词 -/
inductive repeats {X : Type} : list X → Prop where
  | repeats_trans (x : X) (l : list X) (h : In x l) : repeats (x :: l)
  | repeats_more (x : X) (l : list X) (h : repeats l) : repeats (x :: l)

def manual_grade_for_check_repeats : Option (Nat × String) := none

/-- 鸽巢原理（结合排中律公理） -/
theorem pigeonhole_principle (hem : excluded_middle) (X : Type) (l1 l2 : list X)
    (hin : ∀ x, In x l1 → In x l2)
    (hlen : Playground.lt (length l2) (length l1)) :
    repeats l1 := by
  sorry
```

## 7. 扩展案例：可验证的正则表达式匹配器 (Extended Exercise: A Verified Regular-Expression Matcher)

```lean
abbrev ascii := _root_.Char

def string := list ascii

theorem provable_equiv_true (P : Prop) (h : P) : (P ↔ True) := by
  constructor
  · intro _; trivial
  · intro _; exact h

theorem not_equiv_false (P : Prop) (h : ¬P) : (P ↔ False) := by
  constructor
  · intro hp; exact h hp
  · intro contra; cases contra

theorem null_matches_none (s : string) : (s =~ EmptySet) ↔ False := by
  constructor
  · intro h; cases h
  · intro contra; cases contra

theorem empty_matches_eps (s : string) : (s =~ EmptyStr) ↔ s = nil := by
  constructor
  · intro h
    generalize hr : (EmptyStr : reg_exp ascii) = re at h
    cases h
    all_goals cases hr
    rfl
  · intro h; rw [h]; exact MEmpty

theorem empty_nomatch_ne (a : ascii) (s : string) : (a :: s =~ EmptyStr) ↔ False := by
  constructor
  · intro h
    generalize hs : a :: s = s' at h
    generalize hr : (EmptyStr : reg_exp ascii) = re at h
    cases h
    all_goals cases hr
    cases hs
  · intro contra; cases contra

theorem char_nomatch_char (a b : ascii) (s : string) (hne : b ≠ a) :
    (b :: s =~ reg_exp.Char a) ↔ False := by
  constructor
  · intro h
    generalize hs : b :: s = s' at h
    generalize hr : (reg_exp.Char a : reg_exp ascii) = re at h
    cases h
    all_goals cases hr
    injection hs with hb _
    exact hne hb
  · intro contra; cases contra

theorem char_eps_suffix (a : ascii) (s : string) : (a :: s =~ reg_exp.Char a) ↔ s = nil := by
  constructor
  · intro h
    generalize hs : a :: s = s' at h
    generalize hr : (reg_exp.Char a : reg_exp ascii) = re at h
    cases h
    all_goals cases hr
    injection hs
  · intro h
    rw [h]
    exact MChar a

theorem app_exists (s : string) (re0 re1 : reg_exp ascii) :
    (s =~ App re0 re1) ↔ ∃ s0 s1 : string, s = s0 ++ s1 ∧ s0 =~ re0 ∧ s1 =~ re1 := by
  constructor
  · intro h
    generalize hr : (App re0 re1 : reg_exp ascii) = re at h
    cases h
    all_goals cases hr
    exact ⟨_, _, rfl, by assumption, by assumption⟩
  · intro ⟨s0, s1, heq, h1, h2⟩
    rw [heq]
    exact MApp s0 re0 s1 re1 h1 h2
```

### 🎯 练习：`app_ne` <Badge type="warning" text="3 星 · standard, optional" />

```lean
theorem app_ne (a : ascii) (s : string) (re0 re1 : reg_exp ascii) :
    (a :: s =~ App re0 re1) ↔
      ((nil =~ re0 ∧ a :: s =~ re1) ∨
       ∃ s0 s1, s = s0 ++ s1 ∧ a :: s0 =~ re0 ∧ s1 =~ re1) := by
  sorry

theorem union_disj (s : string) (re0 re1 : reg_exp ascii) :
    (s =~ Union re0 re1) ↔ (s =~ re0 ∨ s =~ re1) := by
  constructor
  · intro h
    generalize hr : (Union re0 re1 : reg_exp ascii) = re at h
    cases h
    all_goals cases hr
    · exact Or.inl (by assumption)
    · exact Or.inr (by assumption)
  · intro
    | Or.inl h1 => exact MUnionL s re0 re1 h1
    | Or.inr h2 => exact MUnionR s re0 re1 h2
```

### 🎯 练习：`star_ne` <Badge type="warning" text="3 星 · standard, optional" />

```lean
theorem star_ne (a : ascii) (s : string) (re : reg_exp ascii) :
    (a :: s =~ Star re) ↔
      ∃ s0 s1, s = s0 ++ s1 ∧ a :: s0 =~ re ∧ s1 =~ Star re := by
  sorry

def refl_matches_eps (m : reg_exp ascii → Bool) : Prop :=
  ∀ re : reg_exp ascii, reflect (nil =~ re) (m re)
```

### 🎯 练习：`match_eps` <Badge type="info" text="2 星 · standard, optional" />

```lean
def match_eps : reg_exp ascii → Bool
  | .EmptySet => false
  | .EmptyStr => true
  | .Char _ => false
  | .App re1 re2 => match_eps re1 && match_eps re2
  | .Union re1 re2 => match_eps re1 || match_eps re2
  | .Star _ => true
```

### 🎯 练习：`match_eps_refl` <Badge type="warning" text="3 星 · standard, optional" />

```lean
theorem match_eps_refl : refl_matches_eps match_eps := by
  sorry

def is_der (re : reg_exp ascii) (a : ascii) (re' : reg_exp ascii) : Prop :=
  ∀ s : string, (a :: s =~ re) ↔ s =~ re'

def derives (d : ascii → reg_exp ascii → reg_exp ascii) : Prop :=
  ∀ a re, is_der re a (d a re)
```

### 🎯 练习：`derive` <Badge type="warning" text="3 星 · standard, optional" />

```lean
def derive (a : ascii) : reg_exp ascii → reg_exp ascii
  | .EmptySet => .EmptySet
  | .EmptyStr => .EmptySet
  | .Char x => if x == a then .EmptyStr else .EmptySet
  | .App re1 re2 =>
    if match_eps re1 then .Union (derive a re2) (.App (derive a re1) re2)
    else .App (derive a re1) re2
  | .Union re1 re2 => .Union (derive a re1) (derive a re2)
  | .Star re => .App (derive a re) (.Star re)

def c : ascii := 'c'
def d : ascii := 'd'

theorem test_der0 : match_eps (derive c .EmptySet) = false := by rfl
theorem test_der1 : match_eps (derive c (.Char c)) = true := by rfl
theorem test_der2 : match_eps (derive c (.Char d)) = false := by rfl
theorem test_der3 : match_eps (derive c (.App (.Char c) .EmptyStr)) = true := by rfl
theorem test_der4 : match_eps (derive c (.App .EmptyStr (.Char c))) = true := by rfl
theorem test_der5 : match_eps (derive c (.Star (.Char c))) = true := by rfl
theorem test_der6 : match_eps (derive d (derive c (.App (.Char c) (.Char d)))) = true := by rfl
theorem test_der7 : match_eps (derive d (derive c (.App (.Char d) (.Char c)))) = false := by rfl
```

### 🎯 练习：`derive_corr` <Badge type="danger" text="4 星 · standard, optional" />

```lean
theorem derive_corr : derives derive := by
  sorry

def matches_regex (m : string → reg_exp ascii → Bool) : Prop :=
  ∀ (s : string) (re : reg_exp ascii), reflect (s =~ re) (m s re)
```

### 🎯 练习：`regex_match` <Badge type="info" text="2 星 · standard, optional" />

```lean
def regex_match : string → reg_exp ascii → Bool
  | nil, re => match_eps re
  | a :: s', re => regex_match s' (derive a re)
```

### 🎯 练习：`regex_match_correct` <Badge type="warning" text="3 星 · standard, optional" />

```lean
theorem regex_match_correct : matches_regex regex_match := by
  sorry

end IndProp
```
