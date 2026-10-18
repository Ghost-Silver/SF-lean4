---
title: "Tactics: 策略进阶：反演、代换与泛化归纳"
---

```lean
import SFLean4.LF.Basics
import SFLean4.LF.Induction
import SFLean4.LF.Lists
import SFLean4.LF.Poly
```

# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)

## 第五章：证明策略进阶 (Tactics: More Basic Tactics)

在前几章中，我们已经接触了最基本的证明手段：
- 用于自反性化简的 `rfl`；
- 用于全称量词与前件引入的 `intro`；
- 用于等式替换的 `rw`（重写）；
- 用于分类讨论的 `cases` 以及用于结构归纳的 `induction`。

然而，随着我们所要验证的函数式程序与性质日益复杂，仅凭这些初级工具往往会捉襟见肘。
本章将系统介绍形式化证明中一系列极为重要的**进阶策略**与证明范式：
1. **后向与前向推理 (Backward vs Forward Reasoning)**：
   - 深入理解 `apply` 及其在假设上的应用（`apply ... at ...`），学会在目标与上下文之间双向传导；
   - 掌握通过显式具现化参数（`apply ... with` / `specialize`）解决无法由模式匹配直接推断的引理；
2. **归纳构造子的代数本质**：
   - **单射性 (Injectivity)**：同名构造子所包含的字段相等，即 $C(x) = C(y) \implies x = y$（`injection`）；
   - **不相交性 (Disjointness)**：不同构造子绝不可能相等，即 $C_1(\dots) = C_2(\dots) \implies \text{False}$（`contradiction` / 爆炸原理）；
3. **强化归纳假设 (Strengthening the Induction Hypothesis)**：
   - 深刻理解何时不能过早 `intro` 变量，学会在归纳前利用 `revert` 将特定变量重新泛化回目标，以获得足够通用的归纳假设；
4. **复合表达式上的分支推理**：
   - 学习在非变量的复杂计算表达式上进行情况分析（`split` / `cases`），并保留分支等式信息。

```lean
namespace Tactics

open Poly
open Poly.list
open Poly.prod
open Poly.option

/- ================================================================== -/
```

## 1. `apply` 策略 (The `apply` Tactic)

```lean
/- ================================================================== -/
```

### 1.1 `apply` 的基础用法

在交互式证明中，我们经常会遇到待证明的目标与上下文中的某个前提假设（或者先前已经获证的全局定理）**完全一致**的情形。

```lean
/-- 最简单的情形：目标与已知假设完全相同 -/
theorem silly1 (n m : Nat) (eq : n = m) : n = m := by
  -- 此处我们固然可以使用 `rw [eq]`，但也可以直接使用 `apply`
  apply eq
```

`apply` 策略不仅能用于直接闭合目标，还可以用于**蕴含（条件）前提**：
如果待应用的引理或假设是一个蕴含式 `P → Q`，且当前证明目标恰好能与结论 `Q` 统一匹配，
那么 `apply` 会将目标转化为必须首先证明其前件 `P`：

```lean
/-- apply 用于条件假设：后向归约 -/
theorem silly2 (n m o p : Nat)
    (eq1 : n = m)
    (eq2 : n = m → [n; o] = [m; p]) :
    [n; o] = [m; p] := by
  apply eq2
  apply eq1
```

通常情况下，待应用的定理往往以全称量词 `∀` 开头。
当将定理的结论与当前目标进行模式匹配时，类型推导引擎会自动解出这些被全称量化的变量：

```lean
/-- 全称量化引理的自动模式匹配实例化 -/
theorem silly2a (n m : Nat)
    (eq1 : (n, n)ₚ = (m, m)ₚ)
    (eq2 : ∀ (q r : Nat), (q, q)ₚ = (r, r)ₚ → (q :: nil) = (r :: nil)) :
    (n :: nil) = (m :: nil) := by
  apply eq2
  apply eq1
```

### 🎯 练习：`silly_ex` <Badge type="info" text="2 星 · standard, optional" />

仅使用 `intro` 和 `apply` 完成下列证明：

```lean
theorem silly_ex (p : Nat)
    (eq1 : ∀ n, even n = true → even (n + 1) = false)
    (eq2 : ∀ n, even n = false → odd n = true)
    (eq3 : even p = true) :
    odd (p + 1) = true := by
  sorry
```

需要特别注意的是：要成功使用 `apply`，结论项必须与当前目标严格匹配。
例如，如果等式左右两侧恰好颠倒，直接 `apply` 将会报错。
在 Lean 4 中，我们可以使用 `symm` 策略翻转目标等式的左右两侧：

```lean
/-- 对称性与 apply 的配合使用 -/
theorem silly3 (n m : Nat) (H : n = m) : m = n := by
  -- 尝试直接 apply H 将会失败，因为 m = n 与 n = m 左右颠倒
  symm
  apply H
```

### 🎯 练习：`apply_exercise1` <Badge type="info" text="2 星 · standard" />

结合我们在上一章证明的列表翻转对合律 `rev_involutive`，使用 `apply` 完成下列证明（无需归纳法）：

```lean
theorem rev_exercise1 (l l' : list Nat)
    (eq : l = rev l') :
    l' = rev l := by
  sorry
```

### 🎯 练习：`apply_rewrite` <Badge type="tip" text="1 星 · standard, optional" />

简要阐述策略 `apply` 与 `rw`（重写）的核心区别，以及它们各自的适用场景：
1. `rw`（重写）：基于等式假设 $a = b$，将目标或上下文中的子项 $a$ 替换为 $b$；它作用于目标内部的任意子表达式，且不改变目标的逻辑外壳。
2. `apply`（后向归约）：基于蕴含关系 $P \implies Q$ 或全称命题 $\forall x, P(x) \implies Q(x)$，将当前与 $Q$ 匹配的目标替换为前件子目标 $P$；如果应用于无前件的假设，则直接完成证明。

```lean
/- ================================================================== -/
```

## 2. `apply ... with ...` 与中介变量指定

```lean
/- ================================================================== -/
```

考虑等式的传递性定理：如果 $n = m$ 且 $m = o$，那么 $n = o$。

```lean
/-- 等式的传递性定理 -/
theorem trans_eq {X : Type} {n m o : X} (eq1 : n = m) (eq2 : m = o) : n = o := by
  rw [eq1, eq2]

/-- 使用连续重写证明示例 -/
theorem trans_eq_example (a b c d e f : Nat)
    (eq1 : [a; b] = [c; d])
    (eq2 : [c; d] = [e; f]) :
    [a; b] = [e; f] := by
  rw [eq1, eq2]
```

若我们希望通过 `apply trans_eq` 来证明上述例子：
编译器将目标 `[a; b] = [e; f]` 与定理结论 `n = o` 统一匹配，
可以顺利得出 $n = [a; b]$ 且 $o = [e; f]$，但**中间变量 $m$ 无法从目标结论中获知**！
在 Lean 4 中，我们可以显式为该具名参数指定实参：`apply trans_eq (m := [c; d])`：

```lean
/-- 显式指定传递性中间项 -/
theorem trans_eq_example' (a b c d e f : Nat)
    (eq1 : [a; b] = [c; d])
    (eq2 : [c; d] = [e; f]) :
    [a; b] = [e; f] := by
  apply trans_eq (m := [c; d])
  · apply eq1
  · apply eq2

/-- 也可以利用 Lean 4 原生传递性定理 Eq.trans -/
theorem trans_eq_example'' (a b c d e f : Nat)
    (eq1 : [a; b] = [c; d])
    (eq2 : [c; d] = [e; f]) :
    [a; b] = [e; f] := by
  apply Eq.trans (b := [c; d])
  · apply eq1
  · apply eq2
```

### 🎯 练习：`trans_eq_exercise` <Badge type="warning" text="3 星 · standard, optional" />

```lean
theorem trans_eq_exercise (n m o p : Nat)
    (eq1 : m = minustwo o)
    (eq2 : n + p = m) :
    n + p = minustwo o := by
  sorry

/- ================================================================== -/
```

## 3. 构造子的单射性与不相交性 (Injection and Disjointness)

```lean
/- ================================================================== -/
```

在代数数据类型（`inductive`）的定义中，潜藏着两项最基础也最重要的公理化法则：
1. **构造子的单射性 (Injectivity)**：
   同名构造子是单射的。例如对自然数后继构造子，若 `n + 1 = m + 1`，则必然有 `n = m`；
   对列表构造子，若 `x :: l1 = y :: l2`，则必然有 `x = y` 且 `l1 = l2`。
2. **构造子的不相交性 (Disjointness)**：
   不同构造子构造出的值绝不可能相等。例如 `0` 绝不等于任意 `n + 1`，空列表 `nil` 绝不等于非空列表 `x :: l`。

```lean
/-- 通过逆运算 pred 证明自然数后继构造子的单射性 -/
theorem S_injective (n m : Nat) (H1 : n + 1 = m + 1) : n = m := by
  have H2 : n = Nat.pred (n + 1) := rfl
  rw [H2, H1]
  rfl
```

在 Lean 4 中，我们可以直接使用 `injection` 策略利用构造子单射性分解等式：

```lean
/-- 使用 injection 策略自动解构构造子单射性 -/
theorem S_injective' (n m : Nat) (H : n + 1 = m + 1) : n = m := by
  injection H

/-- 从列表等式中一次性提取出多个分量的单射等式 -/
theorem injection_ex1 (n m o : Nat) (H : [n; m] = [o; o]) : n = m := by
  injection H with h1 h2
  injection h2 with h3
  rw [h1, h3]
```

### 🎯 练习：`injection_ex3` <Badge type="warning" text="3 星 · standard" />

```lean
theorem injection_ex3 (X : Type) (x y z : X) (l j : list X)
    (eq1 : x :: y :: l = z :: j)
    (eq2 : j = z :: l) :
    x = y := by
  sorry
```

### 3.1 构造子的不相交性与爆炸原理 (Disjointness & Principle of Explosion)

不相交性指出：不同构造子绝无可能相等。
若我们在前提中假设了 `false = true` 或 `0 = n + 1`，则意味着处于一个荒谬的矛盾上下文中。
在经典逻辑与构造逻辑中，**矛盾蕴含万物**（*ex falso quodlibet*，即爆炸原理）。
在 Lean 4 中，`contradiction` 策略（或直接对矛盾等式执行 `cases`）会自动识别构造子不相交性并立即消除目标：

```lean
/-- 布尔构造子不相交性与爆炸原理 -/
theorem discriminate_ex1 (n m : Nat) (contra : false = true) : n = m := by
  contradiction

/-- 自然数零与后继不相交 -/
theorem discriminate_ex2 (n : Nat) (contra : n + 1 = 0) : 2 + 2 = 5 := by
  contradiction
```

### 🎯 练习：`discriminate_ex3` <Badge type="tip" text="1 星 · standard" />

```lean
theorem discriminate_ex3 (X : Type) (x y z : X) (l j : list X)
    (contra : x :: y :: l = nil) :
    x = z := by
  sorry

/-- 连接布尔等式测试 =? 与逻辑等式 = -/
theorem eqb_0_l (n : Nat) (H : (0 =? n) = true) : n = 0 := by
  cases n with
  | zero => rfl
  | succ n' =>
    -- 此时 0 =? (n' + 1) 化简为 false，与 H 产生矛盾 false = true
    contradiction
```

### 3.2 函数相等的同余性：`f_equal` 与 `congr`

若两个输入项相等 $x = y$，则任意纯函数作用其上的结果必然相等 $f(x) = f(y)$：

```lean
/-- 函数应用的同余性引理 -/
theorem f_equal {A B : Type} (f : A → B) (x y : A) (eq : x = y) : f x = f y := by
  rw [eq]

/-- 构造子同余性应用 -/
theorem eq_implies_succ_equal (n m : Nat) (H : n = m) : n + 1 = m + 1 := by
  apply f_equal (fun x => x + 1)
  apply H

/-- 使用现代 Lean 4 的同余策略 congr -/
theorem eq_implies_succ_equal' (n m : Nat) (H : n = m) : n + 1 = m + 1 := by
  congr

/- ================================================================== -/
```

## 4. 在假设上运用策略与前向推理 (Tactics on Hypotheses)

```lean
/- ================================================================== -/
```

默认情况下，绝大多数策略（如 `rw`、`dsimp`）均作用于目标公式。
但在实际证明中，我们也经常需要直接对上下文中的假设进行操作（例如在假设中展开或化简）：
在 Lean 4 中，只需使用 `at H` 子句即可（对应 Coq 中的 `in H`）。

```lean
/-- 对假设进行化简 -/
theorem S_inj (n m : Nat) (b : Bool) (H : (((n + 1) =? (m + 1)) = b)) : (n =? m) = b := by
  dsimp [eqb] at H
  exact H

/-- 前向推理演示：从已知出发逐步推导直至闭合 -/
theorem silly4 (n m p q : Nat)
    (EQ : n = m → p = q)
    (H : m = n) :
    q = p := by
  have H' : n = m := H.symm
  have H'' : p = q := EQ H'
  exact H''.symm

/- ================================================================== -/
```

## 5. 具现化量化假设 (Specializing Hypotheses)

```lean
/- ================================================================== -/
```

当上下文包含一个全称量化假设 `H : ∀ x : T, P x` 时，
我们有时希望将其具体化到某个特定项 `e` 上，即把 `H` 具现化为 `P e`。
在 Lean 4 中，这可以直接通过 `specialize H e` 完成：

```lean
theorem specialize_example (n : Nat) (H : ∀ m, m * n = 0) : n = 0 := by
  specialize H 1
  rw [Nat.one_mul] at H
  exact H

/-- 通过对全局传递性引理进行具现化完成证明 -/
theorem trans_eq_example''' (a b c d e f : Nat)
    (eq1 : [a; b] = [c; d])
    (eq2 : [c; d] = [e; f]) :
    [a; b] = [e; f] := by
  have H := @trans_eq (list Nat) [a; b] [c; d] [e; f]
  apply H
  · exact eq1
  · exact eq2

/- ================================================================== -/
```

## 6. 强化归纳假设与变量泛化 (Varying the Induction Hypothesis)

```lean
/- ================================================================== -/
```

进行归纳证明时，**归纳假设的形式是否足够强**往往直接决定了证明的成败。
特别是在证明涉及多个全称量化变量的定理时，过早使用 `intro` 将全部变量引入局部上下文，
会导致归纳假设绑定在一个*固定的局部特定值*上，从而无法在归纳步中应用！

考虑证明翻倍函数 `double` 是单射的：

```lean
/-- 过早引入变量导致归纳假设过于脆弱的失败尝试 -/
theorem double_injective_FAILED (n m : Nat) (h : double n = double m) : n = m := by
  -- 若在此处直接对 n 归纳，m 会被冻结为某个固定常数，
  -- 导致归纳假设仅能给出 double n' = double m → n' = m，无法应对 double m' 的变化。
  sorry

/-- 正确做法：归纳时保持第二个变量处于全称量化泛化状态 -/
theorem double_injective (n m : Nat) (h : double n = double m) : n = m := by
  revert m
  induction n with
  | zero =>
    intro m eq
    cases m with
    | zero => rfl
    | succ m' => contradiction
  | succ n' ih =>
    intro m eq
    cases m with
    | zero => contradiction
    | succ m' =>
      congr
      apply ih
      have : double n' = double m' := by
        dsimp [double] at eq
        omega
      exact this
```

### 🎯 练习：`eqb_true` <Badge type="info" text="2 星 · standard" />

证明自然数布尔相等判定为 true 蕴含它们命题逻辑相等：

```lean
theorem eqb_true (n m : Nat) (h : (n =? m) = true) : n = m := by
  sorry
```

### 🎯 练习：`eqb_true_informal` <Badge type="info" text="2 星 · advanced" />

请给出 `eqb_true` 的严谨非形式化数学证明，显式注明归纳假设及量词作用域：

【数学证明整理如下】：
- 对自然数 `n` 进行数学归纳。证明目标为：对任意自然数 `m`，若 `(n =? m) = true`，则 `n = m`。
  1. **基底情况**：`n = 0`。
     设 `m` 为任意自然数，假设 `(0 =? m) = true`。
     对 `m` 进行情况分析：
     - 若 `m = 0`，则显然 $n = 0 = m$，结论成立；
     - 若 `m = m' + 1`，根据 `eqb` 的定义可知 `(0 =? m' + 1) = false`，这与假设为 `true` 矛盾。
     基底获证。
  2. **归纳步**：设 `n = n' + 1`，归纳假设为：
     对于任意自然数 `m`，若 `(n' =? m) = true`，则 `n' = m`。
     现在设 `m` 为任意自然数，并假设 `(n' + 1 =? m) = true`。
     对 `m` 进行情况分析：
     - 若 `m = 0`，由定义 `(n' + 1 =? 0) = false`，产生矛盾；
     - 若 `m = m' + 1`，由 `eqb` 的递推定义可知 `(n' + 1 =? m' + 1) = (n' =? m')`。
       故假设化为 `(n' =? m') = true`。
       此时将归纳假设实例化到 `m'`，立即得到 `n' = m'`。
       两边同加 1 即得 `n' + 1 = m' + 1`，即 `n = m`。
     归纳步获证。
  综上，定理对所有自然数 $n, m$ 均成立。证毕。

```lean
/-- 非形式化证明评分标记（请勿修改） -/
def manual_grade_for_informal_proof : Option (Nat × String) := none
```

### 🎯 练习：`plus_n_n_injective` <Badge type="warning" text="3 星 · standard, especially useful" />

证明自然数自身相加运算是单射的：

```lean
theorem plus_n_n_injective (n m : Nat) (h : n + n = m + m) : n = m := by
  sorry
```

### 6.1 使用 `revert` 重新泛化变量

若变量已经被引入了上下文，但我们希望对另一个后声明的变量进行归纳，
可以通过 `revert` 将其重新推回证明目标的结论前面：

```lean
/-- 试图直接在 m 上归纳导致失败的尝试（未泛化 n） -/
theorem double_injective_take2_FAILED (n m : Nat) (h : double n = double m) : n = m := by
  sorry

/-- 对 m 进行归纳前首先 revert n -/
theorem double_injective_take2 (n m : Nat) (h : double n = double m) : n = m := by
  revert n
  induction m with
  | zero =>
    intro n eq
    cases n with
    | zero => rfl
    | succ n' => contradiction
  | succ m' ih =>
    intro n eq
    cases n with
    | zero => contradiction
    | succ n' =>
      congr
      apply ih
      have : double n' = double m' := by
        dsimp [double] at eq
        omega
      exact this
```

### 🎯 练习：`gen_dep_practice` <Badge type="warning" text="3 星 · standard, especially useful" />

在归纳前对索引变量 `n` 进行 `revert` 泛化：

```lean
theorem nth_error_after_last (n : Nat) (X : Type) (l : list X)
    (h : length l = n) :
    nth_error l n = None := by
  sorry

/- ================================================================== -/
```

## 7. 展开定义 (Unfolding Definitions)

```lean
/- ================================================================== -/
```

有时某些定理的证明需要我们显式展开（Unfold）函数的定义，以暴露出其底层的运算结构。
在 Lean 4 中，我们可以使用 `dsimp [def_name]` 或 `unfold def_name`：

```lean
/-- 平方定义 -/
def square (n : Nat) : Nat := n * n

/-- 平方关于乘法的分配律 -/
theorem square_mult (n m : Nat) : square (n * m) = square n * square m := by
  dsimp [square]
  rw [Nat.mul_assoc n m (n * m)]
  rw [← Nat.mul_assoc m n m]
  rw [Nat.mul_comm m n]
  rw [Nat.mul_assoc n m m]
  rw [← Nat.mul_assoc n n (m * m)]

def foo (_x : Nat) := 5

theorem silly_fact_1 (m : Nat) : foo m + 1 = foo (m + 1) + 1 := by
  rfl

def bar (x : Nat) : Nat :=
  match x with
  | 0 => 5
  | _ + 1 => 5

theorem silly_fact_2 (m : Nat) : bar m + 1 = bar (m + 1) + 1 := by
  cases m <;> rfl

theorem silly_fact_2' (m : Nat) : bar m + 1 = bar (m + 1) + 1 := by
  unfold bar
  cases m <;> rfl

/- ================================================================== -/
```

## 8. 在复合表达式上进行分支推理 (`split` / `cases`)

```lean
/- ================================================================== -/
```

我们不仅能对单个变量进行 `cases` 分类讨论，还可以对**任意复杂的复合条件表达式**进行分类讨论。
在 Lean 4 中，针对 `if ... then ... else ...` 结构，专用的 `split` 策略能够自动寻找并分离所有分支：

```lean
def sillyfun (n : Nat) : Bool :=
  if n == 3 then false
  else if n == 5 then false
  else false

theorem sillyfun_false (n : Nat) : sillyfun n = false := by
  dsimp [sillyfun]
  split <;> try rfl
  split <;> rfl
```

### 🎯 练习：`combine_split` <Badge type="warning" text="3 星 · standard" />

证明上一章中定义的列表拆分函数与组合函数互为逆操作：

```lean
theorem combine_split (X Y : Type) (l : list (X *ₚ Y)) (l1 : list X) (l2 : list Y)
    (h : split l = (l1, l2)ₚ) :
    combine l1 l2 = l := by
  sorry

def sillyfun1 (n : Nat) : Bool :=
  if n == 3 then true
  else if n == 5 then true
  else false

/-- 分支讨论时遗失等式信息导致卡住的失败尝试 -/
theorem sillyfun1_odd_FAILED (n : Nat) (eq : sillyfun1 n = true) : odd n = true := by
  sorry

theorem sillyfun1_odd (n : Nat) (eq : sillyfun1 n = true) : odd n = true := by
  dsimp [sillyfun1] at eq
  split at eq
  · next h =>
    have : n = 3 := by
      cases h_eq : n == 3
      · rw [h_eq] at h; contradiction
      · exact Nat.eq_of_beq_eq_true h_eq
    rw [this]; rfl
  · next h =>
    split at eq
    · next h2 =>
      have : n = 5 := by
        cases h_eq : n == 5
        · rw [h_eq] at h2; contradiction
        · exact Nat.eq_of_beq_eq_true h_eq
      rw [this]; rfl
    · contradiction
```

### 🎯 练习：`destruct_eqn_practice` <Badge type="info" text="2 星 · standard" />

证明任何布尔函数自身作用三次的结果恒等于作用一次的结果：

```lean
theorem bool_fn_applied_thrice (f : Bool → Bool) (b : Bool) :
    f (f (f b)) = f b := by
  sorry

/- ================================================================== -/
```

## 9. 附加习题 (Additional Exercises)

```lean
/- ================================================================== -/
```

### 🎯 练习：`eqb_sym` <Badge type="warning" text="3 星 · standard" />

证明自然数布尔判等运算的对称性：

```lean
theorem eqb_sym (n m : Nat) : (n =? m) = (m =? n) := by
  sorry
```

### 🎯 练习：`eqb_sym_informal` <Badge type="warning" text="3 星 · advanced, optional" />

请给出 `eqb_sym` 的非形式化数学证明：

【证明要点整理】：
对自然数 $n$ 施加数学归纳法：
- 基底：$n = 0$。任取 $m$，若 $m = 0$，两边均为 $0 =? 0 \implies \text{true}$；若 $m = m' + 1$，左边为 $0 =? m' + 1 \implies \text{false}$，右边为 $m' + 1 =? 0 \implies \text{false}$，两边相等。
- 归纳步：设对 $n'$ 定理对所有 $m$ 均成立。现考虑 $n = n' + 1$。
  - 若 $m = 0$：两边均为 false，显然相等；
  - 若 $m = m' + 1$：左边 $(n' + 1 =? m' + 1) = (n' =? m')$，右边 $(m' + 1 =? n' + 1) = (m' =? n')$。
    由归纳假设 $(n' =? m') = (m' =? n')$，两边相等。
证毕。

### 🎯 练习：`eqb_trans` <Badge type="warning" text="3 星 · standard, optional" />

证明自然数布尔判等的传递性：

```lean
theorem eqb_trans (n m p : Nat)
    (h1 : (n =? m) = true)
    (h2 : (m =? p) = true) :
    (n =? p) = true := by
  sorry
```

### 🎯 练习：`split_combine` <Badge type="warning" text="3 星 · advanced" />

```lean
/-- 形式化命题声明：两列表等长时，split 是 combine 的逆映射 -/
def split_combine_statement : Prop :=
  ∀ (X Y : Type) (l1 : list X) (l2 : list Y),
    length l1 = length l2 → split (combine l1 l2) = (l1, l2)ₚ

theorem split_combine : split_combine_statement := by
  sorry

/-- 评分占位项（请勿修改） -/
def manual_grade_for_split_combine : Option (Nat × String) := none
```

### 🎯 练习：`filter_exercise` <Badge type="warning" text="3 星 · advanced" />

证明：若经过过滤后的列表首元素为 `x`，则谓词作用在 `x` 上必定产生 `true`。

```lean
theorem filter_exercise (X : Type) (test : X → Bool)
    (x : X) (l lf : list X)
    (h : filter test l = x :: lf) :
    test x = true := by
  sorry
```

### 🎯 练习：`forall_exists_challenge` <Badge type="danger" text="4 星 · advanced, especially useful" />

请完成布尔全称测试函数 `forallb` 与存在测试函数 `existsb` 的定义，
并用 `forallb` 与布尔非运算定义非递归版本的 `existsb'`，最后证明两者的行为等价。

```lean
/-- 检验列表中所有元素是否均满足谓词 -/
def forallb {X : Type} (test : X → Bool) : list X → Bool :=
  sorry

theorem test_forallb_1 : forallb odd [1; 3; 5; 7; 9] = true := by
  sorry

theorem test_forallb_2 : forallb negb [false; false] = true := by
  sorry

theorem test_forallb_3 : forallb even [0; 2; 4; 5] = false := by
  sorry

theorem test_forallb_4 : forallb (fun x => x =? 5) nil = true := by
  sorry

/-- 检验列表中是否存在至少一个元素满足谓词 -/
def existsb {X : Type} (test : X → Bool) : list X → Bool :=
  sorry

theorem test_existsb_1 : existsb (fun x => x =? 5) [0; 2; 3; 6] = false := by
  sorry

theorem test_existsb_2 : existsb (fun b => b && true) [true; true; false] = true := by
  sorry

theorem test_existsb_3 : existsb odd [1; 0; 0; 0; 0; 3] = true := by
  sorry

theorem test_existsb_4 : existsb even nil = false := by
  sorry

/-- 基于 德·摩根定律 的非递归版本 existsb -/
def existsb' {X : Type} (test : X → Bool) (l : list X) : Bool :=
  !(forallb (fun x => !test x) l)

/-- 证明 existsb 与 existsb' 行为完全等价 -/
theorem existsb_existsb' (X : Type) (test : X → Bool) (l : list X) :
    existsb test l = existsb' test l := by
  sorry

end Tactics
```
