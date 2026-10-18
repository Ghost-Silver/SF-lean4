import SFLean4.VFA.Perm
import SFLean4.VFA.Maps

/-!
# 前缀树：数字表示与高效查找表 (Trie: Number Representations and Efficient Lookup Tables)

在纯函数式编程中，由于缺乏命令式语言中数组的原地常数时间（$O(1)$）索引更新，
算法往往会承受额外的对数因子（$O(\log N)$）代价。
本章探讨如何构造高效的任意精度二进制数（正数 `positive`），并基于其二进制结构
设计一种高效的查找表——**二进制前缀树（Binary Trie）**。
前缀树不仅将单次查找与插入的复杂度降低到以键的位长为限（$O(\log N)$），
而且在 CompCert 编译器与 Coq/Lean 标准库中被广泛用作高效符号表和有限映射的核心实现。

## 主要内容
1. 函数式编程中的 $\log N$ 代价与数值表示
2. 正数二进制表示 `positive` 及其算术运算（`succ`, `addc`, `compare`）
3. 比较低效方案：`VerySlow` ($O(N^3)$), `RatherSlow` ($O(N^2 \log N)$), 平衡树 ($O(N \log^2 N)$)
4. 二进制前缀树 `trie` 的结构、查找（`look`）与插入（`ins`），达到 $O(N \log N)$
5. 前缀树查找与插入的代数关系（`look_ins_same`, `look_ins_other`）
6. 正数与自然数的双射（`nat2pos`, `pos2nat`）
7. 前缀树表 ADT 的表示不变量与全映射抽象关系（`is_trie`, `Abs`, `lookup_relate`, `insert_relate`）
-/

namespace VFA.Trie

open VFA.Perm
open VFA.Maps

/-!
## 1. 极其低效的初版程序 (A Simple Program That's Waaaaay Too Slow)

考虑检测一组数字中是否存在重复元素的算法。在命令式语言中使用数组标记，只需 $O(N)$ 时间。
若在函数式语言中使用基于函数的低效全映射（`total_map`，见 `Maps.lean`），
单次查找与更新需 $O(N)$，且由于一进制自然数 `Nat` 的相等性判定本身耗时 $O(N)$，
总体运行时间将高达三次多项式阶 $O(N^3)$！
-/

namespace VerySlow

/-- 循环遍历输入列表，利用低效的 `total_map` 统计重复项 -/
def loop (input : List Nat) (c : Nat) (table : total_map Bool) : Nat :=
  match input with
  | [] => c
  | a :: al =>
    if table a then
      loop al (c + 1) table
    else
      loop al c (t_update table a true)

/-- 检测碰撞总数 -/
def collisions (input : List Nat) : Nat :=
  loop input 0 (t_empty false)

example : collisions [3, 1, 4, 1, 5, 9, 2, 6] = 1 := by
  decide

end VerySlow

/-!
## 2. 高效正整数表示 (Efficient Positive Numbers)

为消除自然数一进制表示带来的线性代价，我们可以采用任意精度的二进制数表示。
正数 `positive` 由三种情形归纳构成：
- `xH`：表示 1
- `xO p`：表示 $2p + 0$
- `xI p`：表示 $2p + 1$
-/

namespace Integers

/-- 严格正整数的二进制表示（低位在最内层，高位在最外层） -/
inductive positive : Type where
  | xI : positive → positive
  | xO : positive → positive
  | xH : positive
deriving Repr, DecidableEq

open positive

/-- 10 的二进制表示为 1010₂ = 0 + 2*(1 + 2*(0 + 2*1)) -/
def ten : positive :=
  xO (xI (xO xH))

/-- 将二进制正数解释为一进制自然数 `Nat` -/
def positive2nat (p : positive) : Nat :=
  match p with
  | xI q => 1 + 2 * positive2nat q
  | xO q => 0 + 2 * positive2nat q
  | xH => 1

#eval positive2nat ten  -- 10

/-- 以高位到低位的二进制比特位列表形式打印 -/
def print_in_binary (p : positive) : List Nat :=
  match p with
  | xI q => print_in_binary q ++ ([1] : List Nat)
  | xO q => print_in_binary q ++ ([0] : List Nat)
  | xH => ([1] : List Nat)

/-- 二进制后继函数（自增 1，沿低位向高位进位） -/
def succ (x : positive) : positive :=
  match x with
  | xI p => xO (succ p)
  | xO p => xI p
  | xH => xO xH

/-- 带进位标志的二进制加法 -/
def addc (carry : Bool) (x y : positive) : positive :=
  match carry, x, y with
  | false, xI p, xI q => xO (addc true p q)
  | false, xI p, xO q => xI (addc false p q)
  | false, xI p, xH => xO (succ p)
  | false, xO p, xI q => xI (addc false p q)
  | false, xO p, xO q => xO (addc false p q)
  | false, xO p, xH => xI p
  | false, xH, xI q => xO (succ q)
  | false, xH, xO q => xI q
  | false, xH, xH => xO xH
  | true,  xI p, xI q => xI (addc true p q)
  | true,  xI p, xO q => xO (addc true p q)
  | true,  xI p, xH => xI (succ p)
  | true,  xO p, xI q => xO (addc true p q)
  | true,  xO p, xO q => xI (addc false p q)
  | true,  xO p, xH => xO (succ p)
  | true,  xH, xI q => xI (succ q)
  | true,  xH, xO q => xO (succ q)
  | true,  xH, xH => xI xH

/-- 二进制正数加法 -/
def add (x y : positive) : positive :=
  addc false x y

/-!
### 练习：succ_correct (2 星)
证明后继函数与自然数加 1 的语义等价性。
-/
theorem succ_correct (p : positive) :
    positive2nat (succ p) = positive2nat p + 1 := by
  sorry

/-!
### 练习：addc_correct (3 星)
证明带进位加法的正确性。
-/
theorem addc_correct (c : Bool) (p q : positive) :
    positive2nat (addc c p q) =
      (if c then 1 else 0) + positive2nat p + positive2nat q := by
  sorry

/-- 不带进位加法的正确性 -/
theorem add_correct (p q : positive) :
    positive2nat (add p q) = positive2nat p + positive2nat q := by
  unfold add
  rw [addc_correct]
  simp

/-- 三路数值比较结果 -/
inductive comparison : Type where
  | Eq : comparison
  | Lt : comparison
  | Gt : comparison
deriving Repr, DecidableEq

/-- 二进制正数的对数时间三路比较算法 -/
def compare (x y : positive) : comparison :=
  match x, y with
  | xI p, xI q => compare p q
  | xI p, xO q =>
    match compare p q with
    | comparison.Lt => comparison.Lt
    | _ => comparison.Gt
  | xI _, xH => comparison.Gt
  | xO p, xI q =>
    match compare p q with
    | comparison.Gt => comparison.Gt
    | _ => comparison.Lt
  | xO p, xO q => compare p q
  | xO _, xH => comparison.Gt
  | xH, xI _ => comparison.Lt
  | xH, xO _ => comparison.Lt
  | xH, xH => comparison.Eq
termination_by x

theorem positive2nat_pos (p : positive) :
    positive2nat p > 0 := by
  induction p with
  | xI q ih =>
    dsimp [positive2nat]
    omega
  | xO q ih =>
    dsimp [positive2nat]
    omega
  | xH =>
    dsimp [positive2nat]
    omega

/-!
### 练习：compare_correct (5 星)
证明三路比较算法的结果与自然数的大小顺序一致。
-/
theorem compare_correct (x y : positive) :
    match compare x y with
    | comparison.Lt => positive2nat x < positive2nat y
    | comparison.Eq => positive2nat x = positive2nat y
    | comparison.Gt => positive2nat x > positive2nat y := by
  sorry

/-- 由符号与正数构成的任意精度整数 -/
inductive Z : Type where
  | Z0 : Z
  | Zpos : positive → Z
  | Zneg : positive → Z
deriving Repr, DecidableEq

end Integers

open Integers
open Integers.positive

/-- 将自然数（大于 0）转换为二进制正数 -/
def natToPositive : Nat → positive
  | 0 => .xH
  | 1 => .xH
  | n + 2 =>
    if (n + 2) % 2 == 0 then
      .xO (natToPositive ((n + 2) / 2))
    else
      .xI (natToPositive ((n + 2) / 2))

instance (n : Nat) [NeZero n] : OfNat positive n where
  ofNat := natToPositive n

/-!
### 练习：successor_of_Z_constant_time (2 星，思考题)

解释为什么带进位的二进制整数后继操作（加 1）的平均时间复杂度为常数时间 $O(1)$：
在二进制数加 1 时，翻转的比特位数量取决于尾部连续为 1 的个数：
- 50% 的数字末位为 0，只需翻转 1 位，无需进一步进位；
- 25% 的数字末位为 01，翻转 2 位；
- 12.5% 的数字末位为 011，翻转 3 位；
- 依此类推，对长为 $k$ 的进位序列，发生的概率为 $1/2^k$。
平均翻转位数期望为：
$$\sum_{k=1}^\infty k \cdot \frac{1}{2^k} = 2 = O(1)$$
因此后继操作具有常数均摊 / 平均时间复杂度。
-/
def manual_grade_for_successor_of_Z_constant_time : Option (Nat × String) := none

/-!
## 3. 前缀树：基于正整数的高效查找表 (Binary Tries)

前缀树（Trie，又称数字查找树）是一种将键的位分解作为路径分支的多叉/二叉树。
由于正数 `positive` 是非空的比特序列，我们使用二进制前缀树：
- 沿 `xO` 分支向左走；
- 沿 `xI` 分支向右走；
- 到达 `xH` 时到达目标节点，读出或更新该处存储的值。

这种前缀树在深度至多为 $O(\log N)$ 的树高上完成单次查找与插入，
无需任何复杂的自平衡旋转，且键的比较仅为单步比特模式匹配。
-/

/-- 二叉前缀树 -/
inductive trie (A : Type) : Type where
  | Leaf : trie A
  | Node : trie A → A → trie A → trie A
deriving Repr

/-- 带有全局默认值的前缀树表 -/
def trie_table (A : Type) : Type := A × trie A

/-- 构造空前缀树表 -/
def empty {A : Type} (default : A) : trie_table A :=
  (default, trie.Leaf)

/-- 在前缀树中按正数键递归查找 -/
def look {A : Type} (default : A) (i : positive) (m : trie A) : A :=
  match m with
  | trie.Leaf => default
  | trie.Node l x r =>
    match i with
    | .xH => x
    | .xO i' => look default i' l
    | .xI i' => look default i' r

/-- 在前缀树表中查找正数键对应的值 -/
def lookup {A : Type} (i : positive) (t : trie_table A) : A :=
  look t.1 i t.2

/-- 向前缀树中插入正数键值对（若经过空节点则动态用默认值补全子树） -/
def ins {A : Type} (default : A) (i : positive) (a : A) (m : trie A) : trie A :=
  match m with
  | trie.Leaf =>
    match i with
    | .xH => trie.Node trie.Leaf a trie.Leaf
    | .xO i' => trie.Node (ins default i' a trie.Leaf) default trie.Leaf
    | .xI i' => trie.Node trie.Leaf default (ins default i' a trie.Leaf)
  | trie.Node l o r =>
    match i with
    | .xH => trie.Node l a r
    | .xO i' => trie.Node (ins default i' a l) o r
    | .xI i' => trie.Node l o (ins default i' a r)

/-- 向前缀树表中插入正数键值对 -/
def insert {A : Type} (i : positive) (a : A) (t : trie_table A) : trie_table A :=
  (t.1, ins t.1 i a t.2)

/-- 测试示例：连续插入 10 和 3 -/
def three_ten : trie_table Bool :=
  insert (3 : positive) true (insert (10 : positive) true (empty false))

#eval [3, 1, 4, 1, 5].map (fun (i : positive) => lookup i three_ten)

namespace FastEnough

/-- 利用前缀树表的高效检测循环 -/
def loop (input : List positive) (c : Nat) (table : trie_table Bool) : Nat :=
  match input with
  | [] => c
  | a :: al =>
    if lookup a table then
      loop al (1 + c) table
    else
      loop al c (insert a true table)

/-- 检测正数列表中的碰撞 -/
def collisions (input : List positive) : Nat :=
  loop input 0 (empty false)

example : collisions [3, 1, 4, 1, 5, 9, 2, 6] = 1 := by
  native_decide

end FastEnough

/-!
## 4. 查找与插入的代数关系引理 (Lemmas About lookup and insert)
-/

/-!
### 练习：look_leaf (1 星)
证明在空前缀树中查找任意键均返回默认值。
-/
theorem look_leaf {A : Type} (a : A) (j : positive) :
    look a j trie.Leaf = a := by
  sorry

/-!
### 练习：look_ins_same (2 星)
证明在插入键 `k` 后立即查找同一个键 `k`，必定返回刚刚插入的值 `v`。
-/
theorem look_ins_same {A : Type} (a : A) (k : positive) (v : A) (t : trie A) :
    look a k (ins a k v t) = v := by
  sorry

/-!
### 练习：look_ins_other (3 星)
证明在插入键 `k` 后查找另一个不相等的键 `j`，其值保持不变。
-/
theorem look_ins_other {A : Type} (a : A) (j k : positive) (v : A) (t : trie A)
    (h : j ≠ k) :
    look a j (ins a k v t) = look a j t := by
  sorry

/-!
## 5. 正数与自然数之间的双射 (Bijection Between positive and nat)

为了将基于 `positive` 的前缀树 ADT 与基于 `Nat` 的数学模型 `total_map` 关联，
我们需要建立从正数（$1, 2, 3, \dots$）到自然数（$0, 1, 2, \dots$）的一一双射：
- $0 \mapsto 1 = \text{xH}$
- $n+1 \mapsto \text{succ}(n)$
-/

/-- 将自然数双射到严格正数（0 对应 1, 1 对应 2, 等等） -/
def nat2pos : Nat → positive
  | 0 => .xH
  | n + 1 => succ (nat2pos n)

/-- 将严格正数双射回自然数 -/
def pos2nat (p : positive) : Nat :=
  positive2nat p - 1

/-- 从正数到自然数再到正数的恒等性 -/
axiom pos2nat2pos (p : positive) : nat2pos (pos2nat p) = p

/-- 从自然数到正数再到自然数的恒等性 -/
axiom nat2pos2nat (i : Nat) : pos2nat (nat2pos i) = i

/-!
### 练习：pos2nat_injective / nat2pos_injective (2 星)
基于双射引理证明两个映射均为单射。
-/
theorem pos2nat_injective (p q : positive) (h : pos2nat p = pos2nat q) :
    p = q := by
  sorry

theorem nat2pos_injective (i j : Nat) (h : nat2pos i = nat2pos j) :
    i = j := by
  sorry

/-!
## 6. 前缀树作为映射 ADT 的正确性证明 (Proving That Tries are a "Table" ADT)

在这里我们采用“所见即所得”的抽象关系：
一个前缀树表 `t` 抽象出的全映射 `abstract t`，就是通过 `lookup` 查询得到的函数。
-/

/-- 前缀树表的表示不变量（最简形式可设为平凡真） -/
def is_trie {A : Type} (_ : trie_table A) : Prop := True

/-- 抽象映射函数：通过双射 `nat2pos` 将自然数键映射为正数并查询前缀树 -/
def abstract {A : Type} (t : trie_table A) (n : Nat) : A :=
  lookup (nat2pos n) t

/-- 抽象关系：前缀树表 `t` 的抽象函数与规范全映射 `m` 外延相等 -/
def Abs {A : Type} (t : trie_table A) (m : total_map A) : Prop :=
  abstract t = m

/-!
### 练习：is_trie 不变量维护 (2 星)
-/
theorem empty_is_trie {A : Type} (default : A) :
    is_trie (empty default) := by
  sorry

theorem insert_is_trie {A : Type} (i : positive) (x : A) (t : trie_table A)
    (h : is_trie t) :
    is_trie (insert i x t) := by
  sorry

/-!
### 练习：empty_relate (2 星)
证明空表与 `t_empty` 保持抽象关系。
-/
theorem empty_relate {A : Type} (default : A) :
    Abs (empty default) (t_empty default) := by
  sorry

/-!
### 练习：lookup_relate (2 星)
证明查找操作与全映射查表一致。
-/
theorem lookup_relate {A : Type} (i : positive) (t : trie_table A) (m : total_map A)
    (ht : is_trie t) (ha : Abs t m) :
    lookup i t = m (pos2nat i) := by
  sorry

/-!
### 练习：insert_relate (3 星)
证明插入操作与全映射更新 `t_update` 保持抽象关系。
-/
theorem insert_relate {A : Type} (k : positive) (v : A) (t : trie_table A)
    (cts : total_map A) (ht : is_trie t) (ha : Abs t cts) :
    Abs (insert k v t) (t_update cts (pos2nat k) v) := by
  sorry

/-- 健全性检验：连续插入示例 -/
example :
    Abs
      (insert (3 : positive) true (insert (10 : positive) true (empty false)))
      (t_update (t_update (t_empty false) (pos2nat 10) true) (pos2nat 3) true) := by
  sorry

end VFA.Trie
