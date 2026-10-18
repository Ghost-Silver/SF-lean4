import SFLean4.VFA.Perm

/-!
# 优先队列 (Priqueue: Priority Queues)

**优先队列（Priority Queue）** 是一种支持快速检索并移除最高优先级元素的数据结构，
其核心操作包括：
- `empty`: 构造空队列
- `insert`: 向队列插入带权键值
- `delete_max`: 检出并删除最大键及其对应队列
- `merge`: 合并两个优先队列（可合并优先队列，Mergeable Priority Queue）

优先队列在离散事件模拟（如按时间步调度）、图算法（Dijkstra 最短路径）、
计算几何（凸包算法）以及堆排序（Heapsort）中扮演着不可或缺的角色。

本章先介绍优先队列的抽象规范签名（`PRIQUEUE`），
然后实现一个基于无序列表的轻量级参考模型（`List_Priqueue`），并严格证明其正确性。
-/

namespace VFA.Priqueue

open VFA.Perm

/-!
## 1. 优先队列模块规范签名 (Module Signature)

本规范定义了以自然数 `Nat` 为键的优先队列抽象数据类型（ADT）。
包含操作签名、表示不变量（`priq`）、抽象关系（`Abs`）以及代数正确性公理。
-/

abbrev key := Nat

structure PRIQUEUE where
  priqueue : Type

  empty : priqueue
  insert : key → priqueue → priqueue
  delete_max : priqueue → Option (key × priqueue)
  merge : priqueue → priqueue → priqueue

  priq : priqueue → Prop
  Abs : priqueue → List key → Prop

  can_relate : ∀ p, priq p → ∃ al, Abs p al
  abs_perm : ∀ p al bl,
    priq p → Abs p al → Abs p bl → Permutation al bl
  empty_priq : priq empty
  empty_relate : Abs empty []
  insert_priq : ∀ k p, priq p → priq (insert k p)
  insert_relate :
    ∀ p al k, priq p → Abs p al → Abs (insert k p) (k :: al)
  delete_max_None_relate :
    ∀ p, priq p → (Abs p [] ↔ delete_max p = none)
  delete_max_Some_priq :
    ∀ p q k, priq p → delete_max p = some (k, q) → priq q
  delete_max_Some_relate :
    ∀ (p q : priqueue) (k : key) (pl ql : List key),
      priq p →
      Abs p pl →
      delete_max p = some (k, q) →
      Abs q ql →
      Permutation pl (k :: ql) ∧ Forall (fun x => k ≥ x) ql
  merge_priq : ∀ p q, priq p → priq q → priq (merge p q)
  merge_relate :
    ∀ p q pl ql al,
      priq p → priq q →
      Abs p pl → Abs q ql → Abs (merge p q) al →
      Permutation al (pl ++ ql)

/-!
## 2. 基于列表的参考实现 (Implementation)

我们使用最直接的无序列表实现优先队列：
- `empty`: 常数时间 $O(1)$
- `insert`: 常数时间 $O(1)$（头插法）
- `delete_max`: 线性时间 $O(N)$（利用 `select` 遍历找出最大元）
- `merge`: 线性时间 $O(N)$（列表拼接 `++`）
-/

namespace List_Priqueue

abbrev key := Nat

/-- 队列即无序自然数列表 -/
abbrev priqueue := List key

/-- 选择列表中的最大元素并返回 `(最大值, 剩余元素列表)` -/
def select (i : Nat) (l : List Nat) : Nat × List Nat :=
  match l with
  | [] => (i, [])
  | h :: t =>
    if i >=? h then
      let (j, l') := select i t
      (j, h :: l')
    else
      let (j, l') := select h t
      (j, i :: l')

/-!
### 练习：select_perm_and_friends (3 星)
证明 `select` 函数的置换性质与最大值性质。
-/

/-- `select` 拆分出的元素对构成原列表的一个置换 -/
theorem select_perm (i : Nat) (l : List Nat) :
    let (j, r) := select i l
    Permutation (i :: l) (j :: r) := by
  sorry

/-- 辅助引理：`select` 找到的候选最大值大于等于初始累加器 `i` -/
theorem select_biggest_aux (i : Nat) (al : List Nat) (j : Nat) (bl : List Nat)
    (h1 : Forall (fun x => j ≥ x) bl)
    (h2 : select i al = (j, bl)) :
    j ≥ i := by
  sorry

/-- `select` 找到的最大值必定大于等于剩余列表中的所有元素 -/
theorem select_biggest (i : Nat) (al : List Nat) (j : Nat) (bl : List Nat)
    (h : select i al = (j, bl)) :
    Forall (fun x => j ≥ x) bl := by
  sorry

/-- 空队列 -/
def empty : priqueue := []

/-- 插入操作（常数时间头插） -/
def insert (k : key) (p : priqueue) : priqueue := k :: p

/-- 删除最大值（若为空返回 none；若非空利用 select 提取最大值） -/
def delete_max (p : priqueue) : Option (key × priqueue) :=
  match p with
  | [] => none
  | i :: p' => some (select i p')

/-- 队列合并（列表连接） -/
def merge (p q : priqueue) : priqueue := p ++ q

/-!
### 表示不变量与抽象关系
由于任意列表均能作为有效优先队列，表示不变量为平凡真；
抽象关系为自反同一关系。
-/

/-- 表示不变量：对无序列表任意排列均满足 -/
def priq (_ : priqueue) : Prop := True

/-- 抽象关系归纳定义 -/
inductive Abs' : priqueue → List key → Prop where
  | Abs_intro : ∀ p, Abs' p p

def Abs := Abs'

theorem can_relate : ∀ p, priq p → ∃ al, Abs p al := by
  intro p _
  exists p
  exact Abs'.Abs_intro p

theorem abs_perm : ∀ p al bl,
    priq p → Abs p al → Abs p bl → Permutation al bl := by
  intro p al bl _ h1 h2
  cases h1
  cases h2
  exact List.Perm.refl p

theorem empty_priq : priq empty := trivial

theorem empty_relate : Abs empty [] := Abs'.Abs_intro []

theorem insert_priq : ∀ k p, priq p → priq (insert k p) := by
  intros; trivial

theorem insert_relate :
    ∀ p al k, priq p → Abs p al → Abs (insert k p) (k :: al) := by
  intro p al k _ h
  cases h
  exact Abs'.Abs_intro (k :: p)

theorem delete_max_Some_priq :
    ∀ p q k, priq p → delete_max p = some (k, q) → priq q := by
  intros; trivial

/-!
### 练习：simple_priq_proofs (2 星)
完成 `delete_max` 与 `merge` 的正确性证明。
-/

theorem delete_max_None_relate :
    ∀ p, priq p →
      (Abs p [] ↔ delete_max p = none) := by
  sorry

theorem delete_max_Some_relate :
    ∀ (p q : priqueue) (k : key) (pl ql : List key),
      priq p →
      Abs p pl →
      delete_max p = some (k, q) →
      Abs q ql →
      Permutation pl (k :: ql) ∧ Forall (fun x => k ≥ x) ql := by
  sorry

theorem merge_priq :
    ∀ p q, priq p → priq q → priq (merge p q) := by
  intros; trivial

theorem merge_relate :
    ∀ p q pl ql al,
      priq p → priq q →
      Abs p pl → Abs q ql → Abs (merge p q) al →
      Permutation al (pl ++ ql) := by
  sorry

end List_Priqueue

end VFA.Priqueue
