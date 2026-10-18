---
title: "Redblack: Okasaki 红黑树：平衡旋转、黑高度与对数平衡界限"
---

```lean
import SFLean4.VFA.Perm
import SFLean4.VFA.Extract

namespace VFA.Redblack

open VFA.Perm
open VFA.Extract
```

# 《软件基础》(Software Foundations) 卷三：函数式算法验证 (VFA)

## 第十二章：红黑树 (Redblack: Red-Black Trees)

二叉搜索树（BST）在最坏情况下（例如按顺序连续插入元素）可能退化为线性链表，
导致查找与插入时间退化为 $\mathcal{O}(n)$。
**红黑树（Red-Black Tree, RBT）**是一种自平衡二叉搜索树，通过引入颜色标记与旋转重平衡策略，
确保整棵树维持对数级高度，从而保证最坏情况下的操作时间复杂度严格为 $\mathcal{O}(\log n)$。

本章基于 Chris Okasaki 的纯函数式红黑树算法（Purely Functional Data Structures）与 Andrew Appel 在 Coq 标准库 `MSets.MSetRBT` 中的经典设计，
深入展开两组关键性质的形式化证明：
1. **有序性与查改正确性（BST Invariant & Equational Specification）**：
   在树平衡旋转操作 `balance` 下保持元素有序、插入与查找的代数等式成立；
2. **平衡性与黑高度不变量（Red-Black Invariant & Black-Height Balance）**：
   证明任意节点红红不相邻（Local Invariant）、所有根到叶路径黑高度严格相同（Global Invariant），
   进而证明树的最大高度受限于最小深度的两倍加一（严格平衡性界限）。

---

## 1. 红黑树的函数式实现 (Implementation)

```lean
abbrev key : Type := Extract.int

/-- 节点颜色标记：红色或黑色 -/
inductive color where
  | Red
  | Black
  deriving Repr, DecidableEq

/-- 带有颜色标记的二叉搜索树 -/
inductive tree (V : Type) : Type where
  | E : tree V
  | T (c : color) (l : tree V) (k : key) (v : V) (r : tree V) : tree V

def empty_tree (V : Type) : tree V := tree.E

/-- 红黑树的元素查找操作（直接忽略节点颜色，遵循标准二叉查找） -/
def lookup {V : Type} (d : V) (x : key) (t : tree V) : V :=
  match t with
  | tree.E => d
  | tree.T _ tl k v tr =>
    if ltb x k then lookup d x tl
    else if ltb k x then lookup d x tr
    else v

/-- Okasaki 纯函数式四向树重平衡操作 -/
def balance {V : Type} (c : color) (t1 : tree V) (k : key) (vk : V) (t2 : tree V) : tree V :=
  match c with
  | color.Red => tree.T color.Red t1 k vk t2
  | color.Black =>
    match t1 with
    | tree.T color.Red (tree.T color.Red a x vx b) y vy c' =>
      tree.T color.Red (tree.T color.Black a x vx b) y vy (tree.T color.Black c' k vk t2)
    | tree.T color.Red a x vx (tree.T color.Red b y vy c') =>
      tree.T color.Red (tree.T color.Black a x vx b) y vy (tree.T color.Black c' k vk t2)
    | _ =>
      match t2 with
      | tree.T color.Red (tree.T color.Red b y vy c') z vz d =>
        tree.T color.Red (tree.T color.Black t1 k vk b) y vy (tree.T color.Black c' z vz d)
      | tree.T color.Red b y vy (tree.T color.Red c' z vz d) =>
        tree.T color.Red (tree.T color.Black t1 k vk b) y vy (tree.T color.Black c' z vz d)
      | _ => tree.T color.Black t1 k vk t2

/-- 内部插入递归过程：插入新红色节点并在回溯时重新平衡 -/
def ins {V : Type} (x : key) (vx : V) (t : tree V) : tree V :=
  match t with
  | tree.E => tree.T color.Red tree.E x vx tree.E
  | tree.T c a y vy b =>
    if ltb x y then balance c (ins x vx a) y vy b
    else if ltb y x then balance c a y vy (ins x vx b)
    else tree.T c a x vx b

/-- 树根置黑：确保红黑树全局根节点始终为黑色 -/
def make_black {V : Type} (t : tree V) : tree V :=
  match t with
  | tree.E => tree.E
  | tree.T _ a x vx b => tree.T color.Black a x vx b

/-- 完整的红黑树插入操作：插入后强制树根置黑 -/
def insert {V : Type} (x : key) (vx : V) (t : tree V) : tree V :=
  make_black (ins x vx t)

/-- 快速中序遍历转关联列表 -/
def elements_aux {V : Type} (t : tree V) (acc : List (key × V)) : List (key × V) :=
  match t with
  | tree.E => acc
  | tree.T _ l k v r => elements_aux l ((k, v) :: elements_aux r acc)

def elements {V : Type} (t : tree V) : List (key × V) :=
  elements_aux t []

theorem ins_not_E : ∀ (V : Type) (x : key) (vx : V) (t : tree V),
    ins x vx t ≠ tree.E := by
  sorry
```

---
## 2. 红黑树的 BST 不变量 (The BST Invariant)

```lean
/-- 全树节点谓词保持 -/
def ForallT {V : Type} (P : key → V → Prop) (t : tree V) : Prop :=
  match t with
  | tree.E => True
  | tree.T _ l k v r => P k v ∧ ForallT P l ∧ ForallT P r

/-- 忽略颜色标记的二叉搜索树保序不变量 -/
inductive BST {V : Type} : tree V → Prop where
  | ST_E : BST tree.E
  | ST_T (c : color) (l : tree V) (k : key) (v : V) (r : tree V) :
      ForallT (fun k' _ => Abs k' < Abs k) l →
      ForallT (fun k' _ => Abs k' > Abs k) r →
      BST l →
      BST r →
      BST (tree.T c l k v r)

theorem empty_tree_BST : ∀ (V : Type), BST (@empty_tree V) := by
  intro V
  exact BST.ST_E

/-- 平衡旋转操作保持 BST 不变量 -/
theorem balance_BST : ∀ (V : Type) (c : color) (l : tree V) (k : key) (v : V) (r : tree V),
    ForallT (fun k' _ => Abs k' < Abs k) l →
    ForallT (fun k' _ => Abs k' > Abs k) r →
    BST l →
    BST r →
    BST (balance c l k v r) := by
  sorry

/-- #### 练习：2 星 (balanceP)
证明平衡操作保持任意树节点性质 `P`。 -/
theorem balanceP : ∀ (V : Type) (P : key → V → Prop) (c : color) (l r : tree V) (k : key) (v : V),
    ForallT P l →
    ForallT P r →
    P k v →
    ForallT P (balance c l k v r) := by
  sorry

/-- #### 练习：2 星 (insP)
证明内部插入过程保持树节点性质 `P`。 -/
theorem insP : ∀ (V : Type) (P : key → V → Prop) (t : tree V) (k : key) (v : V),
    ForallT P t →
    P k v →
    ForallT P (ins k v t) := by
  sorry

/-- #### 练习：3 星 (ins_BST)
证明内部插入过程保持 BST 不变量。 -/
theorem ins_BST : ∀ (V : Type) (t : tree V) (k : key) (v : V),
    BST t → BST (ins k v t) := by
  sorry

/-- #### 练习：2 星 (insert_BST)
核心定理：完整红黑树插入操作保持 BST 不变量。 -/
theorem insert_BST : ∀ (V : Type) (t : tree V) (v : V) (k : key),
    BST t → BST (insert k v t) := by
  sorry
```

---
## 3. 代数性质形式化验证 (Verification of Map Equations)

```lean
theorem lookup_empty : ∀ (V : Type) (d : V) (k : key),
    lookup d k (@empty_tree V) = d := by
  intro V d k
  rfl

/-- #### 练习：6 星 (balance_lookup)
核心引理：证明平衡旋转操作保全 `lookup` 查询结果。 -/
theorem balance_lookup : ∀ (V : Type) (d : V) (c : color) (k k' : key) (v : V) (l r : tree V),
    BST l →
    BST r →
    ForallT (fun k'0 _ => Abs k'0 < Abs k) l →
    ForallT (fun k'0 _ => Abs k'0 > Abs k) r →
    lookup d k' (balance c l k v r) =
      (if Abs k' < Abs k then lookup d k' l
       else if Abs k' > Abs k then lookup d k' r
       else v) := by
  sorry

/-- #### 练习：3 星 (lookup_ins_eq)
在内部插入后查询刚刚插入的键，必得到插入值。 -/
theorem lookup_ins_eq : ∀ (V : Type) (d : V) (t : tree V) (k : key) (v : V),
    BST t → lookup d k (ins k v t) = v := by
  sorry

/-- #### 练习：3 星 (lookup_ins_neq)
在内部插入后查询不同的键，结果与原树一致。 -/
theorem lookup_ins_neq : ∀ (V : Type) (d : V) (t : tree V) (k k' : key) (v : V),
    BST t → k ≠ k' → lookup d k' (ins k v t) = lookup d k' t := by
  sorry

/-- #### 练习：1 星 (lookup_insert_eq)
顶层插入代数性质：新键命中。 -/
theorem lookup_insert_eq : ∀ (V : Type) (d : V) (t : tree V) (k : key) (v : V),
    BST t → lookup d k (insert k v t) = v := by
  sorry

/-- #### 练习：1 星 (lookup_insert_neq)
顶层插入代数性质：非相关键保持。 -/
theorem lookup_insert_neq : ∀ (V : Type) (d : V) (t : tree V) (k k' : key) (v : V),
    BST t → k ≠ k' → lookup d k' (insert k v t) = lookup d k' t := by
  sorry
```

---
## 4. 红黑平衡性不变量 (Efficiency and Red-Black Invariant)

```lean
/-- 红黑平衡谓词 `RB t c n`：
- `t`：目标子树；
- `c`：父节点的颜色（用于保证红节点的孩子绝不可为红）；
- `n`：该子树的黑高度（Black Height）。 -/
inductive RB {V : Type} : tree V → color → Nat → Prop where
  | RB_leaf (c : color) : RB tree.E c 0
  | RB_r (l r : tree V) (k : key) (v : V) (n : Nat) :
      RB l color.Red n →
      RB r color.Red n →
      RB (tree.T color.Red l k v r) color.Black n
  | RB_b (c : color) (l r : tree V) (k : key) (v : V) (n : Nat) :
      RB l color.Black n →
      RB r color.Black n →
      RB (tree.T color.Black l k v r) c (n + 1)

/-- #### 练习：1 星 (RB_blacken_parent)
将父节点颜色由红置黑保持 RB 谓词。 -/
theorem RB_blacken_parent : ∀ (V : Type) (t : tree V) (n : Nat),
    RB t color.Red n → RB t color.Black n := by
  sorry

/-- 允许根节点存在连续红色破坏的局部过渡状态 -/
inductive NearlyRB {V : Type} : tree V → Nat → Prop where
  | NearlyRB_r (l r : tree V) (k : key) (v : V) (n : Nat) :
      RB l color.Black n →
      RB r color.Black n →
      NearlyRB (tree.T color.Red l k v r) n
  | NearlyRB_b (l r : tree V) (k : key) (v : V) (n : Nat) :
      RB l color.Black n →
      RB r color.Black n →
      NearlyRB (tree.T color.Black l k v r) (n + 1)

/-- #### 练习：6 星 (ins_RB)
引理：`ins` 产生一棵标准红黑树或准红黑树。 -/
theorem ins_RB : ∀ (V : Type) (k : key) (v : V) (t : tree V) (n : Nat),
    (RB t color.Black n → NearlyRB (ins k v t) n) ∧
    (RB t color.Red n → RB (ins k v t) color.Black n) := by
  sorry

theorem ins_red : ∀ (V : Type) (t : tree V) (k : key) (v : V) (n : Nat),
    RB t color.Red n → RB (ins k v t) color.Black n := by
  intro V t k v n h
  exact (ins_RB V k v t n).2 h

/-- #### 练习：1 星 (RB_blacken_root)
证明将子树根节点置黑能维持合法红黑树性质（存在某个黑高度）。 -/
theorem RB_blacken_root : ∀ (V : Type) (t : tree V) (n : Nat),
    RB t color.Black n → ∃ n' : Nat, RB (make_black t) color.Red n' := by
  sorry

/-- #### 练习：1 星 (insert_RB)
核心定理：红黑树的插入操作保持红黑平衡性！ -/
theorem insert_RB : ∀ (V : Type) (t : tree V) (k : key) (v : V) (n : Nat),
    RB t color.Red n → ∃ n' : Nat, RB (insert k v t) color.Red n' := by
  sorry
```

### 树高度与平衡性界限证明

```lean
/-- 计算二叉树的最大高度 -/
def height {V : Type} (t : tree V) : Nat :=
  match t with
  | tree.E => 0
  | tree.T _ l _ _ r => 1 + max (height l) (height r)

/-- 计算二叉树的最小深度 -/
def mindepth {V : Type} (t : tree V) : Nat :=
  match t with
  | tree.E => 0
  | tree.T _ l _ _ r => 1 + min (mindepth l) (mindepth r)

/-- #### 练习：4 星，进阶 (redblack_bound)
红黑树平衡性定理：红黑树的最大高度不超过其最小深度的两倍加一。 -/
theorem redblack_balanced : ∀ (V : Type) (t : tree V) (c : color) (n : Nat),
    RB t c n → height t ≤ 2 * mindepth t + 1 := by
  sorry

end VFA.Redblack
```
