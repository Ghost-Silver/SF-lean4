---
title: "SearchTree: 二叉搜索树 BST：表示不变量与抽象仿真模型"
---

```lean
import SFLean4.VFA.Perm
import SFLean4.VFA.Maps
import SFLean4.VFA.Sort

namespace VFA.SearchTree

open VFA.Perm
open VFA.Maps
open VFA.Sort
```

# 《软件基础》(Software Foundations) 卷三：函数式算法验证 (VFA)

## 第九章：二叉搜索树 (SearchTree: Binary Search Trees)

在前面章节中，我们分别使用**键值对列表**（《逻辑基础》）和**高阶函数**（`Maps`）实现了字典映射。
但这两种实现各有利弊：
- 列表查找的时间复杂度与键值对数量呈线性关系 $\mathcal{O}(n)$；
- 高阶函数不支持枚举元素键集，且难以检查有限性。

如果键集合存在全序关系（例如自然数上的 $\le$ 与 $<$ 判定），我们可以利用**二叉搜索树（Binary Search Tree, BST）**实现映射。
在平衡的 BST 中，查找（Lookup）和插入（Insert）操作的时间复杂度与树高度呈正比，即达到对数级 $\mathcal{O}(\log n)$。

本章将系统性完成：
1. **持久化函数式 BST 的实现**（纯函数式树节点插入与查询）；
2. **BST 不变量（BST Invariant）的形式化定义**；
3. **代数规范（Algebraic Specification）**对 BST 操作的刻画；
4. **展平为有序关联列表（Elements）的完备性与正确性双向证明**；
5. **模型化规范（Model-based Specification）**：证明 BST 与抽象字典映射（Partial Map）的仿真对应。

---

## 1. BST 的持久化函数式实现 (BST Implementation)

```lean
/-- 树中存储的键类型统一采用自然数 -/
abbrev key : Type := Nat

/-- 二叉搜索树的归纳数据类型：
- `E`：空树（Empty Tree）；
- `T l k v r`：存储键 `k` 与值 `v` 的节点，左子树为 `l`，右子树为 `r`。 -/
inductive tree (V : Type) : Type where
  | E : tree V
  | T (l : tree V) (k : key) (v : V) (r : tree V) : tree V

/-- 空树常量 -/
def empty_tree {V : Type} : tree V :=
  tree.E

/-- 查询键 `x` 是否在树 `t` 中被绑定 -/
def bound {V : Type} (x : key) (t : tree V) : Bool :=
  match t with
  | tree.E => false
  | tree.T l y _ r =>
    if x < y then bound x l
    else if x > y then bound x r
    else true

/-- 在树 `t` 中查找键 `x` 对应的值；若键未绑定，则返回默认值 `d` -/
def lookup {V : Type} (d : V) (x : key) (t : tree V) : V :=
  match t with
  | tree.E => d
  | tree.T l y v r =>
    if x < y then lookup d x l
    else if x > y then lookup d x r
    else v

/-- 持久化插入：向树中加入新的键值绑定 `(x, v)`；若键已存在则替换其值 -/
def insert {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | tree.E => tree.T tree.E x v tree.E
  | tree.T l y v' r =>
    if x < y then tree.T (insert x v l) y v' r
    else if x > y then tree.T l y v' (insert x v r)
    else tree.T l x v r
```

### 树操作的单元测试

```lean
def ex_tree : tree String :=
  tree.T (tree.T tree.E 2 "two" tree.E) 4 "four" (tree.T tree.E 5 "five" tree.E)

example : insert 5 "five" (insert 2 "two" (insert 4 "four" empty_tree)) = ex_tree := by
  rfl

example : lookup "" 5 ex_tree = "five" := by rfl
example : lookup "" 3 ex_tree = "" := by rfl
example : bound 3 ex_tree = false := by rfl
```

---
## 2. BST 不变量 (BST Invariant)

二叉搜索树的核心在于其结构不变量：
对于每个非空节点 `T l k v r`，左子树 `l` 中的所有键均严格小于 `k`，
而右子树 `r` 中的所有键均严格大于 `k`，且左右子树自身也均满足 BST 不变量。

```lean
/-- 谓词全称遍历：命题 `P` 对二叉树 `t` 的每一个节点均成立 -/
def ForallT {V : Type} (P : key → V → Prop) (t : tree V) : Prop :=
  match t with
  | tree.E => True
  | tree.T l k v r => P k v ∧ ForallT P l ∧ ForallT P r

/-- 二叉搜索树不变量的归纳定义 -/
inductive BST {V : Type} : tree V → Prop where
  | BST_E : BST tree.E
  | BST_T (l : tree V) (x : key) (v : V) (r : tree V) :
      ForallT (fun y _ => y < x) l →
      ForallT (fun y _ => y > x) r →
      BST l →
      BST r →
      BST (tree.T l x v r)

/-- #### 练习：1 星 (empty_tree_BST)
证明空树必然满足 BST 不变量。 -/
theorem empty_tree_BST : ∀ (V : Type), BST (@empty_tree V) := by
  sorry

/-- #### 练习：1.5 星 (ForallT_insert)
引理：向树中插入新元素后，保全树节点谓词。 -/
theorem ForallT_insert : ∀ (V : Type) (P : key → V → Prop) (t : tree V),
    ForallT P t →
    ∀ (k : key) (v : V), P k v → ForallT P (insert k v t) := by
  sorry

/-- #### 练习：1.5 星 (insert_BST)
核心定理：对满足 BST 不变量的树执行插入，得到的新树仍然满足 BST 不变量。 -/
theorem insert_BST : ∀ (V : Type) (k : key) (v : V) (t : tree V),
    BST t → BST (insert k v t) := by
  sorry
```

---
## 3. BST 操作的代数规范 (Algebraic Specification)

```lean
/-- 在空树中查找任何键均返回默认值 -/
theorem lookup_empty : ∀ (V : Type) (d : V) (k : key),
    lookup d k empty_tree = d := by
  intro V d k
  rfl

/-- 刚刚插入的键立即查询必能命中对应的值 -/
theorem lookup_insert_eq : ∀ (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insert k v t) = v := by
  sorry

/-- 插入键 `k` 不会影响对不同键 `k'` 的查询结果 -/
theorem lookup_insert_neq : ∀ (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
    k ≠ k' → lookup d k' (insert k v t) = lookup d k' t := by
  sorry

/-- #### 练习：1 星，选做 (bound_default)
证明若 `bound` 返回 false，则 `lookup` 必定返回默认值。 -/
theorem bound_default : ∀ (V : Type) (k : key) (d : V) (t : tree V),
    bound k t = false → lookup d k t = d := by
  sorry

/-- #### 练习：2 星，选做 (lookup_insert_shadow) -/
theorem lookup_insert_shadow : ∀ (V : Type) (t : tree V) (v v' d : V) (k k' : key),
    lookup d k' (insert k v (insert k v' t)) = lookup d k' (insert k v t) := by
  sorry

/-- #### 练习：2 星，选做 (lookup_insert_same) -/
theorem lookup_insert_same : ∀ (V : Type) (k k' : key) (d : V) (t : tree V),
    lookup d k' (insert k (lookup d k t) t) = lookup d k' t := by
  sorry

/-- #### 练习：2 星，选做 (lookup_insert_permute) -/
theorem lookup_insert_permute : ∀ (V : Type) (v1 v2 d : V) (k1 k2 k' : key) (t : tree V),
    k1 ≠ k2 →
    lookup d k' (insert k1 v1 (insert k2 v2 t)) =
    lookup d k' (insert k2 v2 (insert k1 v1 t)) := by
  sorry

/-- 树结构层面覆盖插入的直接等式 -/
theorem insert_shadow_equality : ∀ (V : Type) (t : tree V) (k : key) (v v' : V),
    insert k v (insert k v' t) = insert k v t := by
  sorry

/-- #### 练习：2 星，选做 (direct_equalities_break)
树层面的“重新插入原值”等式反例 -/
theorem insert_same_equality_breaks :
    ∃ (V : Type) (d : V) (t : tree V) (k : key),
      insert k (lookup d k t) t ≠ t := by
  sorry

/-- 树层面的“交换插入次序”等式反例 -/
theorem insert_permute_equality_breaks :
    ∃ (V : Type) (v1 v2 : V) (k1 k2 : key) (t : tree V),
      k1 ≠ k2 ∧ insert k1 v1 (insert k2 v2 t) ≠ insert k2 v2 (insert k1 v1 t) := by
  sorry
```

---
## 4. 将 BST 转换为列表 (Converting a BST to a List)

```lean
/-- 中序遍历二叉树生成键值对关联列表 -/
def elements {V : Type} (t : tree V) : List (key × V) :=
  match t with
  | tree.E => []
  | tree.T l k v r => elements l ++ ([(k, v)] : List (key × V)) ++ elements r

example : elements ex_tree = [(2, "two"), (4, "four"), (5, "five")] := by
  decide

/-- 元素完备性规约 -/
def elements_complete_spec : Prop :=
  ∀ (V : Type) (k : key) (v d : V) (t : tree V),
    bound k t = true →
    lookup d k t = v →
    List.Mem (k, v) (elements t)

/-- #### 练习：3 星 (elements_complete)
证明 `elements` 的完备性：凡是树中绑定的元素均会出现在列表中。 -/
theorem elements_complete : elements_complete_spec := by
  sorry

/-- 元素正确性规约 -/
def elements_correct_spec : Prop :=
  ∀ (V : Type) (k : key) (v d : V) (t : tree V),
    BST t →
    List.Mem (k, v) (elements t) →
    bound k t = true ∧ lookup d k t = v

/-- 辅助函数：解柯里化（Uncurry） -/
def uncurry {X Y Z : Type} (f : X → Y → Z) : X × Y → Z :=
  fun (a, b) => f a b

/-- #### 练习：2 星 (elements_preserves_forall)
证明树的节点性质转化为列表中元素对性质的保持。 -/
theorem elements_preserves_forall : ∀ (V : Type) (P : key → V → Prop) (t : tree V),
    ForallT P t →
    Forall (uncurry P) (elements t) := by
  sorry

/-- #### 练习：2 星 (elements_preserves_relation)
证明树键与外部分界键的关系在元素列表中得到保持。 -/
theorem elements_preserves_relation :
    ∀ (V : Type) (k k' : key) (v : V) (t : tree V) (R : key → key → Prop),
      ForallT (fun y _ => R y k') t →
      List.Mem (k, v) (elements t) →
      R k k' := by
  sorry

/-- #### 练习：6 星 (elements_correct)
核心定理：证明 `elements` 的正确性。 -/
theorem elements_correct : elements_correct_spec := by
  sorry

/-- #### 练习：2 星，进阶 (elements_complete_inverse) -/
theorem elements_complete_inverse :
    ∀ (V : Type) (k : key) (v : V) (t : tree V),
      BST t →
      bound k t = false →
      ¬ List.Mem (k, v) (elements t) := by
  sorry

/-- #### 练习：2 星，进阶 (bound_value) -/
theorem bound_value : ∀ (V : Type) (k : key) (t : tree V),
    bound k t = true → ∃ v : V, ∀ d : V, lookup d k t = v := by
  sorry

/-- #### 练习：4 星，进阶 (elements_correct_inverse) -/
theorem elements_correct_inverse :
    ∀ (V : Type) (k : key) (t : tree V),
      (∀ v : V, ¬ List.Mem (k, v) (elements t)) →
      bound k t = false := by
  sorry
```

### 列表的有序性与无重复键

```lean
/-- #### 练习：3 星，进阶 (sorted_app)
证明在两个列表间插入中枢元保持全局有序。 -/
theorem sorted_app : ∀ (l1 l2 : List Nat) (x : Nat),
    VFA.Sort.sorted l1 →
    VFA.Sort.sorted l2 →
    Forall (fun n => n < x) l1 →
    Forall (fun n => n > x) l2 →
    VFA.Sort.sorted (l1 ++ x :: l2) := by
  sorry

/-- 抽取关联列表中的所有键 -/
def list_keys {V : Type} (lst : List (key × V)) : List Nat :=
  lst.map Prod.fst

/-- #### 练习：6 星，进阶 (sorted_elements)
证明 BST 转换出的列表键必然严格升序排列。 -/
theorem sorted_elements : ∀ (V : Type) (t : tree V),
    BST t → VFA.Sort.sorted (list_keys (elements t)) := by
  sorry

/-- 双列表无交集判定 -/
def disjoint {X : Type} (l1 l2 : List X) : Prop :=
  ∀ x : X, List.Mem x l1 → ¬ List.Mem x l2

/-- 无重复列表归纳谓词 -/
inductive NoDup {A : Type} : List A → Prop where
  | NoDup_nil : NoDup []
  | NoDup_cons (x : A) (l : List A) : ¬ List.Mem x l → NoDup l → NoDup (x :: l)

/-- #### 练习：3 星，进阶，选做 (NoDup_append) -/
theorem NoDup_append : ∀ (X : Type) (l1 l2 : List X),
    NoDup l1 → NoDup l2 → disjoint l1 l2 → NoDup (l1 ++ l2) := by
  sorry

/-- #### 练习：4 星，进阶，选做 (elements_nodup_keys) -/
theorem elements_nodup_keys : ∀ (V : Type) (t : tree V),
    BST t → NoDup (list_keys (elements t)) := by
  sorry
```

---
## 5. 快速尾递归中序遍历 (Fast Elements Implementation)

```lean
/-- 累加器风格的尾递归中序遍历（避免 `++` 带来的二次方开销） -/
def fast_elements_tr {V : Type} (t : tree V) (acc : List (key × V)) : List (key × V) :=
  match t with
  | tree.E => acc
  | tree.T l k v r => fast_elements_tr l ((k, v) :: fast_elements_tr r acc)

/-- 快速遍历顶层调用 -/
def fast_elements {V : Type} (t : tree V) : List (key × V) :=
  fast_elements_tr t []

/-- #### 练习：2 星 (fast_elements_tr_helper) -/
theorem fast_elements_tr_helper :
    ∀ (V : Type) (t : tree V) (lst : List (key × V)),
      fast_elements_tr t lst = elements t ++ lst := by
  sorry

/-- #### 练习：1 星 (fast_elements_eq_elements)
证明快速遍历与标准遍历结果完全等价。 -/
theorem fast_elements_eq_elements : ∀ (V : Type) (t : tree V),
    fast_elements t = elements t := by
  sorry

/-- 由等价性即刻推得快速遍历的完全正确性 -/
theorem fast_elements_correct :
    ∀ (V : Type) (k : key) (v d : V) (t : tree V),
      BST t →
      List.Mem (k, v) (fast_elements t) →
      bound k t = true ∧ lookup d k t = v := by
  intro V k v d t hbst hin
  rw [fast_elements_eq_elements] at hin
  exact elements_correct V k v d t hbst hin
```

---
## 6. 模型化规范 (Model-based Specifications)

```lean
/-- 将关联列表转化为抽象偏映射 -/
def map_of_list {V : Type} (el : List (key × V)) : partial_map V :=
  match el with
  | [] => VFA.Maps.empty
  | (k, v) :: el' => VFA.Maps.update (map_of_list el') k v

/-- 抽象映射函数：将具体二叉树投影为抽象偏映射 -/
def Abs {V : Type} (t : tree V) : partial_map V :=
  map_of_list (elements t)

/-- 抽象偏映射查询操作 -/
def find {V : Type} (d : V) (k : key) (m : partial_map V) : V :=
  match m k with
  | some v => v
  | none => d

/-- 抽象偏映射绑定状态判定 -/
def map_bound {V : Type} (k : key) (m : partial_map V) : Bool :=
  match m k with
  | some _ => true
  | none => false

theorem empty_relate : ∀ (V : Type), @Abs V empty_tree = VFA.Maps.empty := by
  intro V
  rfl

/-- #### 练习：3 星，选做 (bound_relate) -/
theorem bound_relate : ∀ (V : Type) (t : tree V) (k : key),
    BST t → map_bound k (Abs t) = bound k t := by
  sorry

/-- #### 练习：3 星，选做 (lookup_relate) -/
theorem lookup_relate : ∀ (V : Type) (t : tree V) (d : V) (k : key),
    BST t → find d k (Abs t) = lookup d k t := by
  sorry

/-- 将关联列表作为键值插入 -/
def kvs_insert {V : Type} (k : key) (v : V) (kvs : List (key × V)) : List (key × V) :=
  match kvs with
  | [] => [(k, v)]
  | (k', v') :: kvs' =>
    if k < k' then (k, v) :: kvs
    else if k > k' then (k', v') :: kvs_insert k v kvs'
    else (k, v) :: kvs'

/-- #### 练习：3 星，选做 (kvs_insert_elements) -/
theorem kvs_insert_elements : ∀ (V : Type) (t : tree V),
    BST t →
    ∀ (k : key) (v : V),
      elements (insert k v t) = kvs_insert k v (elements t) := by
  sorry

/-- #### 练习：3 星，选做 (insert_relate) -/
theorem insert_relate : ∀ (V : Type) (t : tree V) (k : key) (v : V),
    BST t → Abs (insert k v t) = VFA.Maps.update (Abs t) k v := by
  sorry

theorem elements_relate : ∀ (V : Type) (t : tree V),
    BST t → map_of_list (elements t) = Abs t := by
  intro V t _h
  rfl
```

---
## 7. 备用抽象关系 (Alternative Abstraction Relation)

```lean
/-- 两偏映射的不相交并集运算 -/
def union {X : Type} (m1 m2 : partial_map X) : partial_map X :=
  fun k =>
    match m1 k, m2 k with
    | none, none => none
    | none, some v => some v
    | some v, none => some v
    | some _, some _ => none

/-- 基于树结构的直接抽象转换 -/
def map_of_tree {V : Type} (t : tree V) : partial_map V :=
  match t with
  | tree.E => VFA.Maps.empty
  | tree.T l k v r => VFA.Maps.update (union (map_of_tree l) (map_of_tree r)) k v

/-- 备用抽象函数 -/
def Abs' {V : Type} (t : tree V) : partial_map V :=
  map_of_tree t

theorem empty_relate' : ∀ (V : Type), @Abs' V empty_tree = VFA.Maps.empty := by
  intro V
  rfl

/-- #### 练习：3 星，进阶，选做 (bound_relate') -/
theorem bound_relate' : ∀ (V : Type) (t : tree V) (k : key),
    BST t → map_bound k (Abs' t) = bound k t := by
  sorry

/-- #### 练习：3 星，进阶，选做 (lookup_relate') -/
theorem lookup_relate' : ∀ (V : Type) (d : V) (t : tree V) (k : key),
    BST t → find d k (Abs' t) = lookup d k t := by
  sorry

/-- #### 练习：4 星，进阶，选做 (insert_relate') -/
theorem insert_relate' : ∀ (V : Type) (k : key) (v : V) (t : tree V),
    BST t → Abs' (insert k v t) = VFA.Maps.update (Abs' t) k v := by
  sorry

/-- #### 练习：4 星，进阶，选做 (elements_relate') -/
theorem elements_relate' : ∀ (V : Type) (t : tree V),
    BST t → map_of_list (elements t) = Abs' t := by
  sorry

end VFA.SearchTree
```
