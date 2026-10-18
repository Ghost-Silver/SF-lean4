import SFLean4.VFA.Perm
import SFLean4.VFA.Maps
import SFLean4.VFA.SearchTree

namespace VFA.ADT

open VFA.Perm
open VFA.Maps
open VFA.SearchTree

/-!
# 《软件基础》(Software Foundations) 卷三：函数式算法验证 (VFA)

## 第十章：抽象数据类型 (ADT: Abstract Data Types)

**抽象数据类型（Abstract Data Type, ADT）**由一组值以及作用于该值集上的操作构成。
在形式化验证中，各操作所满足的形式化规范（Specification）也是 ADT 不可分割的核心组成部分。

在第九章 `SearchTree` 中，我们发现维持“表示不变量（Representation Invariant）”至关重要，
它排除了无法通过正规操作构建的非法数据，并充当了绝大多数操作的前提条件。
然而，作为数据结构的使用者（Client），并不需要关心底层的表示细节。

在本章中，我们将系统探讨：
1. **模块接口与实现（Interfaces & Implementations）**：全映射表（Table）的函数实现、关联列表实现与 BST 实现；
2. **带表示不变量的扩展接口（ETable with Representation Invariants）**；
3. **基于模型的规范与仿真关系（Model-based Specification & Simulation Relations）**；
4. **先进先出队列 ADT（FIFO Queue）**：单列表实现与摊还常数时间复杂度的双列表实现（Two-List Queue）；
5. **子类型与依值类型（Subset Types / Subtypes）**：向量（Vectors）与将不变量内嵌于类型的构造范式。

---

## 1. 关联表 ADT 接口 (The Table ADT)
-/

/-- 关联表 ADT 接口类 -/
structure Table (V : Type) where
  table : Type
  default : V
  empty : table
  get : key → table → V
  set : key → V → table → table
  get_empty_default : ∀ (k : key), get k empty = default
  get_set_same : ∀ (k : key) (v : V) (t : table), get k (set k v t) = v
  get_set_other : ∀ (k k' : key) (v : V) (t : table), k ≠ k' → get k' (set k v t) = get k' t

/-!
### 1.1 基于高阶函数的实现 (FunTable)
-/

namespace FunTable

def table (V : Type) : Type := key → V

def empty {V : Type} (default : V) : table V := fun _ => default

def get {V : Type} (k : key) (t : table V) : V := t k

def set {V : Type} (k : key) (v : V) (t : table V) : table V :=
  fun k' => if k = k' then v else t k'

theorem get_empty_default {V : Type} (default : V) : ∀ (k : key),
    get k (empty default) = default := by
  intro k
  rfl

theorem get_set_same {V : Type} : ∀ (k : key) (v : V) (t : table V),
    get k (set k v t) = v := by
  intro k v t
  dsimp [get, set]
  simp

theorem get_set_other {V : Type} : ∀ (k k' : key) (v : V) (t : table V),
    k ≠ k' → get k' (set k v t) = get k' t := by
  intro k k' v t h
  dsimp [get, set]
  by_cases h1 : k = k'
  · contradiction
  · simp [h1]

/-- 构造 FunTable 实例 -/
def makeTable (V : Type) (default : V) : Table V where
  table := table V
  default := default
  empty := empty default
  get := get
  set := set
  get_empty_default := get_empty_default default
  get_set_same := get_set_same
  get_set_other := get_set_other

end FunTable

/-!
---
## 2. 基于关联列表的实现 (Implementing Table with Lists)
-/

namespace ListsTable

def table (V : Type) : Type := List (key × V)

def empty {V : Type} : table V := []

/-- 查找关联列表中键对应的值 -/
def get {V : Type} (default : V) (k : key) (t : table V) : V :=
  match t with
  | [] => default
  | (k', v) :: t' => if k = k' then v else get default k t'

/-- 更新关联列表：头部追加最新键值对 -/
def set {V : Type} (k : key) (v : V) (t : table V) : table V :=
  (k, v) :: t

/-- #### 练习：0.5 星 (lists_table: get_empty_default) -/
theorem get_empty_default {V : Type} (default : V) : ∀ (k : key),
    get default k (@empty V) = default := by
  sorry

/-- #### 练习：0.5 星 (lists_table: get_set_same) -/
theorem get_set_same {V : Type} (default : V) : ∀ (k : key) (v : V) (t : table V),
    get default k (set k v t) = v := by
  sorry

/-- #### 练习：0.5 星 (lists_table: get_set_other) -/
theorem get_set_other {V : Type} (default : V) : ∀ (k k' : key) (v : V) (t : table V),
    k ≠ k' → get default k' (set k v t) = get default k' t := by
  sorry

end ListsTable

namespace StringListsTableExamples

open ListsTable

def default : String := ""

/-- #### 练习：0.5 星 (lists_table: ex1) -/
example : get default 0 empty = "" := by
  sorry

/-- #### 练习：0.5 星 (lists_table: ex2) -/
example : get default 0 (set 0 "A" empty) = "A" := by
  sorry

/-- #### 练习：0.5 星 (lists_table: ex3) -/
example : get default 1 (set 0 "A" empty) = "" := by
  sorry

end StringListsTableExamples

/-!
---
## 3. 基于二叉搜索树的实现 (Implementing Table with BSTs)
-/

namespace TreeTable

def table (V : Type) : Type := tree V

def empty {V : Type} : table V := empty_tree

def get {V : Type} (default : V) (k : key) (t : table V) : V :=
  lookup default k t

def set {V : Type} (k : key) (v : V) (t : table V) : table V :=
  insert k v t

theorem get_empty_default {V : Type} (default : V) : ∀ (k : key),
    get default k (@empty V) = default := by
  intro k
  apply lookup_empty

theorem get_set_same {V : Type} (default : V) : ∀ (k : key) (v : V) (t : table V),
    get default k (set k v t) = v := by
  intro k v t
  apply lookup_insert_eq

theorem get_set_other {V : Type} (default : V) : ∀ (k k' : key) (v : V) (t : table V),
    k ≠ k' → get default k' (set k v t) = get default k' t := by
  intro k k' v t h
  exact lookup_insert_neq V t default k k' v h

end TreeTable

/-!
---
## 4. 带表示不变量的扩展表 ADT (ETable)
-/

/-- 带有表示不变量 rep_ok 的扩展表接口 -/
structure ETable (V : Type) extends Table V where
  rep_ok : table → Prop
  bound : key → table → Bool
  elements : table → List (key × V)
  empty_ok : rep_ok empty
  set_ok : ∀ (k : key) (v : V) (t : table), rep_ok t → rep_ok (set k v t)
  bound_empty : ∀ (k : key), bound k empty = false
  bound_set_same : ∀ (k : key) (v : V) (t : table), bound k (set k v t) = true
  bound_set_other : ∀ (k k' : key) (v : V) (t : table), k ≠ k' → bound k' (set k v t) = bound k' t
  elements_complete : ∀ (k : key) (v : V) (t : table),
    rep_ok t → bound k t = true → get k t = v → List.Mem (k, v) (elements t)
  elements_correct : ∀ (k : key) (v : V) (t : table),
    rep_ok t → List.Mem (k, v) (elements t) → bound k t = true ∧ get k t = v

namespace TreeETable

open TreeTable

def rep_ok {V : Type} (t : table V) : Prop :=
  BST t

def bound {V : Type} (k : key) (t : table V) : Bool :=
  SearchTree.bound k t

def elements {V : Type} (t : table V) : List (key × V) :=
  SearchTree.elements t

theorem empty_ok {V : Type} : @rep_ok V empty :=
  empty_tree_BST V

theorem set_ok {V : Type} : ∀ (k : key) (v : V) (t : table V),
    rep_ok t → rep_ok (set k v t) := by
  intro k v t h
  apply insert_BST _ _ _ _ h

end TreeETable

/-!
---
## 5. 模型化规范 (Model-based Specification: ETableAbs)
-/

/-- 辅助定义：偏映射操作重命名适配 -/
def map_update {V : Type} (k : key) (v : V) (m : partial_map V) : partial_map V :=
  VFA.Maps.update m k v

def map_find {V : Type} (d : V) (k : key) (m : partial_map V) : V :=
  SearchTree.find d k m

def empty_map {V : Type} : partial_map V :=
  VFA.Maps.empty

/-- 带有抽象仿真函数的表接口 -/
structure ETableAbs (V : Type) extends Table V where
  bound : key → table → Bool
  elements : table → List (key × V)
  Abs : table → partial_map V
  rep_ok : table → Prop
  empty_ok : rep_ok empty
  set_ok : ∀ (k : key) (v : V) (t : table), rep_ok t → rep_ok (set k v t)
  empty_relate : Abs empty = empty_map
  bound_relate : ∀ (t : table) (k : key), rep_ok t → SearchTree.map_bound k (Abs t) = bound k t
  lookup_relate : ∀ (t : table) (k : key), rep_ok t → map_find default k (Abs t) = get k t
  insert_relate : ∀ (t : table) (k : key) (v : V), rep_ok t → map_update k v (Abs t) = Abs (set k v t)
  elements_relate : ∀ (t : table), rep_ok t → Abs t = SearchTree.map_of_list (elements t)

/-!
### 练习：基于关联列表实现 ETableAbs
-/

namespace ListETableAbs

def table (V : Type) : Type := List (key × V)

def default : String := ""

def empty {V : Type} : table V := []

def get {V : Type} (default : V) (k : key) (t : table V) : V :=
  ListsTable.get default k t

def set {V : Type} (k : key) (v : V) (t : table V) : table V :=
  (k, v) :: t

def bound {V : Type} (k : key) (t : table V) : Bool :=
  match t with
  | [] => false
  | (k', _) :: t' => if k = k' then true else bound k t'

def elements {V : Type} (t : table V) : List (key × V) :=
  t

def Abs {V : Type} (t : table V) : partial_map V :=
  SearchTree.map_of_list t

def rep_ok {V : Type} (_t : table V) : Prop :=
  True

/-- #### 练习：0.5 星 (StringListETableAbs.empty_ok) -/
theorem empty_ok {V : Type} : @rep_ok V empty := by
  trivial

/-- #### 练习：0.5 星 (StringListETableAbs.set_ok) -/
theorem set_ok {V : Type} : ∀ (k : key) (v : V) (t : table V),
    rep_ok t → rep_ok (set k v t) := by
  intro _ _ _ _
  trivial

/-- #### 练习：0.5 星 (StringListETableAbs.empty_relate) -/
theorem empty_relate {V : Type} : @Abs V empty = empty_map := by
  sorry

/-- #### 练习：0.5 星 (StringListETableAbs.bound_relate) -/
theorem bound_relate {V : Type} : ∀ (t : table V) (k : key),
    rep_ok t → SearchTree.map_bound k (Abs t) = bound k t := by
  sorry

/-- #### 练习：1.5 星 (StringListETableAbs.lookup_relate) -/
theorem lookup_relate {V : Type} (default : V) : ∀ (t : table V) (k : key),
    rep_ok t → map_find default k (Abs t) = get default k t := by
  sorry

/-- #### 练习：1.5 星 (StringListETableAbs.insert_relate) -/
theorem insert_relate {V : Type} : ∀ (t : table V) (k : key) (v : V),
    rep_ok t → map_update k v (Abs t) = Abs (set k v t) := by
  sorry

/-- #### 练习：1 星 (StringListETableAbs.elements_relate) -/
theorem elements_relate {V : Type} : ∀ (t : table V),
    rep_ok t → Abs t = SearchTree.map_of_list (elements t) := by
  sorry

end ListETableAbs

/-!
---
## 6. 另一个 ADT：先进先出队列 (FIFO Queue)
-/

/-- 队列代数规约接口 -/
structure Queue (V : Type) where
  queue : Type
  empty : queue
  is_empty : queue → Bool
  enq : queue → V → queue
  deq : queue → queue
  peek : V → queue → V
  is_empty_empty : is_empty empty = true
  is_empty_nonempty : ∀ q v, is_empty (enq q v) = false
  peek_empty : ∀ d, peek d empty = d
  peek_nonempty : ∀ d q v, peek d (enq q v) = peek v q
  deq_empty : deq empty = empty
  deq_nonempty : ∀ q v, deq (enq q v) = if is_empty q then q else enq (deq q) v

/-!
### 练习：单列表队列实现 (ListQueue)
-/

namespace ListQueue

abbrev V : Type := Nat

abbrev queue : Type := List V

def empty : queue := []

def is_empty (q : queue) : Bool :=
  match q with
  | [] => true
  | _ => false

def enq (q : queue) (v : V) : queue :=
  q ++ ([v] : List V)

def deq (q : queue) : queue :=
  match q with
  | [] => []
  | _ :: t => t

def peek (default : V) (q : queue) : V :=
  match q with
  | [] => default
  | h :: _ => h

/-- #### 练习：0.5 星 (ListQueue.is_empty_empty) -/
theorem is_empty_empty : is_empty empty = true := by
  sorry

/-- #### 练习：0.5 星 (ListQueue.is_empty_nonempty) -/
theorem is_empty_nonempty : ∀ q v, is_empty (enq q v) = false := by
  sorry

/-- #### 练习：0.5 星 (ListQueue.peek_empty) -/
theorem peek_empty : ∀ d, peek d empty = d := by
  sorry

/-- #### 练习：0.5 星 (ListQueue.peek_nonempty) -/
theorem peek_nonempty : ∀ d q v, peek d (enq q v) = peek v q := by
  sorry

/-- #### 练习：0.5 星 (ListQueue.deq_empty) -/
theorem deq_empty : deq empty = empty := by
  sorry

/-- #### 练习：0.5 星 (ListQueue.deq_nonempty) -/
theorem deq_nonempty : ∀ q v, deq (enq q v) = if is_empty q then q else enq (deq q) v := by
  sorry

end ListQueue

/-!
### 队列模型化规范与双列表队列 (Two-List Queue)
-/

/-- 双列表队列模型规约接口 -/
structure QueueAbs (V : Type) where
  queue : Type
  empty : queue
  is_empty : queue → Bool
  enq : queue → V → queue
  deq : queue → queue
  peek : V → queue → V
  Abs : queue → List V
  empty_relate : Abs empty = ([] : List V)
  enq_relate : ∀ q v, Abs (enq q v) = Abs q ++ ([v] : List V)
  peek_relate : ∀ d q, peek d q = (Abs q).headD d
  deq_relate : ∀ q, Abs (deq q) = (Abs q).tail

namespace TwoListQueueAbs

abbrev V : Type := Nat

/-- 双列表结构：`(f, b)` 前表正常存储，后表逆序存储 -/
def queue : Type := List V × List V

def Abs (q : queue) : List V :=
  q.1 ++ q.2.reverse

def empty : queue := ([], [])

def is_empty (q : queue) : Bool :=
  match q with
  | ([], []) => true
  | _ => false

def enq (q : queue) (v : V) : queue :=
  (q.1, v :: q.2)

def deq (q : queue) : queue :=
  match q with
  | ([], []) => ([], [])
  | ([], b) =>
    match b.reverse with
    | [] => ([], [])
    | _ :: f => (f, [])
  | (_ :: f, b) => (f, b)

def peek (d : V) (q : queue) : V :=
  match q with
  | ([], []) => d
  | ([], b) =>
    match b.reverse with
    | [] => d
    | v :: _ => v
  | (v :: _, _) => v

/-- #### 练习：0.5 星 (TwoListQueueAbs.empty_relate) -/
theorem empty_relate : Abs empty = ([] : List V) := by
  sorry

/-- #### 练习：0.5 星 (TwoListQueueAbs.enq_relate) -/
theorem enq_relate : ∀ q v, Abs (enq q v) = Abs q ++ ([v] : List V) := by
  sorry

/-- #### 练习：1 星 (TwoListQueueAbs.peek_relate) -/
theorem peek_relate : ∀ d q, peek d q = (Abs q).headD d := by
  sorry

/-- #### 练习：1 星 (TwoListQueueAbs.deq_relate) -/
theorem deq_relate : ∀ q, Abs (deq q) = (Abs q).tail := by
  sorry

end TwoListQueueAbs

/-!
---
## 7. 子类型与依值向量 (Subset Types & Vectors)
-/

/-- 定长向量（Vector）：由基础列表和长度相符的证明构成的子类型 -/
def vector (X : Type) : Type :=
  { p : List X × Nat // p.1.length = p.2 }

/-- #### 练习：1 星 (a_vector)
构造任意合法向量示例 -/
def a_vector : vector Nat :=
  ⟨([], 0), rfl⟩

def list_of_vector {X : Type} (v : vector X) : List X :=
  v.val.1

def vector_cons {X : Type} (x : X) (v : vector X) : vector X :=
  ⟨(x :: v.val.1, v.val.2 + 1), by simp; exact v.property⟩

/-- #### 练习：2 星 (vector_cons_correct) -/
theorem vector_cons_correct : ∀ (X : Type) (x : X) (v : vector X),
    list_of_vector (vector_cons x v) = x :: list_of_vector v := by
  sorry

def vector_app {X : Type} (v1 v2 : vector X) : vector X :=
  ⟨(v1.val.1 ++ v2.val.1, v1.val.2 + v2.val.2), by
    simp [v1.property, v2.property]⟩

/-- #### 练习：2 星 (vector_app_correct) -/
theorem vector_app_correct : ∀ (X : Type) (v1 v2 : vector X),
    list_of_vector (vector_app v1 v2) = list_of_vector v1 ++ list_of_vector v2 := by
  sorry

end VFA.ADT
