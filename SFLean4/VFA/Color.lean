import SFLean4.VFA.Perm

/-!
# 图着色与寄存器分配 (Color: Graph Coloring)

无向图的 **$K$-着色问题（$K$-Coloring）** 是指为图中每个节点分配一种颜色（从包含 $K$ 种颜色的调色板中选取），
使得任意两个通过边相连的节点具有不同的颜色。
图的 **色数（Chromatic Number）** 是成功着色所需的最小颜色数。

在编译器构造中，**图着色寄存器分配（Register Allocation via Graph Coloring）** 是一项经典核心技术：
- 图的节点对应程序中的临时变量（虚拟寄存器）；
- 图的边表示变量的 **冲突（Interference）**（即两个变量在同一生命周期内同时存活，不能共享同一硬件寄存器）；
- 颜色对应目标处理器的物理寄存器；
- 若图中某些节点因度数过高无法分配物理寄存器，则将其 **溢出（Spill）** 到内存栈帧中。

本章形式化实现并验证基于 **Kempe-Chaitin 启发式算法** 的快速图着色算法：
1. **简化阶段（Simplify）**：寻找度数小于 $K$ 的节点将其移除并压入栈（因为度数小于 $K$ 的节点即使其余邻居染上互不相同的颜色，也至少剩余一种安全可用颜色）；
2. **选择阶段（Select）**：若不存在低度数节点，则挑选节点溢出；
3. **着色阶段（Color）**：将栈中节点依次弹出放回图中，贪心挑选邻居未占用的安全颜色完成着色。
-/

namespace VFA.Color

open VFA.Perm

/-!
## 1. 基础结构：节点、集合与映射接口 (Nodes, Sets and Maps)

为了与 Coq 原书中的 `PositiveSet` (`FSets`) 和 `PositiveMap` (`FMaps`) 概念对齐，
我们在此构建具有相同接口规范的函数式节点集合 `S` 与节点字典 `M`。
-/

namespace E

abbrev t := Nat

def lt (x y : t) : Prop := x < y
def eq (x y : t) : Prop := x = y
def eq_dec (x y : t) : Decidable (x = y) := inferInstance

end E

namespace S

abbrev elt := Nat
abbrev t := List Nat

def empty : t := []
def add (x : elt) (s : t) : t := if x ∈ s then s else x :: s
def remove (x : elt) (s : t) : t := s.filter (· ≠ x)
def In (x : elt) (s : t) : Prop := x ∈ s
def elements (s : t) : List elt := s
def cardinal (s : t) : Nat := s.length
def fold {B : Type} (f : elt → B → B) (s : t) (b : B) : B := s.foldr f b
def choose (s : t) : Option elt := s.head?
def diff (s1 s2 : t) : t := s1.filter (fun x => decide (x ∉ s2))
def Subset (s1 s2 : t) : Prop := ∀ x, x ∈ s1 → x ∈ s2
def eq (s1 s2 : t) : Prop := Subset s1 s2 ∧ Subset s2 s1

end S

namespace M

abbrev key := Nat
abbrev t (A : Type) := List (Nat × A)

def empty (A : Type) : t A := []
def find {A : Type} (x : key) (m : t A) : Option A :=
  match m.find? (fun p => p.1 == x) with
  | some (_, v) => some v
  | none => none

def add {A : Type} (x : key) (v : A) (m : t A) : t A :=
  (x, v) :: m.filter (·.1 ≠ x)

def remove {A : Type} (x : key) (m : t A) : t A :=
  m.filter (·.1 ≠ x)

def elements {A : Type} (m : t A) : List (key × A) := m
def cardinal {A : Type} (m : t A) : Nat := m.length
def fold {A B : Type} (f : key → A → B → B) (m : t A) (b : B) : B :=
  m.foldr (fun (k, v) acc => f k v acc) b

def map {A B : Type} (f : A → B) (m : t A) : t B :=
  m.map (fun (k, v) => (k, f v))

def In {A : Type} (x : key) (m : t A) : Prop :=
  ∃ v, find x m = some v

def eq_key_elt {A : Type} (p1 p2 : key × A) : Prop :=
  p1.1 = p2.1 ∧ p1.2 = p2.2

def lt_key {A : Type} (p1 p2 : key × A) : Prop :=
  p1.1 < p2.1

end M

/-- 计算映射的定义域（所有键构成的集合） -/
def Mdomain {A : Type} (m : M.t A) : S.t :=
  M.fold (fun n _ s => S.add n s) m S.empty

/-- 示例映射 -/
def example_map : M.t S.t :=
  M.add 3 S.empty (M.add 9 S.empty (M.add 2 S.empty (M.empty S.t)))

#eval S.elements (Mdomain example_map)

/-!
## 2. 集合与映射的相关性质引理 (Lemmas About Sets and Maps)
-/

/-- 列表等价关系（元素包含意义上的双向等价） -/
def equivlistA {A : Type} (eqA : A → A → Prop) (l l' : List A) : Prop :=
  ∀ x : A, (∃ y ∈ l, eqA x y) ↔ (∃ y ∈ l', eqA x y)

/-- 列表相等于集合等价 -/
theorem eqlistA_Eeq_eq (al bl : List Nat) :
    equivlistA Eq al bl ↔ al = bl := by
  sorry

/-- 排序后的列表若元素等价则列表完全相等 -/
theorem SortE_equivlistE_eqlistE (al bl : List Nat)
    (h : equivlistA Eq al bl) : al = bl := by
  sorry

/-!
### 练习：Proper_eq_eq (3 星)
-/
theorem Proper_eq_eq (f : Nat → Bool) (x y : Nat) (h : x = y) :
    f x = f y := by
  subst h; rfl

/-!
### 练习：Sremove_elements (3 星)
证明从集合中移除元素与对元素列表进行过滤等价。
-/
theorem Sremove_elements (i : E.t) (s : S.t) (h : S.In i s) :
    S.elements (S.remove i s) =
      s.filter (fun x => if x = i then false else true) := by
  sorry

/-!
### 练习：InA_map_fst_key (2 星)
证明在键列表中的成员关系等价于存在对应键值对。
-/
theorem InA_map_fst_key {A : Type} (j : Nat) (l : List (Nat × A)) :
    j ∈ l.map Prod.fst ↔ ∃ e : A, (j, e) ∈ l := by
  sorry

abbrev Sorted {A : Type} (R : A → A → Prop) (l : List A) : Prop := l.Pairwise R

/-!
### 练习：Sorted_lt_key (3 星)
证明键值对列表按键排序与键列表自身排序等价。
-/
theorem Sorted_lt_key {A : Type} (al : List (Nat × A)) :
    Sorted (fun p1 p2 => p1.1 < p2.1) al ↔
      Sorted (fun x y => x < y) (al.map Prod.fst) := by
  sorry

/-!
### 练习：cardinal_map (4 星)
证明对映射的值进行变换不改变映射的基数（键数量）。
-/
theorem cardinal_map {A B : Type} (f : A → B) (g : M.t A) :
    M.cardinal (M.map f g) = M.cardinal g := by
  sorry

/-!
### 练习：Sremove_cardinal_less (4 星)
证明从非空包含元素的集合中删除一个元素必然严格减小集合基数。
-/
theorem Sremove_cardinal_less (i : S.elt) (s : S.t) (h : S.In i s) :
    S.cardinal (S.remove i s) < S.cardinal s := by
  sorry

/-!
### 练习：Mremove_elements (4 星)
证明映射键的删除与底层元素列表的过滤一致。
-/
theorem Mremove_elements {A : Type} (i : M.key) (s : M.t A) (h : M.In i s) :
    M.elements (M.remove i s) =
      (M.elements s).filter (fun x => if x.1 = i then false else true) := by
  sorry

/-!
### 练习：Mremove_cardinal_less (3 星)
证明从映射中删除已存在的键必然使映射大小严格递减。
-/
theorem Mremove_cardinal_less {A : Type} (i : M.key) (s : M.t A) (h : M.In i s) :
    M.cardinal (M.remove i s) < M.cardinal s := by
  sorry

/-!
### 练习：two_little_lemmas (2 星)
-/
theorem fold_right_rev_left {A B : Type} (f : A → B → A) (l : List B) (i : A) :
    l.foldl f i = l.reverse.foldr (fun x y => f y x) i := by
  sorry

theorem Snot_in_empty (n : S.elt) : ¬ S.In n S.empty := by
  intro h
  cases h

/-!
### 练习：Sin_domain (3 星)
证明节点属于映射定义域当且仅当该节点在映射中有定义。
-/
theorem Sin_domain {A : Type} (n : S.elt) (g : M.t A) :
    S.In n (Mdomain g) ↔ M.In n g := by
  sorry

/-!
## 3. 图的表示与核心算法 (Graph Representation and Kempe's Algorithm)
-/

abbrev node := E.t
abbrev nodeset := S.t
abbrev nodemap (A : Type) := M.t A

/-- 图表示为邻接表（每个节点映射到其邻居集合 `nodeset`） -/
abbrev graph := nodemap nodeset

/-- 查询节点的邻居集合 -/
def adj (g : graph) (i : node) : nodeset :=
  match M.find i g with
  | some a => a
  | none => S.empty

/-- 无向图性质：邻接关系的对称性 -/
def undirected (g : graph) : Prop :=
  ∀ i j, S.In j (adj g i) → S.In i (adj g j)

/-- 无自环性质：节点不与自身相连 -/
def no_selfloop (g : graph) : Prop :=
  ∀ i, ¬ S.In i (adj g i)

/-- 图中所有节点的集合 -/
def nodes (g : graph) : nodeset := Mdomain g

/-- 条件节点子集：筛选满足谓词 `P` 的所有节点 -/
def subset_nodes (P : node → nodeset → Bool) (g : graph) : nodeset :=
  M.fold (fun n adj s => if P n adj then S.add n s else s) g S.empty

/-- 低度数判定：节点的度数小于 $K$ -/
def low_deg (K : Nat) (_ : node) (adj : nodeset) : Bool :=
  S.cardinal adj < K

/-- 从图中删除节点（同时从所有邻接表中剔除该节点） -/
def remove_node (n : node) (g : graph) : graph :=
  M.map (S.remove n) (M.remove n g)

/-!
### 练习：subset_nodes_sub (3 星)
证明条件节点子集必定包含在图的总节点集合中。
-/
theorem subset_nodes_sub (P : node → nodeset → Bool) (g : graph) :
    S.Subset (subset_nodes P g) (nodes g) := by
  sorry

/-!
### 练习：select_terminates (3 星)
证明移除选定节点必然使图的节点数严格减少，从而保证算法终止。
-/
theorem select_terminates (K : Nat) (g : graph) (n : S.elt)
    (h : S.choose (subset_nodes (low_deg K) g) = some n) :
    M.cardinal (remove_node n g) < M.cardinal g := by
  sorry

/-- 简化选择阶段：重复挑选低度数节点移除并压入着色栈 -/
def select (K : Nat) (g : graph) : List node :=
  match S.choose (subset_nodes (low_deg K) g) with
  | some n => n :: select K (remove_node n g)
  | none => []
termination_by M.cardinal g
decreasing_by
  sorry

/-- 着色映射：每个节点分配一个颜色（自然数编码） -/
abbrev coloring := M.t node

/-- 计算给定节点集合已经占用的颜色集合 -/
def colors_of (f : coloring) (s : S.t) : S.t :=
  S.fold (fun n s => match M.find n f with | some c => S.add c s | none => s) s S.empty

/-- 单节点安全着色：在调色板中挑选邻居未占用的颜色赋予节点 `n` -/
def color1 (palette : S.t) (g : graph) (n : node) (f : coloring) : coloring :=
  match S.choose (S.diff palette (colors_of f (adj g n))) with
  | some c => M.add n c f
  | none => f

/-- 全图着色主函数：按选择栈逆序（foldr）依次为节点安全分配颜色 -/
def color (palette : S.t) (g : graph) : coloring :=
  (select (S.cardinal palette) g).foldr (color1 palette g) (M.empty _)

/-!
## 4. 着色算法的正确性规约与证明 (Correctness of the Algorithm)
-/

/-- 着色正确性规范：
1. 分配的颜色属于有效调色板 `palette`；
2. 任意通过边相连的两个邻居节点颜色互不相同（无颜色冲突）。 -/
def coloring_ok (palette : S.t) (g : graph) (f : coloring) : Prop :=
  ∀ i j, S.In j (adj g i) →
    (∀ ci, M.find i f = some ci → S.In ci palette) ∧
    (∀ ci cj, M.find i f = some ci → M.find j f = some cj → ci ≠ cj)

/-!
### 练习：adj_ext (2 星)
证明邻接表查询对外延等价节点具有一致性。
-/
theorem adj_ext (g : graph) (i j : Nat) (h : i = j) :
    S.eq (adj g i) (adj g j) := by
  subst h
  exact ⟨fun _ h => h, fun _ h => h⟩

/-!
### 练习：in_colors_of_1 (3 星)
证明若邻居具有颜色 `c`，则 `c` 必定出现在已占用颜色集合中。
-/
theorem in_colors_of_1 (i : S.elt) (s : S.t) (f : M.t S.elt) (c : S.elt)
    (hi : S.In i s) (hf : M.find i f = some c) :
    S.In c (colors_of f s) := by
  sorry

/-!
### 练习：color_correct (4 星)
无向无自环图的 Kempe 着色算法主正确性定理。
-/
theorem color_correct (palette : S.t) (g : graph)
    (h_loop : no_selfloop g) (h_undir : undirected g) :
    coloring_ok palette g (color palette g) := by
  sorry

/-!
## 5. 寄存器分配实战测试用例 (Testing on an Actual Graph)
-/

/-- 3 色物理寄存器调色板 -/
def palette : S.t := [1, 2, 3].foldr S.add S.empty

/-- 向无向图中添加一条边（双向更新邻接表） -/
def add_edge (e : E.t × E.t) (g : graph) : graph :=
  M.add e.1 (S.add e.2 (adj g e.1))
    (M.add e.2 (S.add e.1 (adj g e.2)) g)

/-- 根据边列表构建冲突图 -/
def mk_graph (el : List (E.t × E.t)) : graph :=
  el.foldr add_edge (M.empty _)

/-- 测试冲突图示例（包含 5 个节点与 7 条冲突边） -/
def G : graph :=
  mk_graph [(5, 6), (6, 2), (5, 2), (1, 5), (1, 2), (2, 4), (1, 4)]

#eval S.elements (Mdomain G)
#eval! M.elements (color palette G)

end VFA.Color
