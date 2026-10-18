import SFLean4.VFA.Perm
import SFLean4.VFA.Priqueue

/-!
# 二项堆：快速可合并优先队列 (Binom: Binomial Queues)

优先队列（Priority Queue）是计算机科学中最核心的抽象数据类型之一。
在第十四章中，我们使用了朴素的无序列表实现，其 `delete_max` 与 `merge` 需耗费线性时间 $O(N)$。
若使用普通的二叉堆（Binary Heap），`insert` 与 `delete_max` 可达对数时间 $O(\log N)$，
但两个堆的合并 `merge` 仍需将一个堆拆散依次插入另一个，耗时 $O(N \log N)$。

**二项队列（Binomial Queue，又称二项堆）** 巧妙地将数值的二进制算术（位加法与进位 `carry`）
与森林结构结合起来，实现了真正的**对数时间可合并优先队列**：
- `empty`: 常数时间 $O(1)$
- `insert`: 对数时间 $O(\log N)$（均摊常数时间）
- `delete_max`: 对数时间 $O(\log N)$
- `merge`: 对数时间 $O(\log N)$

本章实现纯函数式二项堆，并完成其在规范签名 `PRIQUEUE` 下的完全形式化验证。
-/

namespace VFA.Binom

open VFA.Perm
open VFA.Priqueue

namespace BinomQueue

abbrev key := Nat

/-- 二项树（Binomial Tree）归纳类型：
每个节点包含一个键以及左右子树引用（采用“左孩子-右兄弟”表示法） -/
inductive tree : Type where
  | Node : key → tree → tree → tree
  | Leaf : tree
deriving Repr, DecidableEq

/-- 二项队列是由二项树构成的列表（森林）：
第 $i$ 个位置要么是 `Leaf`，要么是一棵恰好含有 $2^i$ 个节点的 2 次幂最大堆（Power-of-2 Heap） -/
abbrev priqueue := List tree

/-- 空队列 -/
def empty : priqueue := []

/-- 将两棵相同高度的 2 次幂堆合并为一棵更高一阶的堆（二项树的结合）：
键值较大的节点作为新根，较小的节点作为其左子树挂载 -/
def smash (t u : tree) : tree :=
  match t, u with
  | tree.Node x t1 tree.Leaf, tree.Node y u1 tree.Leaf =>
    if x >? y then
      tree.Node x (tree.Node y u1 t1) tree.Leaf
    else
      tree.Node y (tree.Node x t1 u1) tree.Leaf
  | _, _ => tree.Leaf

/-- 二项树森林的进位加法运算（类似二进制数的逐位加 1 与进位传播） -/
def carry (q : List tree) (t : tree) : List tree :=
  match q, t with
  | [], tree.Leaf => []
  | [], _ => [t]
  | tree.Leaf :: q', _ => t :: q'
  | u :: q', tree.Leaf => u :: q'
  | u :: q', _ => tree.Leaf :: carry q' (smash t u)

/-- 插入操作：将单节点树通过 `carry` 进位链并入二项队列 -/
def insert (x : key) (q : priqueue) : priqueue :=
  carry q (tree.Node x tree.Leaf tree.Leaf)

#eval [3, 1, 4, 1, 5, 9, 2, 3, 5].foldl (fun q x => insert x q) empty

/-- 队列合并算法：类似两个多位二进制数的按位相加与进位（全加器逻辑） -/
def join (p q : priqueue) (c : tree) : priqueue :=
  match p, q, c with
  | [], _, _ => carry q c
  | _, [], _ => carry p c
  | tree.Leaf :: p', tree.Leaf :: q', _ => c :: join p' q' tree.Leaf
  | tree.Leaf :: p', q1 :: q', tree.Leaf => q1 :: join p' q' tree.Leaf
  | tree.Leaf :: p', q1 :: q', tree.Node _ _ _ => tree.Leaf :: join p' q' (smash c q1)
  | p1 :: p', tree.Leaf :: q', tree.Leaf => p1 :: join p' q' tree.Leaf
  | p1 :: p', tree.Leaf :: q', tree.Node _ _ _ => tree.Leaf :: join p' q' (smash c p1)
  | p1 :: p', q1 :: q', _ => c :: join p' q' (smash p1 q1)
termination_by p.length + q.length

/-- 辅助解包：将最大堆根节点下的子树解构成逆序的二项队列 -/
def unzip (t : tree) (cont : priqueue → priqueue) : priqueue :=
  match t with
  | tree.Node x t1 t2 => unzip t2 (fun q => tree.Node x t1 tree.Leaf :: cont q)
  | tree.Leaf => cont []

/-- 从单棵二项树中提取除去根节点后的剩余森林 -/
def heap_delete_max (t : tree) : priqueue :=
  match t with
  | tree.Node _ t1 tree.Leaf => unzip t1 (fun u => u)
  | _ => []

/-- 辅助函数：在森林中遍历寻找最大键 -/
def find_max' (current : key) (q : priqueue) : key :=
  match q with
  | [] => current
  | tree.Leaf :: q' => find_max' current q'
  | tree.Node x _ _ :: q' =>
    find_max' (if x >? current then x else current) q'

/-- 寻找森林中的全局最大键 -/
def find_max (q : priqueue) : Option key :=
  match q with
  | [] => none
  | tree.Leaf :: q' => find_max q'
  | tree.Node x _ _ :: q' => some (find_max' x q')

/-- 分割森林：定位最大键所在的二项树，将其余树与该树解包出的子树分开 -/
def delete_max_aux (m : key) (p : priqueue) : priqueue × priqueue :=
  match p with
  | tree.Leaf :: p' =>
    let (j, k) := delete_max_aux m p'
    (tree.Leaf :: j, k)
  | tree.Node x t1 tree.Leaf :: p' =>
    if m >? x then
      let (j, k) := delete_max_aux m p'
      (tree.Node x t1 tree.Leaf :: j, k)
    else
      (tree.Leaf :: p', heap_delete_max (tree.Node x t1 tree.Leaf))
  | _ => ([], [])

/-- 删除最大键：定位最大树，将其分解为子森林，然后用 `join` 与原森林其余部分合并 -/
def delete_max (q : priqueue) : Option (key × priqueue) :=
  match find_max q with
  | none => none
  | some m =>
    let (p', q') := delete_max_aux m q
    some (m, join p' q' tree.Leaf)

/-- 两队列合并（初始进位树为空） -/
def merge (p q : priqueue) : priqueue :=
  join p q tree.Leaf

/-!
## 2. 结构特征谓词与表示不变量 (Characterization Predicates)
-/

/-- `pow2heap' n m t` 表示 `t` 是一棵深度为 `n` 的完全二叉树，且其所有键均不超过 `m` -/
def pow2heap' (n : Nat) (m : key) (t : tree) : Prop :=
  match n, m, t with
  | 0, _, tree.Leaf => True
  | 0, _, tree.Node _ _ _ => False
  | _ + 1, _, tree.Leaf => False
  | n' + 1, m, tree.Node k l r =>
    m ≥ k ∧ pow2heap' n' k l ∧ pow2heap' n' m r

/-- `pow2heap n t` 表示 `t` 是一棵深度为 `n` 的 2 次幂最大堆 -/
def pow2heap (n : Nat) (t : tree) : Prop :=
  match t with
  | tree.Node m t1 tree.Leaf => pow2heap' n m t1
  | _ => False

/-- `priq' i l` 表示列表 `l` 是从第 `i` 位起的合法二项堆后缀 -/
def priq' (i : Nat) (l : List tree) : Prop :=
  match l with
  | [] => True
  | t :: l' => (t = tree.Leaf ∨ pow2heap i t) ∧ priq' (i + 1) l'

/-- 二项堆的全局表示不变量：从第 0 位起满足二项队列性质 -/
def priq (q : priqueue) : Prop :=
  priq' 0 q

/-!
## 3. 各核心操作对表示不变量的维护 (Preserving the Representation Invariant)
-/

/-!
### 练习：empty_priq (1 星)
证明空二项堆天然满足表示不变量。
-/
theorem empty_priq : priq empty := by
  sorry

/-!
### 练习：smash_valid (2 星)
证明两棵 $n$ 阶堆合并后得到合法的 $n+1$ 阶堆。
-/
theorem smash_valid (n : Nat) (t u : tree)
    (ht : pow2heap n t) (hu : pow2heap n u) :
    pow2heap (n + 1) (smash t u) := by
  sorry

/-!
### 练习：carry_valid (3 星)
证明带进位加法维持森林后缀的二项堆性质。
-/
theorem carry_valid (n : Nat) (q : List tree) (hq : priq' n q)
    (t : tree) (ht : t = tree.Leaf ∨ pow2heap n t) :
    priq' n (carry q t) := by
  sorry

/-!
### 练习：insert_valid (2 星，可选)
证明插入操作维护二项堆不变量。
-/
theorem insert_priq (x : key) (q : priqueue) (h : priq q) :
    priq (insert x q) := by
  sorry

/-!
### 练习：join_valid (3 星，可选)
证明多位合并运算维持二项堆不变量。
-/
theorem join_valid (p q : priqueue) (c : tree) (n : Nat)
    (hp : priq' n p) (hq : priq' n q) (hc : c = tree.Leaf ∨ pow2heap n c) :
    priq' n (join p q c) := by
  sorry

/-- 合并操作保持表示不变量 -/
theorem merge_priq (p q : priqueue) (hp : priq p) (hq : priq q) :
    priq (merge p q) := by
  unfold merge
  apply join_valid p q tree.Leaf 0 hp hq
  left; rfl

/-!
### 练习：delete_max_Some_priq (5 星，可选)
证明删除最大元后剩余队列仍然是合法的二项堆。
-/
theorem delete_max_Some_priq (p q : priqueue) (k : key)
    (hp : priq p) (hdel : delete_max p = some (k, q)) :
    priq q := by
  sorry

/-!
## 4. 抽象关系 (The Abstraction Relation)

我们将二项堆抽象为其所有包含元素的无序多重集（用置换等价的列表表示）。
-/

/-- 单棵树中包含的所有元素列表关系（允许任意置换） -/
inductive tree_elems : tree → List key → Prop where
  | tree_elems_leaf : tree_elems tree.Leaf []
  | tree_elems_node : ∀ bl br v tl tr b,
      tree_elems tl bl →
      tree_elems tr br →
      Permutation b (v :: bl ++ br) →
      tree_elems (tree.Node v tl tr) b

/-!
### 练习：priqueue_elems (3 星)
定义二项队列（森林）与其包含元素的多重集抽象关系。
-/
inductive priqueue_elems : List tree → List key → Prop where
  | nil : priqueue_elems [] []
  | cons : ∀ (t : tree) (q : List tree) (bt bq b : List key),
      tree_elems t bt →
      priqueue_elems q bq →
      Permutation b (bt ++ bq) →
      priqueue_elems (t :: q) b

def manual_grade_for_priqueue_elems : Option (Nat × String) := none

/-- 优先队列的抽象关系定义 -/
def Abs (p : priqueue) (al : List key) : Prop :=
  priqueue_elems p al

/-!
## 5. 抽象关系的健全性引理 (Sanity Checks on the Abstraction Relation)
-/

/-!
### 练习：tree_elems_ext (2 星)
外延性引理：若 `e1` 置换等价于 `e2`，则树元素关系可传递。
-/
theorem tree_elems_ext (t : tree) (e1 e2 : List key)
    (hp : Permutation e1 e2) (ht : tree_elems t e1) :
    tree_elems t e2 := by
  sorry

/-!
### 练习：tree_perm (2 星)
两组不同的元素列表若都代表同一棵树，则彼此必然互为置换。
-/
theorem tree_perm (t : tree) (e1 e2 : List key)
    (h1 : tree_elems t e1) (h2 : tree_elems t e2) :
    Permutation e1 e2 := by
  sorry

/-!
### 练习：priqueue_elems_ext (2 星)
二项堆森林元素关系对外延置换封闭。
-/
theorem priqueue_elems_ext (q : List tree) (e1 e2 : List key)
    (hp : Permutation e1 e2) (hq : priqueue_elems q e1) :
    priqueue_elems q e2 := by
  sorry

/-!
### 练习：abs_perm (2 星)
证明二项堆抽象关系的良定义性（任意两组抽象结果必然互为置换）。
-/
theorem abs_perm (p : priqueue) (al bl : List key)
    (hp : priq p) (ha : Abs p al) (hb : Abs p bl) :
    Permutation al bl := by
  sorry

/-!
### 练习：can_relate (2 星)
证明任何合法的二项堆都可以关联到某个元素多重集列表。
-/
theorem tree_can_relate (t : tree) : ∃ al, tree_elems t al := by
  sorry

theorem can_relate (p : priqueue) (hp : priq p) :
    ∃ al, Abs p al := by
  sorry

/-!
## 6. 各核心操作保持抽象关系 (Preserving the Abstraction Relation)
-/

/-!
### 练习：empty_relate (1 星)
证明空堆抽象对应空列表。
-/
theorem empty_relate : Abs empty [] := by
  sorry

/-!
### 练习：smash_elems (3 星)
证明两树合并后的元素集为两树原元素集的并集（拼接）。
-/
theorem smash_elems (n : Nat) (t u : tree) (bt bu : List key)
    (ht : pow2heap n t) (hu : pow2heap n u)
    (ebt : tree_elems t bt) (ebu : tree_elems u bu) :
    tree_elems (smash t u) (bt ++ bu) := by
  sorry

/-!
### 练习：carry_elems (4 星，可选)
证明带进位加法产生的森林包含原森林与进位树的所有元素。
-/
theorem carry_elems (n : Nat) (q : List tree) (hq : priq' n q)
    (t : tree) (ht : t = tree.Leaf ∨ pow2heap n t)
    (eq et : List key) (heq : priqueue_elems q eq) (het : tree_elems t et) :
    priqueue_elems (carry q t) (eq ++ et) := by
  sorry

/-!
### 练习：insert_elems (2 星，可选)
证明插入新元素操作满足抽象关系。
-/
theorem insert_relate (p : priqueue) (al : List key) (k : key)
    (hp : priq p) (ha : Abs p al) :
    Abs (insert k p) (k :: al) := by
  sorry

/-!
### 练习：join_elems (4 星，可选)
证明两森林合并产生的元素集为两森林与进位树的并集。
-/
theorem join_elems (p q : priqueue) (c : tree) (n : Nat)
    (hp : priq' n p) (hq : priq' n q) (hc : c = tree.Leaf ∨ pow2heap n c)
    (pe qe ce : List key)
    (hpe : priqueue_elems p pe) (hqe : priqueue_elems q qe) (hce : tree_elems c ce) :
    priqueue_elems (join p q c) (ce ++ pe ++ qe) := by
  sorry

/-!
### 练习：merge_relate (2 星，可选)
证明队列合并满足抽象关系。
-/
theorem merge_relate (p q : priqueue) (pl ql al : List key)
    (hp : priq p) (hq : priq q)
    (hap : Abs p pl) (haq : Abs q ql) (hal : Abs (merge p q) al) :
    Permutation al (pl ++ ql) := by
  sorry

/-!
### 练习：delete_max_None_relate (5 星，可选)
证明队列为空当且仅当删除操作返回 `none`。
-/
theorem delete_max_None_relate (p : priqueue) (hp : priq p) :
    (Abs p [] ↔ delete_max p = none) := by
  sorry

/-!
### 练习：delete_max_Some_relate (5 星，可选)
证明删除最大元操作返回的最大键确实大于等于队列中所有剩余元素，
且所有元素构成了原元素集的一个置换拆分。
-/
theorem delete_max_Some_relate (p q : priqueue) (k : key) (pl ql : List key)
    (hp : priq p) (hap : Abs p pl)
    (hdel : delete_max p = some (k, q)) (haq : Abs q ql) :
    Permutation pl (k :: ql) ∧ Forall (fun x => k ≥ x) ql := by
  sorry

end BinomQueue

/-!
### 练习：binom_measurement (5 星，可选思考题)
在实际运行性能中，由于二项队列的合并为 $O(\log N)$，而普通堆为 $O(N \log N)$，
当大量进行队列合并操作时，二项堆表现出极显著的渐近优势。
-/
def manual_grade_for_binom_measurement : Option (Nat × String) := none

end VFA.Binom
