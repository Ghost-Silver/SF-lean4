import SFLean4.LF.Basics
import SFLean4.LF.Induction
import SFLean4.LF.Lists
import SFLean4.LF.Poly
import SFLean4.LF.Tactics
import SFLean4.LF.Logic
import SFLean4.LF.IndProp
import SFLean4.LF.Maps
import SFLean4.LF.ProofObjects

set_option linter.defProp false
set_option linter.ambiguousOpen false

/-!
# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)

## 第十章：归纳法则与自定义归纳模式 (IndPrinciples: Induction Principles)

在依赖类型论中，每当我们使用 `inductive` 关键字声明一个全新的归纳数据类型或归纳命题时，
系统都会自动为该类型生成一个全称泛化的推理定理——这就是**归纳法则（Induction Principle / Eliminator）**！

在 Coq 中，类型 `t` 对应的归纳法则被称为 `t_ind`；
在 Lean 4 中，它直接对应于核心计算法则 `t.rec` / `t.recOn`。
我们日常证明中频繁使用的 `induction` 策略，其本质并非什么不可解释的黑魔法，
而仅仅是一个自动化包装器：它在底层通过类型统一（Unification）直接调用并应用了该类型的归纳法则！

---

### 本章核心学习目标：
1. **归纳法则的构造规律**：
   - 理解无参构造子、递归构造子与多分支构造子如何分别生成归纳前提；
   - 掌握非递归类型（如枚举 `time`, `rgb`）与递归类型（如树结构 `booltree`, `tree`）归纳法则的通用推导公式；
2. **多态与参数化归纳**：
   - 深入理解参数（Parameters）与索引（Indices）在归纳法则签名中的根本差异（对比 `le1` 与 `le2`）；
3. **自定义非标归纳模式 (Non-Standard Induction Principles)**：
   - 突破结构性一步递增的局限，学习如何手写显式递归函数构造“按二步递增”（`nat_ind2`）与“嵌套树遍历”（`better_t_tree_ind`）等强力自定义归纳法则；
4. **形式化归纳与非形式化归纳的对比**：
   - 掌握严谨、地道的高质量数学归纳书写模板（包括在数据结构上的结构归纳与在命题证据上的推导树归纳）。
-/

namespace IndPrinciples

open Poly
open Poly.list

/- ================================================================== -/
/-! ## 1. 基础归纳法则与策略底层机制 (Basics) -/
/- ================================================================== -/

/-- 自然数的一阶佩亚诺归纳法则定理 -/
def nat_ind (P : Nat → Prop) (h0 : P 0) (hS : ∀ n, P n → P (n + 1)) (n : Nat) : P n :=
  Nat.recOn n h0 hS

/-- 乘零恒等于零（直接应用 nat_ind 而非 induction 策略证明） -/
theorem mul_0_r' : ∀ n : Nat, n * 0 = 0 := by
  apply nat_ind
  · rfl
  · intro n' ih
    rw [Nat.add_one, Nat.succ_mul, ih]

/-!
#### 练习：2 星, standard (plus_one_r')
-/

/-- 不使用 induction 策略，直接应用归纳法则证明右加一等于后继 -/
theorem plus_one_r' : ∀ n : Nat, n + 1 = n.succ := by
  sorry

/-!
### 1.1 非递归类型的“归纳”法则（穷举分类讨论）
-/

/-- 时间枚举类型 -/
inductive time : Type where
  | day : time
  | night : time

/-!
#### 练习：1 星, standard, optional (rgb)
-/

/-- 三原色枚举类型 -/
inductive rgb : Type where
  | red : rgb
  | green : rgb
  | blue : rgb

/-- 自然数特化单链表 -/
inductive natlist : Type where
  | nnil : natlist
  | ncons (n : Nat) (l : natlist) : natlist

/-- 尾部追加风格的自然数列表 -/
inductive natlist' : Type where
  | nnil' : natlist'
  | nsnoc (l : natlist') (n : Nat) : natlist'

/-!
#### 练习：2 星, standard (booltree_ind)
-/

/-- 叶子与分支均携带布尔值的二叉树 -/
inductive booltree : Type where
  | bt_empty : booltree
  | bt_leaf (b : Bool) : booltree
  | bt_branch (b : Bool) (t1 t2 : booltree) : booltree

def booltree_property_type : Type := booltree → Prop

def base_case (P : booltree_property_type) : Prop :=
  P booltree.bt_empty

def leaf_case (P : booltree_property_type) : Prop :=
  ∀ b : Bool, P (booltree.bt_leaf b)

def branch_case (P : booltree_property_type) : Prop :=
  ∀ (b : Bool) (t1 : booltree), P t1 → ∀ (t2 : booltree), P t2 → P (booltree.bt_branch b t1 t2)

def booltree_ind_type :=
  ∀ (P : booltree_property_type),
    base_case P →
    leaf_case P →
    branch_case P →
    ∀ (b : booltree), P b

/-- 验证手写的 booltree 归纳法则类型完全正确 -/
theorem booltree_ind_type_correct : booltree_ind_type := by
  sorry

/-!
#### 练习：2 星, standard (toy_ind)
-/

/-- 玩具归纳类型 -/
inductive Toy : Type where
  | con1 (b : Bool) : Toy
  | con2 (n : Nat) (t : Toy) : Toy

/-- 验证 Toy 的构造子完备契合其归纳法则 -/
theorem Toy_correct : ∃ (f : Bool → Toy) (g : Nat → Toy → Toy),
    ∀ P : Toy → Prop,
      (∀ b : Bool, P (f b)) →
      (∀ (n : Nat) (t : Toy), P t → P (g n t)) →
      ∀ t : Toy, P t := by
  sorry

/- ================================================================== -/
/-! ## 2. 多态数据类型的归纳法则 (Polymorphism) -/
/- ================================================================== -/

/-!
#### 练习：1 星, standard, optional (tree)
-/

/-- 多态通用二叉树 -/
inductive tree (X : Type) : Type where
  | leaf (x : X) : tree X
  | node (t1 t2 : tree X) : tree X

/-!
#### 练习：1 星, standard, optional (mytype)

问：什么样的归纳类型声明会生成如下归纳法则？
```
mytype_ind :
  ∀ (X : Type) (P : mytype X → Prop),
    (∀ x : X, P (constr1 X x)) →
    (∀ n : Nat, P (constr2 X n)) →
    (∀ m : mytype X, P m → ∀ n : Nat, P (constr3 X m n)) →
    ∀ m : mytype X, P m
```
答：
```lean
inductive mytype (X : Type) : Type where
  | constr1 (x : X) : mytype X
  | constr2 (n : Nat) : mytype X
  | constr3 (m : mytype X) (n : Nat) : mytype X
```
-/

/-!
#### 练习：1 星, standard, optional (foo)

问：什么样的归纳类型声明会生成如下归纳法则？
```
foo_ind :
  ∀ (X Y : Type) (P : foo X Y → Prop),
    (∀ x : X, P (bar X Y x)) →
    (∀ y : Y, P (baz X Y y)) →
    (∀ f1 : Nat → foo X Y, (∀ n : Nat, P (f1 n)) → P (quux X Y f1)) →
    ∀ f2 : foo X Y, P f2
```
答：
```lean
inductive foo (X Y : Type) : Type where
  | bar (x : X) : foo X Y
  | baz (y : Y) : foo X Y
  | quux (f : Nat → foo X Y) : foo X Y
```
-/

/-!
#### 练习：1 星, standard, optional (foo')
-/

/-- 带列表递归分支的归纳类型 -/
inductive foo' (X : Type) : Type where
  | C1 (l : list X) (f : foo' X) : foo' X
  | C2 : foo' X

/- ================================================================== -/
/-! ## 3. 显式归纳假设与命题命名 (Induction Hypotheses) -/
/- ================================================================== -/

def P_m0r (n : Nat) : Prop :=
  n * 0 = 0

def P_m0r' : Nat → Prop :=
  fun n => n * 0 = 0

/-- 显式使用谓词 P_m0r 完成归纳证明 -/
theorem mul_0_r'' : ∀ n : Nat, P_m0r n := by
  intro n
  apply nat_ind
  · rfl
  · intro n' ih
    dsimp [P_m0r]

/-- 加法结合律（对变量 n 归纳） -/
theorem add_assoc' : ∀ n m p : Nat, n + (m + p) = (n + m) + p := by
  intro n m p
  rw [Nat.add_assoc]

/-- 加法交换律（对前置全称量词 n 归纳） -/
theorem add_comm' : ∀ n m : Nat, n + m = m + n := by
  intro n m
  rw [Nat.add_comm]

/-- 加法交换律（引入 n 后对 m 归纳） -/
theorem add_comm'' : ∀ n m : Nat, n + m = m + n := by
  intro n m
  rw [Nat.add_comm]

/-!
#### 练习：1 星, standard, optional (plus_explicit_prop)
-/

def Passoc (n m p : Nat) : Prop := n + (m + p) = (n + m) + p
def Pcomm (n m : Nat) : Prop := n + m = m + n

/-- 使用显式命题 Passoc 重写加法结合律证明 -/
theorem add_assoc'' : ∀ n m p : Nat, Passoc n m p := by
  sorry

/-- 使用显式命题 Pcomm 重写加法交换律证明 -/
theorem add_comm''' : ∀ n m : Nat, Pcomm n m := by
  sorry

/- ================================================================== -/
/-! ## 4. 命题上的归纳法则 (Induction Principles for Propositions) -/
/- ================================================================== -/

/-- 备选偶数定义 -/
inductive ev' : Nat → Prop where
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m)

/-- 直接在偶数证据上执行归纳 -/
theorem ev_ev' : ∀ n, ProofObjects.ev n → ev' n := by
  intro n h
  induction h with
  | ev_0 => exact ev'.ev'_0
  | ev_SS m hm ih =>
    have hsum := ev'.ev'_sum 2 m ev'.ev'_2 ih
    exact Nat.add_comm 2 m ▸ hsum

/-- 两个参数均作为索引的小于等于定义（归纳法则更为繁琐） -/
inductive le1 : Nat → Nat → Prop where
  | le1_n : ∀ n, le1 n n
  | le1_S : ∀ n m, le1 n m → le1 n (m + 1)

/-- 将左侧端点作为全局参数的小于等于定义（推荐做法，归纳法则极度精简） -/
inductive le2 (n : Nat) : Nat → Prop where
  | le2_n : le2 n n
  | le2_S m (H : le2 n m) : le2 n (m + 1)

/- ================================================================== -/
/-! ## 5. 显式构造归纳证明项 (Explicit Proof Objects for Induction) -/
/- ================================================================== -/

/-- 递归函数显式构造自然数归纳证明 -/
def build_proof
    (P : Nat → Prop)
    (evPO : P 0)
    (evPS : ∀ n : Nat, P n → P (n + 1))
    (n : Nat) : P n :=
  match n with
  | 0 => evPO
  | k + 1 => evPS k (build_proof P evPO evPS k)

/-- 精简版自然数归纳法则别名 -/
def nat_ind_tidy := build_proof

/-- 两步跨度（by twos）非标自然数归纳法则 -/
def nat_ind2 :
    ∀ (P : Nat → Prop),
    P 0 →
    P 1 →
    (∀ n : Nat, P n → P (n + 2)) →
    ∀ n : Nat, P n :=
  fun P P0 P1 PSS =>
    let rec f (n : Nat) : P n :=
      match n with
      | 0 => P0
      | 1 => P1
      | n' + 2 => PSS n' (f n')
    f

def even (n : Nat) : Bool :=
  match n with
  | 0 => true
  | 1 => false
  | n' + 2 => even n'

/-- 利用 nat_ind2 两步归纳优雅秒杀布尔偶数到归纳偶数的蕴含 -/
theorem even_ev : ∀ n, even n = true → ProofObjects.ev n := by
  intro n
  induction n using nat_ind2
  · intro _; exact ProofObjects.ev.ev_0
  · intro contra; cases contra
  · intro n' ih h
    dsimp [even] at h
    exact ProofObjects.ev.ev_SS n' (ih h)

/-!
#### 练习：4 星, standard, optional (t_tree)
-/

/-- 分支打包为三元组的二叉树 -/
inductive t_tree (X : Type) : Type where
  | t_leaf : t_tree X
  | t_branch (node : t_tree X × X × t_tree X) : t_tree X

/-- 树镜像翻转函数 -/
def reflect {X : Type} : t_tree X → t_tree X
  | .t_leaf => .t_leaf
  | .t_branch (l, v, r) => .t_branch (reflect r, v, reflect l)

/-- 针对打包三元组树的更强自定义归纳法则类型 -/
def better_t_tree_ind_type : Prop :=
  ∀ (X : Type) (P : t_tree X → Prop),
    P t_tree.t_leaf →
    (∀ (v : X) (l : t_tree X), P l → ∀ (r : t_tree X), P r → P (t_tree.t_branch (l, v, r))) →
    ∀ (t : t_tree X), P t

/-- 显式模式匹配构造自定义强归纳法则 -/
def better_t_tree_ind : better_t_tree_ind_type :=
  sorry

/-- 证明镜像翻转是对合变换（Involution） -/
theorem reflect_involution : ∀ (X : Type) (t : t_tree X),
    reflect (reflect t) = t := by
  sorry

end IndPrinciples
