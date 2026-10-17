import SFLean4.LF.Basics
import SFLean4.LF.Induction
import SFLean4.LF.Lists
import SFLean4.LF.Poly
import SFLean4.LF.Tactics
import SFLean4.LF.Logic
import SFLean4.LF.IndProp

/-!
# 《软件基础》(Software Foundations) 卷一：逻辑基础 (LF)

## 第八章：全域映射与偏映射 (Maps: Total and Partial Maps)

映射（Maps，或称词典 / 符号表 / 关联数组）是日常编程与程序语言理论中最不可或缺的核心数据结构之一。
在后续关于命令式语言语义（`Imp`）、类型系统与程序分析的章节中，我们将无处不在地使用映射来表示：
- 运行时内存状态（State / Store：变量名到数值的绑定）；
- 类型环境（Context / Type Environment：变量名到类型的绑定）；
- 过程与函数符号表。

在本章中，我们将综合运用前几章学到的函数式编程精髓（高阶函数、多态）与逻辑论证技巧（函数外延性公理、分类讨论），
构造两类精巧的映射结构：
1. **全域映射 (Total Maps)**：当查找的键不存在时返回用户预设的**默认值**；
2. **偏映射 (Partial Maps)**：用 `Option A` 作为值类型，未绑定的键自然返回 `none`。

值得特别注意的是：在第三章《Lists》中，我们曾通过键值对列表 `list (id × A)` 来建模偏映射；
而在本章中，我们将直接使用**高阶函数（Higher-Order Functions，即 `String → A`）**来表示映射！
这一表示法极具数学美感与理论优势：
- 两个行为相同的映射在函数外延性公理（Functional Extensionality）下是**严格等价且同一的**（`m1 = m2`）；
- 查找键的操作直接化为**函数作用（Function Application）**，完全免去了链表遍历与递归查找算法；
- 相关的状态修改等式（如覆盖、交换律）可以直接借由函数等式推导，极大简化了语义推理。

---

### 本章核心学习目标：
1. **函数式映射的构造原理**：理解空映射 `t_empty` 与更新函数 `t_update` 如何以高阶函数包装实现；
2. **映射更新的核心代数性质**：
   - 更新立即读取：`(x !-> v ; m) x = v`；
   - 互异键读取无关：`x1 ≠ x2 → (x1 !-> v ; m) x2 = m x2`；
   - 阴影覆盖律 (Shadowing)：连续两次赋给同个键，后一次更新将彻底覆盖前一次；
   - 相同值自等律：更新已有相同值，映射保持不变；
   - 互异键交换律 (Permutation)：给不同键更新赋值的先后次序不影响最终映射状态；
3. **偏映射与映射包含关系 (Map Inclusion)**：掌握 `includedin` 关系及其更新保持定理。
-/

namespace Maps

/- ================================================================== -/
/-! ## 1. 标识符与全域映射 (Identifiers and Total Maps) -/
/- ================================================================== -/

/-!
在 [Lists] 章节中，我们曾专门定义了全新的归纳类型 `id` 作为词典的键；
从本章开始，我们将直接采用标准库的字符串类型 `String` 作为映射的统一键类型。
-/

/-- 全域映射类型：将字符串映射至目标类型 `A` 的一等公民函数 -/
def total_map (A : Type) := String → A

/-- 构造带有默认元素 `v` 的空全域映射 -/
def t_empty {A : Type} (v : A) : total_map A :=
  fun _ => v

/-- 全域映射更新函数：在原映射 `m` 的基础上将键 `x` 重新绑定至新值 `v` -/
def t_update {A : Type} (m : total_map A) (x : String) (v : A) : total_map A :=
  fun x' => if x == x' then v else m x'

/-!
### 1.1 映射语法糖记号 (Notations for Maps)

为了让状态与词典的书写如数学公式般直观，我们引入两套易读的符号：
1. `_ !-> v` 表示所有键均映射至默认值 `v` 的空映射；
2. `x !-> v ; m` 表示在现有映射 `m` 上扩充 `x` 到 `v` 的绑定。
-/

scoped notation:100 "_" " !-> " v:101 => t_empty v
scoped notation:100 (priority := high) x:101 " !-> " v:101 "; " m:100 => t_update m x v

/-- 示例映射：将 "foo" 与 "bar" 映射至 true，其余映射至 false -/
def examplemap : total_map Bool :=
  t_update (t_update (t_empty false) "foo" true) "bar" true

/-- 空映射记号使用示例 -/
def example_empty : total_map Bool := (_ !-> false)

/-- 链式更新语法糖书写的示例映射 -/
def examplemap' : total_map Bool :=
  ("bar" !-> true;
   "foo" !-> true;
   _     !-> false)

/-!
### 1.2 单元测试：映射的函数式求值
-/

theorem update_example1 : examplemap' "baz" = false := by rfl
theorem update_example2 : examplemap' "foo" = true := by rfl
theorem update_example3 : examplemap' "quux" = false := by rfl
theorem update_example4 : examplemap' "bar" = true := by rfl

/- ================================================================== -/
/-! ## 2. 全域映射的基本代数性质 (Properties of Total Maps) -/
/- ================================================================== -/

/-!
#### 练习：1 星, standard, optional (t_apply_empty)
-/

/-- 空全域映射作用于任意键均恒等于其默认值 -/
theorem t_apply_empty (A : Type) (x : String) (v : A) :
    (_ !-> v) x = v := by
  sorry

/-!
#### 练习：2 星, standard, optional (t_update_eq)
-/

/-- 对键 `x` 执行更新后，立即查找 `x` 必得更新值 `v` -/
theorem t_update_eq (A : Type) (m : total_map A) (x : String) (v : A) :
    (x !-> v ; m) x = v := by
  sorry

/-!
#### 练习：2 星, standard, optional (t_update_neq)
-/

/-- 对键 `x1` 执行更新后，查找任意与之不同的键 `x2` 将不受影响 -/
theorem t_update_neq (A : Type) (m : total_map A) (x1 x2 : String) (v : A)
    (h : x1 ≠ x2) :
    (x1 !-> v ; m) x2 = m x2 := by
  sorry

/-!
#### 练习：2 星, standard, optional (t_update_shadow)
-/

/-- 阴影覆盖律：连续对同一个键 `x` 赋值两次，后一次更新将彻底掩盖前一次 -/
theorem t_update_shadow (A : Type) (m : total_map A) (x : String) (v1 v2 : A) :
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m) := by
  sorry

/-!
#### 练习：2 星, standard (t_update_same)
-/

/-- 自等无操作律：若将键 `x` 重新赋值为其在映射 `m` 中原本具有的值，则映射保持不变 -/
theorem t_update_same (A : Type) (m : total_map A) (x : String) :
    (x !-> m x ; m) = m := by
  sorry

/-!
#### 练习：3 星, standard, especially useful (t_update_permute)
-/

/-- 互异键交换律：对两个互异的键分别执行更新，其更新次序可自由调换 -/
theorem t_update_permute (A : Type) (m : total_map A) (v1 v2 : A) (x1 x2 : String)
    (h : x2 ≠ x1) :
    (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m) := by
  sorry

/- ================================================================== -/
/-! ## 3. 偏映射及其代数提升 (Partial Maps) -/
/- ================================================================== -/

/-!
偏映射（Partial Maps）可在全域映射之上直接优雅地定义：
其值域类型为 `Option A`，且未指定项的默认值恒定为 `none`。
-/

/-- 偏映射类型定义 -/
def partial_map (A : Type) := total_map (Option A)

/-- 空偏映射：所有键均映射为 none -/
def empty {A : Type} : partial_map A :=
  t_empty none

/-- 偏映射更新函数：将键 `x` 关联至 `some v` -/
def update {A : Type} (m : partial_map A) (x : String) (v : A) : partial_map A :=
  (x !-> some v ; m)

scoped notation:100 (priority := high) x:101 " |-> " v:101 "; " m:100 => update m x v
scoped notation:100 (priority := high) x:101 " |-> " v:101 => update empty x v

/-- 偏映射书写示例 -/
def examplepmap : partial_map Bool :=
  ("Church" |-> true; "Turing" |-> false)

/-- 空偏映射查找引理 -/
theorem apply_empty (A : Type) (x : String) :
    @empty A x = none := by
  rfl

/-- 偏映射更新立即读取引理 -/
theorem update_eq (A : Type) (m : partial_map A) (x : String) (v : A) :
    (x |-> v ; m) x = some v := by
  apply t_update_eq

/-- 偏映射不同键读取引理 -/
theorem update_neq (A : Type) (m : partial_map A) (x1 x2 : String) (v : A)
    (h : x2 ≠ x1) :
    (x2 |-> v ; m) x1 = m x1 := by
  apply t_update_neq
  exact h

/-- 偏映射阴影覆盖律 -/
theorem update_shadow (A : Type) (m : partial_map A) (x : String) (v1 v2 : A) :
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m) := by
  apply t_update_shadow

/-- 偏映射自等无操作律 -/
theorem update_same (A : Type) (m : partial_map A) (x : String) (v : A)
    (h : m x = some v) :
    (x |-> v ; m) = m := by
  dsimp [update]
  rw [← h]
  apply t_update_same

/-- 偏映射互异键交换律 -/
theorem update_permute (A : Type) (m : partial_map A) (x1 x2 : String) (v1 v2 : A)
    (h : x2 ≠ x1) :
    (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m) := by
  apply t_update_permute
  exact h

/- ================================================================== -/
/-! ## 4. 偏映射的包含关系 (Map Inclusion) -/
/- ================================================================== -/

/-!
在程序语言类型系统（如 PLF 卷的简单类型 Lambda 演算 STLC）中，
我们常常需要表述“上下文 $\Gamma'$ 是上下文 $\Gamma$ 的超集（扩充）”。
这可以通过偏映射的包含谓词 `includedin` 精确刻画。
-/

/-- 映射包含谓词：映射 `m` 中绑定的所有键值对均完整保留在映射 `m'` 中 -/
def includedin {A : Type} (m m' : partial_map A) : Prop :=
  ∀ x v, m x = some v → m' x = some v

/-- 映射包含性在同键同值更新下保持封闭 -/
theorem includedin_update (A : Type) (m m' : partial_map A) (x : String) (vx : A)
    (h : includedin m m') :
    includedin (x |-> vx ; m) (x |-> vx ; m') := by
  intro y vy
  by_cases hxy : x = y
  · subst hxy
    rw [update_eq, update_eq]
    exact id
  · rw [update_neq _ _ _ _ _ hxy]
    rw [update_neq _ _ _ _ _ hxy]
    exact h y vy

end Maps
