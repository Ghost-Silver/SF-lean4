---
title: "Maps: 全映射与偏映射：高阶函数模型与状态机基础"
---

```lean
import SFLean4.VFA.Perm

namespace VFA.Maps

open VFA.Perm
```

# 《软件基础》(Software Foundations) 卷三：函数式算法验证 (VFA)

## 第八章：全映射与偏映射 (Maps: Total and Partial Maps)

在第一卷《逻辑基础》的 `Lists` 章节中，我们曾通过键值对列表实现映射。
而在算法验证与高级数据结构的规约中，将映射建模为**函数（Function）**具有极大的优势：
- 函数天然支持**外延性（Extensionality）**：两个映射当且仅当在所有输入键上取值相等时彼此相等；
- 无需处理列表实现中的重复键（Shadowing）、键排列顺序等底层冗余细节；
- 查找操作直接退化为最直观的**函数调用（Function Application）**。

在 VFA 中，为专注于查找树和算法本身，所有映射的键统一采用自然数 `Nat`。

---

## 1. 全映射 (Total Maps)

全映射是指任何键均有明确对应值的映射。创建全映射时需提供一个默认元素，
当未曾特意设定某个键的值时，直接返回该默认元素。

```lean
/-- 全映射类型：由自然数键映射到类型 `A` 的值 -/
def total_map (A : Type) : Type := Nat → A

/-- 构造空全映射：对所有键均返回默认值 `v` -/
def t_empty {A : Type} (v : A) : total_map A :=
  fun _ => v

/-- 全映射更新：若查询键等于更新键 `x` 则返回新值 `v`，否则保持原映射 `m` 的取值 -/
def t_update {A : Type} (m : total_map A) (x : Nat) (v : A) : total_map A :=
  fun x' => if x = x' then v else m x'

/-- 构造映射示例：键 3 映射到 true，键 1 与其余所有键映射到 false -/
def examplemap : total_map Bool :=
  t_update (t_update (t_empty false) 1 false) 3 true

example : examplemap 0 = false := by rfl
example : examplemap 1 = false := by rfl
example : examplemap 2 = false := by rfl
example : examplemap 3 = true  := by rfl
```

### 🎯 练习：全映射基础引理

```lean
/-- #### 练习：1 星 (t_apply_empty)
空全映射在任何键上均返回初始默认值。 -/
theorem t_apply_empty : ∀ (A : Type) (x : Nat) (v : A),
    t_empty v x = v := by
  sorry

/-- #### 练习：1 星 (t_update_eq)
对键 `x` 赋予新值 `v` 后立即查询 `x`，必然得到 `v`。 -/
theorem t_update_eq : ∀ (A : Type) (m : total_map A) (x : Nat) (v : A),
    t_update m x v x = v := by
  sorry

/-- #### 练习：1 星 (t_update_neq)
对键 `x1` 进行更新不会干扰对不同键 `x2` 的查询结果。 -/
theorem t_update_neq : ∀ (X : Type) (v : X) (x1 x2 : Nat) (m : total_map X),
    x1 ≠ x2 → t_update m x1 v x2 = m x2 := by
  sorry

/-- #### 练习：1 星 (t_update_shadow)
连续对同一个键 `x` 两次更新，第一次更新被彻底遮蔽覆盖。 -/
theorem t_update_shadow : ∀ (A : Type) (m : total_map A) (v1 v2 : A) (x : Nat),
    t_update (t_update m x v1) x v2 = t_update m x v2 := by
  sorry

/-- #### 练习：1 星 (t_update_same)
将键 `x` 更新为其已有的取值 `m x`，映射保持不变。 -/
theorem t_update_same : ∀ (X : Type) (x : Nat) (m : total_map X),
    t_update m x (m x) = m := by
  sorry

/-- #### 练习：1 星 (t_update_permute)
对两个不同的键进行更新，更新的先后次序无关紧要。 -/
theorem t_update_permute : ∀ (X : Type) (v1 v2 : X) (x1 x2 : Nat) (m : total_map X),
    x2 ≠ x1 →
    t_update (t_update m x2 v2) x1 v1 = t_update (t_update m x1 v1) x2 v2 := by
  sorry
```

---
## 2. 偏映射 (Partial Maps)

偏映射用于表示某些键可能不存在（查找失败）的情形。
在函数式范式下，偏映射优雅地表达为值类型为 `Option A`、默认值为 `none` 的全映射。

```lean
/-- 偏映射：将键映射到 `Option A` -/
def partial_map (A : Type) : Type := total_map (Option A)

/-- 空偏映射：所有键均映射至 `none` -/
def empty {A : Type} : partial_map A :=
  t_empty none

/-- 偏映射更新：将键 `x` 绑定到有效值 `some v` -/
def update {A : Type} (m : partial_map A) (x : Nat) (v : A) : partial_map A :=
  t_update m x (some v)

/-- 空偏映射查询任意键均得到 `none` -/
theorem apply_empty : ∀ (A : Type) (x : Nat), @empty A x = none := by
  intro A x
  rfl

/-- 偏映射更新后查询对应键得到 `some v` -/
theorem update_eq : ∀ (A : Type) (m : partial_map A) (x : Nat) (v : A),
    update m x v x = some v := by
  intro A m x v
  dsimp [update, t_update]
  simp

/-- 偏映射更新不影响不同键的查询 -/
theorem update_neq : ∀ (X : Type) (v : X) (x1 x2 : Nat) (m : partial_map X),
    x2 ≠ x1 → update m x2 v x1 = m x1 := by
  intro X v x1 x2 m h
  dsimp [update, t_update]
  by_cases h1 : x2 = x1
  · contradiction
  · simp [h1]

/-- 偏映射相同键的新更新覆盖旧更新 -/
theorem update_shadow : ∀ (A : Type) (m : partial_map A) (v1 v2 : A) (x : Nat),
    update (update m x v1) x v2 = update m x v2 := by
  intro A m v1 v2 x
  funext k
  dsimp [update, t_update]
  split <;> rfl

/-- 将偏映射已有绑定重新赋予原值，映射不变 -/
theorem update_same : ∀ (X : Type) (v : X) (x : Nat) (m : partial_map X),
    m x = some v → update m x v = m := by
  intro X v x m h
  funext k
  dsimp [update, t_update]
  by_cases hk : x = k
  · subst hk; simp; exact h.symm
  · simp [hk]

/-- 对偏映射不同键的更新次序可交换 -/
theorem update_permute : ∀ (X : Type) (v1 v2 : X) (x1 x2 : Nat) (m : partial_map X),
    x2 ≠ x1 →
    update (update m x2 v2) x1 v1 = update (update m x1 v1) x2 v2 := by
  intro X v1 v2 x1 x2 m h
  funext k
  dsimp [update, t_update]
  by_cases hk1 : x1 = k
  · subst hk1
    by_cases hk2 : x2 = x1
    · contradiction
    · simp [hk2]
  · by_cases hk2 : x2 = k
    · subst hk2
      simp [Ne.symm h]
    · simp [hk1, hk2]

end VFA.Maps
```
