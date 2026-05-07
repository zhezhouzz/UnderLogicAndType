# Store proof refactoring and lookup extensionality

## 背景

在证明 `ChoicePrelude/examples/StoreExamples.v` 里的 store compatibility 例子时，
直接在 example 文件中展开 `store_restrict` / `map_restrict` 会遇到两类干扰：

- `Store` 是 `Section Store` 里的别名，离开定义文件后有时会让 typeclass inference
  错把 `Store` 当作 map functor，而不是具体的 `gmap atom V`。
- 对 concrete example 使用 `vm_compute` 很方便，但对
  `store_compat : forall key/value, ...` 这种全称性质，计算不会自动完成 key 的分情况讨论。

最终更稳的做法是：把通用 lemma 移到 `ChoicePrelude/Store.v`，在定义所在的 section
里证明；example 文件只调用这些 lemma。

## 判断一个 lemma 是否该移出 example

如果 lemma 描述的是定义本身的通用性质，而不是某个具体例子的事实，就应该放在定义附近。

适合放到 `Store.v` 的例子：

```coq
Lemma disj_dom_store_compat s1 s2 :
  dom s1 ∩ dom s2 = ∅ -> store_compat s1 s2.

Lemma store_compat_spec s1 s2 :
  store_compat s1 s2 <->
  store_restrict s1 (dom s1 ∩ dom s2) =
  store_restrict s2 (dom s1 ∩ dom s2).
```

不适合放到 `Store.v` 的例子：

```coq
Example restrict_xy_to_x :
  store_restrict store_x1_y2 ({['x]}) = store_x1.
```

后者依赖 example 里具体选的 atom/value，留在 examples 中更合适。

## 常用证明模式

### 1. 证明两个 finite maps 相等

优先使用 lookup extensionality：

```coq
apply map_eq. intros x.
```

如果需要比较 `option` lookup 的两个方向，可以再使用：

```coq
rewrite option_eq. intros v.
```

这比 destruct 两边 lookup 后再 rewrite 更稳，因为 destruct 会把目标中的 lookup subterm
化简掉，后续普通 `rewrite Hlookup` 经常找不到原来的 subterm。

### 2. 对 restricted map 的 lookup 做双向展开

对 `store_restrict`，定义层面最终是 `filter`。正向已有：

```coq
Lemma store_restrict_lookup_some s X x y :
  store_restrict s X !! x = Some y -> x ∈ X /\ s !! x = Some y.
```

如果需要反向，先在 `Store.v` 里补通用 lemma：

```coq
Lemma store_restrict_lookup_some_2 s X x y :
  s !! x = Some y ->
  x ∈ X ->
  store_restrict s X !! x = Some y.
```

然后 examples 和后续证明都调用它，避免每次重新展开 `filter`。

### 3. `setoid_rewrite` 比普通 `rewrite` 更适合的情况

当目标中有很多由 typeclass notation 生成的表达式，或目标经过 `map_eq` / `option_eq`
后包含隐藏在 relation 下的 lookup/filter 结构，普通 `rewrite` 可能找不到 subterm。

可尝试：

```coq
setoid_rewrite map_lookup_filter_Some.
```

这在 `store_compat_spec` 的正向证明里比手动 destruct 两个 restricted lookups 更稳：

```coq
apply map_eq. intros x.
rewrite option_eq. intros v.
unfold store_restrict, map_restrict.
setoid_rewrite map_lookup_filter_Some.
simpl. split.
```

### 4. 显式化 overloaded 目标

当 Rocq 报错类似：

```text
The term "s" has type "StoreN" while it is expected to have type "Type".
Could not find an instance for FMap (@Store)
```

通常是隐式参数或 section-level alias 干扰了 typeclass inference。

一次性调试时可以用 `change` 看清目标的 convertible normal form，例如：

```coq
change (@map_restrict atom _ nat s X !! k = Some v).
```

但 proof script 里不要反复留下这种 `change`。如果这个 pattern 频繁出现，优先：

- 把 lemma 上移到定义所在文件；
- 或者写一个窄的 normalization tactic，用 `replace ... by ...`、`rewrite`、
  `setoid_rewrite` 暴露 canonical form；
- 再让主证明调用这个 tactic/lemma。

### 5. Nested restriction: choose the direction explicitly

For goals involving a projected store from an extension world, the useful shape
is often:

```coq
replace (store_restrict σ X)
  with (store_restrict (store_restrict σ D) X).
2:{ rewrite store_restrict_restrict.
    replace (D ∩ X) with X by set_solver.
    reflexivity. }
```

This direction lets you reuse lemmas whose premise is a store in the smaller
world `D`.  Trying to `rewrite <- store_restrict_restrict` directly often fails
because the goal contains `store_restrict σ X`, not the normalized
`store_restrict σ (D ∩ X)` subterm.

When proving that `store_restrict σ D = σ` from a world-store domain fact
`dom σ = D`, use `store_restrict_idemp` with the equality in the right
direction:

```coq
symmetry. apply store_restrict_idemp.
intros z Hz. rewrite <- Hdomσ. exact Hz.
```

## Store compatibility 的推荐 spec

`store_compat s1 s2` 的自然含义是：

> 两个 store 在共同 domain 上给出相同 value。

因此最干净的 spec 是：

```coq
store_compat s1 s2 <->
store_restrict s1 (dom s1 ∩ dom s2) =
store_restrict s2 (dom s1 ∩ dom s2)
```

不要写成“disjoint 或存在 singleton overlap store”。共同 overlap 可以包含多个 key，
并且 disjoint 情况已经由等式 spec 覆盖，此时两边 restriction 都是空 map。

## Example 文件里的写法

Example 文件应尽量短：

```coq
Example compatible_disjoint_stores :
  store_compat store_x1 store_y2.
Proof.
  apply disj_dom_store_compat.
  vm_compute. reflexivity.
Qed.
```

这样 example 表达的是直觉，而不是重复展开底层 finite-map proof。

## 把 normal form 调整收敛到小 tactic

如果同一类 normal-form 调整在多个 proof 中重复出现，不要急着写一个会全局展开所有
定义的 large tactic。更稳的做法是：

1. 先加小 lemma，把 semantic fact 命名出来；
2. 再加参数化的小 tactic，把必要的 `replace`/`rewrite` 收在 tactic 内部；
3. 最后用中间 lemma 改写主证明。

例如 world/resource 层可以先证明：

```coq
Lemma wfworld_store_dom (w : WfWorld) σ :
  w σ -> dom σ = world_dom (w : World).

Lemma wfworld_store_restrict_dom (w : WfWorld) σ X :
  w σ -> dom (store_restrict σ X) = world_dom (w : World) ∩ X.
```

然后写很窄的 tactic：

```coq
Ltac normalize_store_overlap H w1 σ1 Hσ1 w2 σ2 Hσ2 :=
  replace (dom σ1 ∩ dom σ2)
    with (world_dom (w1 : World) ∩ world_dom (w2 : World)) in H
    by (rewrite (wfworld_store_dom w1 σ1 Hσ1);
        rewrite (wfworld_store_dom w2 σ2 Hσ2);
        reflexivity).
```

这种 tactic 虽然需要显式传参数，但它的行为可预测：只处理一个 hypothesis，
不会意外展开别的 map/world 定义。后续如果发现很多 proof 都需要同样的 overlap
normal form，再把它包装成 lemma，例如：

```coq
Lemma world_compat_store_restrict_overlap ... :
  store_restrict σ1 X = store_restrict σ2 X.
```

## Basic-world typing is local to a footprint

`basic_world_formula Σ X` only gives typing/closedness/lc facts for the
projection to `X`.  Do not try to prove that an arbitrary store in a larger
world is wholly closed or typed: the world may contain coordinates outside
`X`, and those are intentionally unconstrained.

Preferred shape:

```coq
store_has_type_on Σ X (store_restrict σ X)
closed_env (store_restrict σ X)
lc_env (store_restrict σ X)
```

Useful lemmas:

```coq
basic_world_formula_subset_current :
  X ⊆ Y ->
  m ⊨ basic_world_formula Σ Y ->
  world_has_type_on Σ X (res_restrict m X).

basic_world_formula_store_restrict_closed_env
basic_world_formula_store_restrict_lc_env
```

In `ChoiceTyping.Soundness`, use the wrappers
`denot_ctx_in_env_world_has_type_on`,
`denot_ctx_in_env_store_restrict_closed`, and
`denot_ctx_in_env_store_restrict_lc` instead of unfolding the context
denotation's `FAnd` manually.

主证明应该优先调用这个 lemma，而不是反复直接调用 tactic。

在 normal form 已经整理好的小目标上，可以用 CoqHammer 自带 tactic 收尾，例如：

```coq
normalize_store_overlap H w1 σ1 Hσ1 w2 σ2 Hσ2.
hauto.
```

经验上，`hauto` 适合处理“目标已经变成某个 hypothesis 或简单一阶组合”的情况；
不要让它负责发现 store/world 的正确 normal form，否则失败时很难定位问题。
