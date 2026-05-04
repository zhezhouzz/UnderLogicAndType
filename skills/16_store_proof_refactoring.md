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

### 4. `change` 用于显式化 overloaded 目标

当 Rocq 报错类似：

```text
The term "s" has type "StoreN" while it is expected to have type "Type".
Could not find an instance for FMap (@Store)
```

通常是隐式参数或 section-level alias 干扰了 typeclass inference。

可以用 `change` 把目标改成具体的 map 表达式，例如：

```coq
change (@map_restrict atom _ nat s X !! k = Some v).
```

不过如果这个 pattern 频繁出现，说明这个 lemma 应该上移到定义所在文件，而不是留在 example 中。

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
