# Core locally-nameless proof patterns

## 拆开 `Lemma ... with ...`

Rocq 有时无法从两个独立 `induction ... using value_mut/tm_mut` 的 proof
中猜出 mutual theorem 的 decreasing argument，报错类似：

```text
Cannot guess decreasing argument of fix.
```

如果两个 theorem 只是名字上成对，并不需要作为一个 mutual theorem 暴露，
更稳的做法是直接拆成两个普通 lemma，名字保持不变：

```coq
Lemma open_fv_value ... . Proof. ... Qed.
Lemma open_fv_tm ... . Proof. ... Qed.
```

这样下游引用不变，proof term 也简单得多。

## 对真正 mutual 的 lc proof 用 combined helper

对 `lc_value` / `lc_tm` 这种 cofinite local-closure theorem，两个方向确实互相依赖。
这时不要把最终 API 写成 mutual `Lemma ... with ...`。可以先证明一个 pair helper：

```coq
Lemma open_rec_lc_mutual :
  (forall v, lc_value v -> forall k u, open_value k u v = v) /\
  (forall e, lc_tm e -> forall k u, open_tm k u e = e).
Proof.
  apply lc_mutind; ...
Qed.
```

然后用 wrapper 暴露原来的名字：

```coq
Lemma open_rec_lc_value v :
  lc_value v -> forall k u, open_value k u v = v.
Proof. exact (proj1 open_rec_lc_mutual v). Qed.
```

这种结构既保留互递归证明，又避免 final theorem 本身成为 mutual fixpoint。

## Cofinite binder case: use fact1

`open_rec_lc` 的 binder case 通常不能靠 structural induction 直接得到
`open (S k) u body = body`。参考 HATs/UnderType，先证明 fact1 风格的辅助 lemma：

```coq
Lemma open_rec_open_eq_tm u w e i j :
  i <> j ->
  open_tm i u (open_tm j w e) = open_tm j w e ->
  open_tm i u e = e.
```

在 binder case 中选择一个 fresh `x ∉ L`，从 induction hypothesis 得到：

```coq
open_tm (S k) u (open_tm 0 (vfvar x) body)
= open_tm 0 (vfvar x) body
```

然后用 fact1，取 `i = S k`、`j = 0`。

## Tactic placement

`set_solver` 很适合纯 `fv` inclusion proof；`hauto` 适合 normal form 已经出现后的收尾。
对涉及 binder index 的 proof，优先显式写出 `destruct (decide (...))` 和 `lia`，
不要让自动化猜 index arithmetic。

## Substitution under cofinite binders

证明 `subst_lc` 的 binder case 时，fresh set 必须扩成 `L ∪ {[x]}`，其中 `x`
是正在替换的变量。否则打开 binder 时选择的 `y` 可能等于 `x`，无法把
`vfvar y` 改写成 `value_subst x u (vfvar y)`。

典型形状：

```coq
eapply LC_lam with (L := L ∪ {[x]}); intros y Hy.
replace (vfvar y) with (value_subst x u (vfvar y))
  by (simpl; rewrite decide_False by set_solver; reflexivity).
rewrite <- subst_open_tm by eauto.
apply IH; set_solver.
```

这里的 `replace` 比直接 `change` 更稳，因为目标中通常是通过 atom-open
instance 得到的 `vfvar y`，而不是 syntactically 显示的 substitution form。

## Typing induction with cofinite binders

Basic typing 的 weakening/regularity proof 通常可以直接用 generated mutual induction：

```coq
induction Hty using value_has_type_mut with
  (P0 := fun Γ e T _ => forall Γ', Γ ⊆ Γ' -> Γ' ⊢ₑ e ⋮ T).
```

binder case 里对 context extension 使用 `insert_mono`：

```coq
econstructor. intros x Hx.
eapply IH; [exact Hx | by apply insert_mono].
```

如果 proof script 里 IH 名字不稳定，避免猜 `H0`/`H1`，用局部 pattern 抓
`forall y, y ∉ _ -> forall Γ', ...` 这一类 IH。

## Watch atom coercions in typing substitution

Typing substitution 的 variable case 容易被 notation/coercion 遮住：目标可能打印成
`{x := vx} x`，其中右边的 `x` 实际上是 atom 经 coercion 得到的 `vfvar x`。
这种目标上直接 `change`/`replace` 很容易因为 syntactic shape 不一致而失败。

处理这类 proof 时，优先先暴露 concrete term：

```coq
change (value_subst x vx (vfvar x)) with vx.
```

如果 `change` 仍不稳定，先把 variable case 单独抽出小 lemma，再在 typing
substitution proof 中调用，避免在大的 mutual induction proof 里调试 coercion。

## FV containment under cofinite typing binders

证明 typing implies `fv ⊆ dom Γ` 时，binder case 的标准套路是：

1. 选择 `x = fresh_for (L ∪ fv body)`；
2. 用 typing IH 得到 `fv (body ^^ x) ⊆ dom (<[x:=T]> Γ)`；
3. 用 `open_fv_tm'` / `open_fv_value'` 得到 `fv body ⊆ fv (body ^^ x)`；
4. `rewrite dom_insert in IH; set_solver` 去掉 fresh 的 `{[x]}`。

如果 IH 名字不稳定，就 pattern-match 形如
`forall y, y ∉ L -> fv_tm (body ^^ y) ⊆ _` 的 hypothesis。

## Basic typing uniqueness with mutual induction

证明 `Γ ⊢ e ⋮ T1 -> Γ ⊢ e ⋮ T2 -> T1 = T2` 时，即使从
`value_has_type_mut` 或 `tm_has_type_mut` 的一边开始，Rocq 仍会生成另一边
judgement 的 obligations。不要假设 bullet 顺序对应当前 syntactic category；
先看当前 goal，再处理。

常见 cases：

- variable：两个 lookup 都指向同一个 key，`simplify_eq` 通常足够；
- lambda/body 或 let/body：选 `fresh_for (L ∪ L0)`，把两个 cofinite typing
  premises 在同一个 fresh atom 上 specialize；
- let：先用 e1 的 uniqueness 证明 binder type 相等，再 `subst`；
- primitive op：把一个 `prim_op_type` 等式 rewrite 到另一个里，再
  `simplify_eq`；
- application：对函数位置的 uniqueness 得到两个 arrow type 相等，再
  `simplify_eq`。

如果 IH 名字不稳定，匹配形如
`forall T2, Γ ⊢ᵥ v1 ⋮ T2 -> TArrow _ _ = T2` 的 hypothesis，比依赖
`IHHty1` 这类自动名更稳。
