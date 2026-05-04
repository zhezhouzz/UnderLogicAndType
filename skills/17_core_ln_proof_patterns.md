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
