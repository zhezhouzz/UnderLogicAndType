# Skill: ElemOf / aset 类型标注

## 问题

在 inductive type 或 lemma 里，当某个参数 `L` 只通过 `x ∉ L` 出现，
Rocq 需要推断 `ElemOf atom ?B` 这个 typeclass instance，
但它无法确定 `?B` 是 `aset`（= `gset atom`）还是别的类型，
于是报：

```
Error: UNDEFINED EVARS:
 ?X == [... |- ElemOf atom ?B] (parameter ElemOf of elem_of)
```

## 解决方案

给 `L` 加上显式类型标注 `: aset`：

```coq
(* 错误 — Rocq 无法推断 ElemOf *)
| LC_lam e L :
    (∀ x, x ∉ L → lc_tm (e ^t^ x)) → ...

(* 正确 — 明确告知 L 的类型 *)
| LC_lam e (L : aset) :
    (∀ x, x ∉ L → lc_tm (e ^t^ x)) → ...
```

同样适用于 lemma 的签名和 inductive constructor 参数。

## 规律

所有使用 cofinite quantification（`∀ x, x ∉ L → ...`）的地方，
`L` 参数一律标注 `(L : aset)`，不依赖 Rocq 推断。
`aset` = `gset atom`（在 stdpp 里）。
