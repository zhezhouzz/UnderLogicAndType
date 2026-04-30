# Skill: Fixpoint vs Definition — 自引用必须用 Fixpoint

## 问题

Rocq 的 `Definition` 不允许函数体引用自身（不生成递归不动点）。
如果一个函数在 match 的分支里调用自己，必须用 `Fixpoint`。

```coq
(* 错误：Definition 里调用了自己 formula_fv *)
Definition formula_fv (φ : Formula) : aset :=
  match φ with
  | FStar p q => formula_fv p ∪ formula_fv q  (* ❌ 自引用 *)
  ...

(* 正确 *)
Fixpoint formula_fv (φ : Formula) : aset :=
  match φ with
  | FStar p q => formula_fv p ∪ formula_fv q  (* ✓ *)
  ...
```

## 也适用于 lift_ctx 的反例

```coq
(* 错误：把 gmap fold 写成 Fixpoint，但 gmap 不是 inductive，无法 structural recurse *)
Fixpoint lift_ctx (Γ : gmap atom ty) : ctx := ...   (* ❌ *)

(* 正确：gmap fold 用 Definition 即可，map_fold 内部已处理递归 *)
Definition lift_ctx (Γ : gmap atom ty) : ctx :=
  map_fold (fun x s acc => CtxComma (CtxBind x (lift_ty s)) acc) CtxEmpty Γ.  (* ✓ *)
```

## 规律

- 函数体 match 分支里有自调用 → `Fixpoint`
- 函数体调用的是别的函数（如 `map_fold`），自身不递归 → `Definition`
- 误用 `Fixpoint` 在非 inductive 类型（如 `gmap`）上 structural recurse → 报错
