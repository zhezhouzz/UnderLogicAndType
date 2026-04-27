# Skill: ^t^ 接受 atom，不接受 value；{k ~> v} 接受 value

## 两种 open notation 的区别

```coq
Notation "e '^t^' x" := (open_tm 0 (vfvar x) e)   (* x : atom  *)
Notation "e '^^'  v" := (open_one 0 v e)           (* v : value *)
Notation "'{' k '~>' v '}' e" := (open_one k v e)  (* v : value *)
```

**`^t^` 内部已经帮你包了 `vfvar`**，所以它的参数是 `atom`，不是 `value`。

## 常见错误

```coq
(* 错误：vfvar y : value，但 ^t^ 期望 atom *)
e ^t^ vfvar y   (* ❌ *)

(* 正确 *)
e ^t^ y         (* ✓ — y : atom，^t^ 内部做 vfvar y *)

(* 也正确，但更啰嗦 *)
{0 ~> vfvar y} e   (* ✓ — {k ~> v} 直接接受 value *)
```

## 规律

- 使用 `^t^` / `^v^` 时，传 `atom`
- 使用 `{k ~> v}` 或 `^^` 时，传 `value`（通常是 `vfvar x` 或 `vbvar k`）
- 在 de Bruijn 显式操作（如 `{0 ~> vfvar y} ({1 ~> vfvar f} e)`）里，用 `{k ~> v}` 形式
