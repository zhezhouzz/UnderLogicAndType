# Skill: Mutual Recursion + Typeclass Instance

## 问题

`value` 和 `tm` 是 mutual inductive type（互相引用对方），
所以对它们的操作（`open`, `close`, `subst`, `lc`）也必须 mutual recursive。
但 typeclass instance 的 body 里没法写 `Fixpoint ... with ...`。

## 解决方案

两步走：

```coq
(* Step 1: 先定义 mutual fixpoint *)
Fixpoint open_value (k : nat) (s : value) (v : value) : value :=
  | vlam s' e => vlam s' (open_tm (S k) s e)   (* 调用 open_tm *)
  ...
with open_tm (k : nat) (s : value) (e : tm) : tm :=
  | tret v => tret (open_value k s v)           (* 调用 open_value *)
  ...

(* Step 2: 再注册为 typeclass instance（零成本别名）*)
#[global] Instance open_value_inst : Open value value := open_value.
#[global] Instance open_tm_inst    : Open value tm    := open_tm.
```

## 规律

凡是涉及 mutual inductive type 的操作，都要遵循这个模式：
- `open_value` / `open_tm`
- `close_value` / `close_tm`
- `subst_value` / `subst_tm`
- `lc_value` / `lc_tm`

先定具体函数，再绑 typeclass，不可颠倒。
