# Skill: Inductive Constructor 里避免用 let 解构

## 问题

在 inductive type 的 constructor 参数列表里，
`let '(a, b) := expr in ...` 或 `match expr with (a, b) => ...` 的写法
在某些情况下会让 Rocq 无法正确处理（类型不稳定或过于复杂）。

```coq
(* 脆弱的写法 *)
| TT_LetOp Γ op args e_body T :
    let '(arg_tys, ret_b) := prim_op_type op in   (* ❌ 在 constructor body 里 let 解构 *)
    ...
```

## 解决方案

改用**显式等式前提**（equality premise）：

```coq
(* 稳健的写法 *)
| TT_LetOp Γ op args e_body T arg_tys ret_b :
    prim_op_type op = (arg_tys, ret_b) →          (* ✓ 显式等式，命名 arg_tys 和 ret_b *)
    ...
```

好处：
1. `arg_tys` 和 `ret_b` 作为独立参数出现，类型推断清晰
2. 在 inversion / case analysis 时更容易操作
3. 不依赖 `let` pattern 的 elaboration 行为

## 规律

在 inductive constructor 的参数里需要"拆开"某个 pair 类型时，
一律用 `Hop : f x = (a, b) →` 的等式前提形式，不用 `let '(a, b) := f x`。
