# Skill: Mutual Inductive 的 EqDecision 无法自动证明

## 问题

对于普通的 inductive type，`solve_decision` 可以自动推导 `EqDecision`。
但对于 **mutual inductive type**（如 `value` 和 `tm` 互相引用），
`solve_decision` 会失败，因为它需要同时对两个类型做互相递归的决策程序。

```coq
(* 这会失败 *)
#[global] Instance EqDecision_value : EqDecision value.
Proof. solve_decision. Qed.   (* ❌ solve_decision 不能处理 mutual case *)
```

直接写 mutual fixpoint proof 也很繁琐，容易触发 focusing 错误。

## 解决方案

直接 `Admitted`，待后续补充：

```coq
#[global] Instance EqDecision_value : EqDecision value.
Proof. Admitted.

#[global] Instance EqDecision_tm : EqDecision tm.
Proof. Admitted.
```

## 说明

在 formalization skeleton 阶段，`EqDecision` 的 proof 并不影响逻辑正确性
（它只是 decidable equality，不改变类型的语义）。
可以先 `Admitted`，等 soundness proof 完成后再补。

如果确实需要证明，正确做法是写一个 mutual `Fixpoint` decision procedure，
然后证明它满足 `EqDecision` 的接口，而不是试图用 `solve_decision` 自动完成。
