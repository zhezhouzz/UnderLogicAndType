# Skill: Strict Positivity in Inductive Types

## 问题

Rocq 要求 inductive type 的定义满足"严格正性"（strict positivity）：
被定义的类型 `T` 不能出现在 `→` 的**左侧**的 lambda 里。

以下写法会触发 positivity checker 报错：

```coq
(* 错误：has_choice_type 出现在 Forall2 的 lambda 左侧 *)
Inductive has_choice_type : ... :=
  | CT_Match ... :
      Forall2
        (fun '(n, body) arg_tys =>
          ... → has_choice_type ...)   (* ❌ Non strictly positive *)
        branches (constructor_tys b) → ...

(* 错误：lc_tm 出现在 Forall 的 lambda 里 *)
Inductive lc_tm : tm → Prop :=
  | LC_match ... :
      Forall (fun '(n, body) => branch_lc n body) brs → ...  (* ❌ *)
```

## 解决方案

把 `Forall`/`Forall2` 里的 lambda 换成**直接的全称量词**：

```coq
(* 正确：用 ∀ + List.In 或 list !! i 替换 Forall *)
Inductive lc_tm : tm → Prop :=
  | LC_match brs L :
      (∀ n body, List.In (n, body) brs → branch_lc n body) → ...  (* ✓ *)

(* 正确：用 ∀ i + 索引替换 Forall2 *)
Inductive has_choice_type : ... :=
  | CT_Match ... :
      (∀ i n body arg_tys,
          branches !! i = Some (n, body) →
          constructor_tys b !! i = Some arg_tys →
          ... → has_choice_type ...)   (* ✓ *)
      → ...
```

## 规律

凡是 inductive 里需要"对列表中每个元素的子推导"，一律用 `∀ x, List.In x xs →` 或 `xs !! i = Some x →`，不用 `Forall (fun x => ...)` 或 `Forall2 (fun x y => ...)`。
