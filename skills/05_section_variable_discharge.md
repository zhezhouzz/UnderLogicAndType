# Skill: Section Variable Discharge — 只有用到的变量才会被 generalize

## 问题

Rocq 的 Section 机制：Section 结束时，只有在定义中**实际出现**的 section variable
会被 discharge 进该定义的类型。

这意味着两个在同一 Section 里定义的类型，可能有**不同数量**的隐式参数，
即使 Section 头声明了更多变量。

## 具体案例

```coq
Section ChoiceLogic.
  Context {Var : Type} `{Countable Var} {Value : Type}.

  Inductive Formula : Type :=
    | FForall (X : gset Var) (φ : Formula)   (* 用到了 Var *)
    | FAtom   (a : WorldT -> Prop)           (* 用到了 Value through WorldT *)
    | ...
```

`Formula` 的定义里：
- 用到了 `Var`（通过 `gset Var`）→ discharge 了 `Var`, `EqDecision Var`, `Countable Var`
- 用到了 `Value`（通过 atom 类型 `WorldT -> Prop`）→ discharge 了 `Value`

所以 Section 结束后，`Formula` 的实际签名是：

```coq
Formula : ∀ {Var} `{Countable Var} {Value}, Type
(* 隐式参数：Var, EqDecision Var, Countable Var, Value *)
```

## 错误的写法

```coq
(* 错误：Formula 现在不再接收额外的 atom type 参数 *)
Notation FormulaQ A := (@Formula atom _ _ value A)

(* Rocq 报错：The expression "Formula value" of type "Type"
   cannot be applied to the term "A" : "Type" *)
```

## 正确的写法

```coq
(* 正确：只提供 Formula 实际需要的参数 *)
Notation FormulaQ := (@Formula atom _ _ value)
(*                              Var  EqDec Countable Value *)
```

## 排查方法

当 `@F a b c ...` 报 "Non-functional construction" 或 "applied to too many arguments"，
用 `Print F.` 或 `Check @F.` 查看 F 的实际 implicit argument 列表，
不要假设它等于 Section 头声明的变量数。
