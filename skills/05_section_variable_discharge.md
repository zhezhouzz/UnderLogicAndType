# Skill: Section Variable Discharge — 只有用到的变量才会被 generalize

## 问题

Rocq 的 Section 机制：Section 结束时，只有在定义中**实际出现**的 section variable
会被 discharge 进该定义的类型。

这意味着两个在同一 Section 里定义的类型，可能有**不同数量**的隐式参数，
即使 Section 头声明了更多变量。

## 具体案例

```coq
Section ChoiceLogic.
  Definition WorldT := (@WfWorld atom _ _ value).

  Inductive Formula : Type :=
    | FForall (x : atom) (φ : Formula)
    | FAtom   (a : logic_qualifier)
    | ...
```

现在的 `Formula` 直接使用全局的 `atom`、`value` 和 `logic_qualifier`，所以它已经不再是
parameterized formula datatype。

所以 `Formula` 的实际签名是：

```coq
Formula : Type
```

## 错误的写法

```coq
(* 错误：Formula 现在不再接收额外参数 *)
Notation FormulaQ A := (Formula A)

(* Rocq 报错：Formula cannot be applied to the term ... *)
```

## 正确的写法

```coq
(* 正确：直接别名即可 *)
Notation FormulaQ := Formula.
```

## 排查方法

当 `@F a b c ...` 报 "Non-functional construction" 或 "applied to too many arguments"，
用 `Print F.` 或 `Check @F.` 查看 F 的实际 implicit argument 列表，
不要假设它等于 Section 头声明的变量数。
