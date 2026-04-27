# Skill: Notation 冲突的排查与解决

## 问题一：`{[σ]} e` 与 stdpp 单例集合 `{[x]}` 冲突

stdpp 定义了 `{[ x ]}` 表示单例集合，前缀是 `{[`。
如果再定义：

```coq
Notation "'{[' σ ']}' e" := (subst_map σ e)
```

Rocq 的 notation parser 会在看到 `{[` 时产生歧义，
导致类型错误或解析失败。

**解决**：删除该 notation，直接调用 `subst_map σ e`。

---

## 问题二：`Class Subst` 与 `Definition Subst` 名称冲突

如果两个库都在顶层定义了同名符号，后者会遮蔽前者：

```coq
(* CoreLang.Prelude *)
Class Subst V A := ...   (* 被遮蔽 *)

(* UnderLogicAndType.Substitution *)
Definition Subst := gmap Var Value   (* 遮蔽了上面的 Class *)
```

**解决**：将 class 重命名为不冲突的名字：

```coq
Class SubstV V A := subst_one : atom → V → A → A.
```

并更新所有 instance 声明：

```coq
#[global] Instance subst_tm_inst : SubstV value tm := tm_subst.
```

---

## 规律

- 定义 notation 前，先检查 stdpp 是否有相同前缀的 notation（`{[`、`⊢` 等是高危前缀）。
- 跨库时避免在顶层使用通用名字（`Subst`、`Open`、`Close` 等）作为 `Definition` 或 `Axiom` 名，容易和 typeclass 名冲突。
