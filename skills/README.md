# Rocq Formalization Skills

本目录收录 UnderLogicAndType formalization 过程中积累的证明和定义经验。
这些文件不是都具有同等优先级：当前主线正在围绕 LN logic、deterministic core、
denotation/tlet proof 和局部 solver 做收敛，所以阅读顺序应按下面分类来走。

## 使用原则

- **P0 常驻规则**：几乎每次证明/重构都要遵守，优先读。
- **P1 当前主线**：和当前 LN、denotation、tlet、instantiation 证明直接相关。
- **P2 局部坑位**：遇到对应报错或定义形态时再查。
- **P3 历史/低优先级**：记录旧路线或较少用经验；不要把其中的旧设计当成当前目标。

如果某个 P3 文件里的建议和当前代码冲突，以当前 Rocq definitions 和用户最近确认的设计为准。

## P0 常驻规则

| 文件 | 主题 |
|------|------|
| [15_definition_sanity_check.md](15_definition_sanity_check.md) | Definition sanity check：先对齐论文、报告冲突、经确认后再修改 |
| [25_proof_style_and_local_solvers.md](25_proof_style_and_local_solvers.md) | Proof style：`eauto 6`、分层 solver、normalization tactics、少用一次性 `assert` |
| [18_tactic_migration.md](18_tactic_migration.md) | Tactic 使用：cofinite fresh、`my_set_solver`、`hauto` 的安全使用边界 |
| [16_store_proof_refactoring.md](16_store_proof_refactoring.md) | Store/map proof：通用 lemma 上移、lookup extensionality、把 `change` 收敛成 norm |
| [19_operational_reduction_helpers.md](19_operational_reduction_helpers.md) | Core operational proof：优先用 reduction intro/iff helper，不手搓 steps |

## P1 当前主线

| 文件 | 主题 |
|------|------|
| [17_core_ln_proof_patterns.md](17_core_ln_proof_patterns.md) | Core LN proof：拆 mutual lemma、combined helper、cofinite binder patterns |
| [21_instantiation_migration.md](21_instantiation_migration.md) | Core instantiation/multi-substitution：`msubst` classes、closed/lc/env side conditions |
| [22_choice_instantiation_migration.md](22_choice_instantiation_migration.md) | ChoiceType instantiation：type/qualifier open/subst，多 substitution 边界 |
| [24_typing_naming_refactor.md](24_typing_naming_refactor.md) | Typing naming：fresh record、erased-context domain、open/subst bridge；部分内容可能随 LN logic refactor 调整 |
| [11_sigma_type_wfworld_pattern.md](11_sigma_type_wfworld_pattern.md) | WfWorld sigma type：raw/private helper 与 public wf interface 的分层 |
| [12_partial_order_stdpp.md](12_partial_order_stdpp.md) | stdpp order instance：`SqSubsetEq`、`PreOrder`、`AntiSymm` 的拆分方式 |

## P2 局部坑位

| 文件 | 主题 |
|------|------|
| [01_mutual_recursion_and_typeclass.md](01_mutual_recursion_and_typeclass.md) | Mutual fixpoint 先定义后注册为 typeclass instance |
| [02_strict_positivity.md](02_strict_positivity.md) | Inductive 严格正性；当前 boolean match 已规避旧 branch-list 问题 |
| [03_elemof_aset_annotation.md](03_elemof_aset_annotation.md) | Cofinite quantification 里 `L` 必须标注 `: aset` |
| [04_notation_clash.md](04_notation_clash.md) | `{[σ]}` / stdpp singleton / `Subst` 等 notation/name clash |
| [05_section_variable_discharge.md](05_section_variable_discharge.md) | Section 只 discharge 实际用到的变量，不要猜参数数量 |
| [09_fixpoint_vs_definition.md](09_fixpoint_vs_definition.md) | 自引用用 `Fixpoint`；非 structural recursion 用 `Definition` |
| [10_inductive_let_pattern.md](10_inductive_let_pattern.md) | Constructor 里避免 `let '(a,b) := ...`，改用显式等式前提 |
| [14_open_notation_typeclass.md](14_open_notation_typeclass.md) | Open typeclass notation：优先 generic `^^`，避免 category-specific notation |

## P3 历史 / 低优先级

这些文件保留为历史记录或局部参考。它们可能提到已经被替换的非-LN logic、
旧 expression-result encoding、旧 branch 状态，不能直接作为当前设计依据。

| 文件 | 状态 |
|------|------|
| [06_anf_and_tletapp.md](06_anf_and_tletapp.md) | 旧 ANF/tletapp 经验；当前已有 `tapp_tm`/deterministic core 调整，遇到 legacy derived form 再查 |
| [07_open_notation_atom_vs_value.md](07_open_notation_atom_vs_value.md) | 旧 notation 区分经验；当前优先参考 generic open/typeclass 与实际代码 |
| [08_eqdecision_mutual_inductive.md](08_eqdecision_mutual_inductive.md) | skeleton 阶段经验；不要把“先 admit EqDecision”作为长期策略 |
| [13_formula_atoms_as_world_predicates.md](13_formula_atoms_as_world_predicates.md) | 旧 Formula atom/qualifier embedding 说明；当前 LN logic 与 atom sugar 已重构 |
| [20_partial_algebra_remaining.md](20_partial_algebra_remaining.md) | 旧 partial algebra branch 的剩余工作记录；只作为历史背景 |
| [23_expression_result_semantics.md](23_expression_result_semantics.md) | 旧 expression-result semantic 记录；当前以 `FStoreResourceAtom`/LN formula 路线为准 |
