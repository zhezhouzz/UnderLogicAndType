# Rocq Formalization Skills

本目录收录了在 UnderLogicAndType / ChoiceType formalization 过程中积累的技巧，
每个文件对应一个独立的坑或模式。

| 文件 | 主题 |
|------|------|
| 01_mutual_recursion_and_typeclass.md | Mutual fixpoint 先定义后注册为 typeclass instance |
| 02_strict_positivity.md | Inductive 严格正性：用 `∀ + List.In` 替换 `Forall (fun ...)` |
| 03_elemof_aset_annotation.md | Cofinite quantification 里 `L` 必须标注 `: aset` |
| 04_notation_clash.md | `{[σ]}` 与 stdpp 冲突；`Subst` 名字冲突 |
| 05_section_variable_discharge.md | Section 结束只 discharge 实际用到的变量，不要猜参数数量 |
| 06_anf_and_tletapp.md | `tletapp` 只接受 `value`，对 `tm` 用 `tlete e (tletapp (vbvar 0) ...)` |
| 07_open_notation_atom_vs_value.md | `^t^` 接受 atom（已内置 vfvar），`{k ~> v}` 接受 value |
| 08_eqdecision_mutual_inductive.md | Mutual inductive 的 `EqDecision` 无法 `solve_decision`，先 Admitted |
| 09_fixpoint_vs_definition.md | 自引用用 `Fixpoint`；在非 inductive 类型上不能 structural recurse |
| 10_inductive_let_pattern.md | Constructor 里不用 `let '(a,b) :=`，改用显式等式前提 |
