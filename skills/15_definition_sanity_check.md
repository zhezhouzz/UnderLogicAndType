# Skill: Definition Sanity Check — 先对齐论文再动 Rocq 定义

当用户要求做 sanity check、检查 formalization 和论文是否一致，或怀疑某些定义是旧残留时，使用这个流程。

## 流程

1. 接受 sanity check 指令后，先不要修改代码。
2. 阅读当前 Rocq definitions，并对照当前论文中的 formalization 描述；重点检查 definition、inductive、record、parameter、notation，以及暴露在论文层面的 lemma/theorem statement。
3. 报告可能冲突，按条目说明：
   - Rocq 中的位置和名字；
   - 论文中的对应描述或缺失；
   - 建议是删除、保留为辅助 lemma、改名，还是等待论文补充。
4. 等用户决定：修改论文描述，或者修改 Rocq definition。
5. 用户批准后再开始操作；修改后运行 `make`，并说明是否通过。

## 判断原则

- Definition 层面优先与当前论文一致。
- 论文没有出现但数学上自然的 lemma 可以保留，但要说明它只是 proof infrastructure。
- 旧设计中已经消失的 modality、notation、derived rule，不应继续作为 core definition 出现。
- Derived rules 不主动实现，除非用户明确要求。
