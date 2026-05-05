# Core locally-nameless proof patterns

## 拆开 `Lemma ... with ...`

Rocq 有时无法从两个独立 `induction ... using value_mut/tm_mut` 的 proof
中猜出 mutual theorem 的 decreasing argument，报错类似：

```text
Cannot guess decreasing argument of fix.
```

如果两个 theorem 只是名字上成对，并不需要作为一个 mutual theorem 暴露，
更稳的做法是直接拆成两个普通 lemma，名字保持不变：

```coq
Lemma open_fv_value ... . Proof. ... Qed.
Lemma open_fv_tm ... . Proof. ... Qed.
```

这样下游引用不变，proof term 也简单得多。

## 对真正 mutual 的 lc proof 用 combined helper

对 `lc_value` / `lc_tm` 这种 cofinite local-closure theorem，两个方向确实互相依赖。
这时不要把最终 API 写成 mutual `Lemma ... with ...`。可以先证明一个 pair helper：

```coq
Lemma open_rec_lc_mutual :
  (forall v, lc_value v -> forall k u, open_value k u v = v) /\
  (forall e, lc_tm e -> forall k u, open_tm k u e = e).
Proof.
  apply lc_mutind; ...
Qed.
```

然后用 wrapper 暴露原来的名字：

```coq
Lemma open_rec_lc_value v :
  lc_value v -> forall k u, open_value k u v = v.
Proof. exact (proj1 open_rec_lc_mutual v). Qed.
```

这种结构既保留互递归证明，又避免 final theorem 本身成为 mutual fixpoint。

## Cofinite binder case: use fact1

`open_rec_lc` 的 binder case 通常不能靠 structural induction 直接得到
`open (S k) u body = body`。参考 HATs/UnderType，先证明 fact1 风格的辅助 lemma：

```coq
Lemma open_rec_open_eq_tm u w e i j :
  i <> j ->
  open_tm i u (open_tm j w e) = open_tm j w e ->
  open_tm i u e = e.
```

在 binder case 中选择一个 fresh `x ∉ L`，从 induction hypothesis 得到：

```coq
open_tm (S k) u (open_tm 0 (vfvar x) body)
= open_tm 0 (vfvar x) body
```

然后用 fact1，取 `i = S k`、`j = 0`。

## Tactic placement

`set_solver` 很适合纯 `fv` inclusion proof；`hauto` 适合 normal form 已经出现后的收尾。
对涉及 binder index 的 proof，优先显式写出 `destruct (decide (...))` 和 `lia`，
不要让自动化猜 index arithmetic。

## Open swap: stay at the UnderType abstraction level

证明 `open_swap` 时不要写两个互不相干的 `value`/`tm` induction，也不要一看到
`if decide` 就在 lemma 里手动拆。UnderType 的关键形状是 simultaneous recursion：
同一个 `P` 同时覆盖 `value` 和 `tm`，这样 `vlam`、`vfix`、`tlete` 这些跨语法类的
constructor 可以直接使用另一侧 IH。

在本 repo 中，`value_tm_mutind` 返回的是 `*`，所以可以先证明一个 pair helper：

```coq
Definition open_swap_mutual :
  (forall v, ... open_value ... v ...) *
  (forall e, ... open_tm ... e ...).
Proof.
  apply value_tm_mutind; intros; autounfold with class_simpl in *; ln_simpl; auto;
    try solve [autounfold with class_simpl in *; ln_simpl; f_equal; eauto].
  all: solve_the_remaining_bvar_normal_form.
Defined.
```

注意 `try solve [f_equal; eauto]`，不要写 `try (f_equal; eauto)`：后者会在
`vbvar` case 里留下 `i = j`、`v = u` 之类由 `f_equal` 生成的子目标，污染证明状态。
如果 `if decide` 还残留，优先检查是否忘了 `autounfold with class_simpl in *`
把 typeclass notation 展开，而不是马上手动 case split。

`open_lc_respect` 也应该用 simultaneous `lc_value`/`lc_tm` induction。Binder case
的核心步骤是用 `open_swap` 把

```coq
open 0 (vfvar x) (open (S k) w body)
```

改成

```coq
open (S k) w (open 0 (vfvar x) body)
```

然后把同样交换过的 `u` 版本作为等式前提交给 IH。避免 set 里漏掉原来的 cofinite
`L`：构造新的 avoidance set 时用 `L ∪ collect_stales`，这样可以直接得到
`x ∉ L` 来 specialize IH。

## Substitution under cofinite binders

证明 `subst_lc` 的 binder case 时，fresh set 必须扩成 `L ∪ {[x]}`，其中 `x`
是正在替换的变量。否则打开 binder 时选择的 `y` 可能等于 `x`，无法把
`vfvar y` 改写成 `value_subst x u (vfvar y)`。

典型形状：

```coq
eapply LC_lam with (L := L ∪ {[x]}); intros y Hy.
replace (vfvar y) with (value_subst x u (vfvar y))
  by (simpl; rewrite decide_False by set_solver; reflexivity).
rewrite <- subst_open_tm by eauto.
apply IH; set_solver.
```

这里的 `replace` 比直接 `change` 更稳，因为目标中通常是通过 atom-open
instance 得到的 `vfvar y`，而不是 syntactically 显示的 substitution form。

## Typing induction with cofinite binders

Basic typing 的 weakening/regularity proof 通常可以直接用 generated mutual induction：

```coq
induction Hty using value_has_type_mut with
  (P0 := fun Γ e T _ => forall Γ', Γ ⊆ Γ' -> Γ' ⊢ₑ e ⋮ T).
```

binder case 里对 context extension 使用 `insert_mono`：

```coq
econstructor. intros x Hx.
eapply IH; [exact Hx | by apply insert_mono].
```

如果 proof script 里 IH 名字不稳定，避免猜 `H0`/`H1`，用局部 pattern 抓
`forall y, y ∉ _ -> forall Γ', ...` 这一类 IH。

## Watch atom coercions in typing substitution

Typing substitution 的 variable case 容易被 notation/coercion 遮住：目标可能打印成
`{x := vx} x`，其中右边的 `x` 实际上是 atom 经 coercion 得到的 `vfvar x`。
这种目标上直接 `change`/`replace` 很容易因为 syntactic shape 不一致而失败。

处理这类 proof 时，优先先暴露 concrete term：

```coq
change (value_subst x vx (vfvar x)) with vx.
```

如果 `change` 仍不稳定，先把 variable case 单独抽出小 lemma，再在 typing
substitution proof 中调用，避免在大的 mutual induction proof 里调试 coercion。

## FV containment under cofinite typing binders

证明 typing implies `fv ⊆ dom Γ` 时，binder case 的标准套路是：

1. 选择 `x = fresh_for (L ∪ fv body)`；
2. 用 typing IH 得到 `fv (body ^^ x) ⊆ dom (<[x:=T]> Γ)`；
3. 用 `open_fv_tm'` / `open_fv_value'` 得到 `fv body ⊆ fv (body ^^ x)`；
4. `rewrite dom_insert in IH; set_solver` 去掉 fresh 的 `{[x]}`。

如果 IH 名字不稳定，就 pattern-match 形如
`forall y, y ∉ L -> fv_tm (body ^^ y) ⊆ _` 的 hypothesis。

## Basic typing uniqueness with mutual induction

证明 `Γ ⊢ e ⋮ T1 -> Γ ⊢ e ⋮ T2 -> T1 = T2` 时，即使从
`value_has_type_mut` 或 `tm_has_type_mut` 的一边开始，Rocq 仍会生成另一边
judgement 的 obligations。不要假设 bullet 顺序对应当前 syntactic category；
先看当前 goal，再处理。

常见 cases：

- variable：两个 lookup 都指向同一个 key，`simplify_eq` 通常足够；
- lambda/body 或 let/body：选 `fresh_for (L ∪ L0)`，把两个 cofinite typing
  premises 在同一个 fresh atom 上 specialize；
- let：先用 e1 的 uniqueness 证明 binder type 相等，再 `subst`；
- primitive op：把一个 `prim_op_type` 等式 rewrite 到另一个里，再
  `simplify_eq`；
- application：对函数位置的 uniqueness 得到两个 arrow type 相等，再
  `simplify_eq`。

如果 IH 名字不稳定，匹配形如
`forall T2, Γ ⊢ᵥ v1 ⋮ T2 -> TArrow _ _ = T2` 的 hypothesis，比依赖
`IHHty1` 这类自动名更稳。

## Basic typing strengthening

证明从 `<[x:=Tx]> Γ ⊢ e ⋮ T` 和 `x ∉ fv e` 得到 `Γ ⊢ e ⋮ T` 时：

1. `remember (<[x:=Tx]> Γ)`，再对 typing derivation 归纳；
2. variable case 用 `lookup_insert_ne`，freshness 给出变量不是 `x`；
3. binder case 构造新 typing 时把 cofinite set 扩成 `L ∪ {[x]}`，这样打开用的
   atom `y` 自动满足 `y ≠ x`；
4. 用 `insert_insert_ne` 交换 `<[y:=T]> (<[x:=Tx]> Γ)` 和
   `<[x:=Tx]> (<[y:=T]> Γ)`；
5. 用 `open_fv_tm` / `open_fv_value` 把 `x ∉ fv body` 推到
   `x ∉ fv (body ^^ y)`。

如果 `eauto` 留下 application/match 这类组合 case，通常是因为每个子项的
freshness 需要从 `x ∉ fv (compound)` 中拆出来；直接对每个 IH 用
`[reflexivity | set_solver]` 即可。

## Head-step determinism

对于 redex 形状互斥的 `head_step` determinism，先直接
`inversion H1; subst; inversion H2; subst`。如果构造子 source 形状设计得足够
具体，`eauto; try congruence` 往往会解决全部 cases；不要急着手写每个 bullet，
否则自动化已经解决完目标时会出现 “No more goals” 的 bullet 错误。

## Multi-step inversion with stdpp rtc

对 `e →* v` 做第一步反演时用 `rtc_inv`，但要显式给 relation 和端点，例如：

```coq
destruct (rtc_inv (R := step) e (tret v) Hsteps)
  as [Heq | [e' [Hstep Hrest]]].
```

如果只写 `rtc_inv Hsteps`，Rocq 可能无法推断 `R`，甚至把 `Hsteps` 解析成
起点参数。head redex 的 inversion 之后，很多 `Step_let` 分支会因为 source
形状不匹配直接消失，所以同样不要预设每个 constructor 都还有 bullet。

如果项目里的 `→*` 被定义成带 regularity 的自定义 inductive，而不是裸
`rtc step`，应改用项目自己的 inversion lemma，例如 `steps_inv`。这种设计能避免
`rtc_refl` 让 ill-formed terms 零步约化到自己；let intro/decomposition 里也可以
直接从 `e →* tret v` 拿到起点和终点的 local closure。

证明 let multi-step decomposition/introduction 的套路：

- intro 方向对 `e1 →* tret vx` 归纳；refl case 用 `HS_Ret`，step case 用
  `Step_let` lift 一步；
- decomposition 方向对 `tlete e1 e2 →* tret v` 反演第一步；`HS_Ret` case 取
  let-bound value，`Step_let` case 递归分解剩余多步。

## Mutual EqDecision for LN syntax

对 mutual inductive syntax 写 equality decision 时，可以写 mutual fixpoint：

```coq
Fixpoint value_eqdec' (v1 v2 : value) : sumbool (v1 = v2) (v1 <> v2)
with tm_eqdec' (e1 e2 : tm) : sumbool (e1 = e2) (e1 <> e2).
Proof.
  - decide equality; try solve_decision.
  - decide equality; try solve_decision.
Defined.
```

不要写 `{v1 = v2} + {v1 <> v2}`：本 repo 的 LN notation `{ x := v } e`
会和 sumbool braces 冲突，导致 parser 期待 `:=` / `~>` / `<~`。

## Splitting LN proof files

保持 `Syntax.v` 只放 syntax/operations/instances；基础 LN regularity 放在
`LocallyNamelessProps.v`；更偏 proof engineering 的 substitution algebra、fv
估计、body helper 可以放进单独的 `LocallyNamelessExtra.v`。这样 BasicTyping 和
Denotation 可以只 import 额外文件，而 syntax 层不会重新累积 theorem stubs。

新建 `.v` 文件后记得更新 `_CoqProject` 并重新生成 `Makefile.coq`。如果新文件里
Unicode token 报 lexer 错，先把 proof statement 里的 `→` / `≠` 改成 ASCII
`->` / `<>`，尤其是在刚拆出的文件中最省时间。

对于 UnderType/HATs 中较重的 substitution algebra，如 `subst_commute` 和
`subst_subst`，可以先把 statement 放到 extra 文件中作为后续 proof target；这些
互归纳证明的变量 case 很容易卡在 `decide` 展开和 `subst_fresh` rewrite 顺序上。

## Strengthen substitution before open/preservation

如果 open lemma 需要形如

```coq
Γ ⊢ᵥ u ⋮ U ->
<[x := U]> Γ ⊢ e ^^ x ⋮ T ->
Γ ⊢ e ^^ u ⋮ T
```

那么 substitution lemma 不应只接受 `∅ ⊢ᵥ u ⋮ U`。先证明更强的 insert-context
版本：

```coq
<[x := U]> Γ ⊢ e ⋮ T ->
Γ ⊢ᵥ u ⋮ U ->
Γ ⊢ {x := u} e ⋮ T
```

旧的 closed-substitution 版本再由 `∅ ⊢ᵥ u ⋮ U` 加 weakening 推出。这样
`basic_typing_open` 可以直接用 `subst_intro` 加强 substitution 收尾。

在 cofinite binder case 中，constructor 的 avoidance set 要显式包含替换变量
和当前 context domain：

```coq
apply VT_Lam with (L := L ∪ {[xsub]} ∪ dom Γ).
```

否则 `eapply` 可能留下未实例化的 set evar，后续想从 `y ∉ L` 推出
`xsub <> y` 或 `y ∉ dom Γ` 时，`set_solver` 会失去关键 singleton/domain 信息。
对打开后的替换交换，优先先 assert：

```coq
assert (Hxy : xsub <> y) by ...
assert (Hlc : lc_value u) by ...
rewrite <- subst_open_var_tm by eauto.
```

这比在 `rewrite ... by [...]` 里塞多分支 tactic 更稳定。

## Preservation over `step`

证明 one-step preservation 时，`Step_let` 的 IH 必须对 context 和 type
重新泛化：

```coq
intros Hty Hstep. revert Γ T Hty.
induction Hstep; intros Γ T Hty.
```

否则 IH 会被固定成外层 let 的返回类型 `T`，而 congruence step 需要的是
`e1` 的中间类型 `T1`。重建 let 时显式分两支更稳：

```coq
inversion Hty; subst.
eapply TT_Let.
- eapply IHHstep; eauto.
- eauto.
```

Head-step preservation 的 beta/let/fix cases 都走同一条路：从 typing inversion
拿到 cofinite premise，选 `fresh_for (L ∪ fv body)`，然后调用
`basic_typing_open_tm/value`。Primitive case 最好先证明一个小 lemma，说明
`prim_step` 保持 `prim_op_type` 的返回 base type，再用 `VT_Const` 构造结果。
