(** * ChoiceTyping.ResultWorldBridge

    Bridges between expression-result formulas and the concrete result worlds
    used by the soundness proof.

    The first group relates the cofinite [fresh_forall] encoding

      forall x.  [e ⇓ x] ==> body x

    to the operational result world [let_result_world_on X e x m].  Because
    [fresh_forall] is explicit-name/cofinite rather than locally nameless, the
    primitive bridge is phrased with the renamed representative
    [formula_rename_atom (fresh_for D) y (body (fresh_for D))].  Callers that
    know their body is equivariant can use the wrapper lemma to transport this
    renamed body to the desired [body y].

    The second group records resource-relative expression equivalence.  This is
    weaker than [expr_result_equiv_on]: it only compares the stores actually
    present in a world/resource.  It is the right shape for rewriting the
    expression part of denotations inside Kripke/resource proofs. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps
  LocallyNamelessProps.
From ChoiceTyping Require Export SoundnessCommon.
From ChoiceTyping Require Export LetResultWorld.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma fresh_forall_expr_result_to_let_result_world_renamed
    X e D (body : atom → FormulaQ) (m : WfWorld) :
  fv_tm e ⊆ X →
  X ⊆ world_dom (m : World) →
  m ⊨ fresh_forall D (fun x => FImpl (FExprResultOn X e x) (body x)) →
  ∃ L : aset,
    world_dom (m : World) ∪ D ∪ X ∪ fv_tm e ⊆ L ∧
    ∀ y,
      y ∉ L →
      ∀ Hfresh Hresult,
        (∀ n,
          n ⊨ FExprResultOn X e y →
          n ⊨ formula_rename_atom (fresh_for D) y
                 (FExprResultOn X e (fresh_for D))) →
        let_result_world_on X e y m Hfresh Hresult ⊨
          formula_rename_atom (fresh_for D) y (body (fresh_for D)).
Proof.
  intros Hfv HX.
  unfold fresh_forall, res_models, res_models_with_store.
  simpl. intros [_ [L [HL Hforall]]].
  exists (L ∪ D ∪ X ∪ fv_tm e).
  split; [set_solver |].
  intros y Hy Hfresh Hresult Hante.
  assert (HyL : y ∉ L) by set_solver.
  set (w := let_result_world_on X e y m Hfresh Hresult).
  pose proof (Hforall y HyL w) as Himpl_fuel.
  specialize (Himpl_fuel ltac:(subst w; reflexivity)).
  specialize (Himpl_fuel (let_result_world_on_restrict X e y m Hfresh Hresult)).
  assert (Himpl :
    w ⊨ FImpl
      (formula_rename_atom (fresh_for D) y (FExprResultOn X e (fresh_for D)))
      (formula_rename_atom (fresh_for D) y (body (fresh_for D)))).
  {
    unfold res_models, res_models_with_store.
    simpl.
    destruct Himpl_fuel as [Hscope Himpl_cont].
    split; [exact Hscope |].
    intros m' Hle Hant.
    eapply res_models_with_store_fuel_irrel.
    3: {
      apply Himpl_cont; [exact Hle |].
      eapply res_models_with_store_fuel_irrel; [| | exact Hant];
        rewrite ?formula_rename_preserves_measure; lia.
    }
    all: rewrite ?formula_rename_preserves_measure; lia.
  }
  eapply res_models_impl_elim.
  - exact Himpl.
  - apply Hante.
    subst w.
    apply let_result_world_on_models_FExprResultOn.
    + exact Hfv.
    + set_solver.
    + simpl. set_solver.
Qed.

Lemma fresh_forall_expr_result_to_let_result_world
    X e D (body : atom → FormulaQ) (m : WfWorld) :
  fv_tm e ⊆ X →
  X ⊆ world_dom (m : World) →
  m ⊨ fresh_forall D (fun x => FImpl (FExprResultOn X e x) (body x)) →
  ∃ L : aset,
    world_dom (m : World) ∪ D ∪ X ∪ fv_tm e ⊆ L ∧
    ∀ y,
      y ∉ L →
      ∀ Hfresh Hresult,
        (∀ n,
          n ⊨ FExprResultOn X e y →
          n ⊨ formula_rename_atom (fresh_for D) y
                 (FExprResultOn X e (fresh_for D))) →
        (∀ n,
          n ⊨ formula_rename_atom (fresh_for D) y (body (fresh_for D)) →
          n ⊨ body y) →
        let_result_world_on X e y m Hfresh Hresult ⊨ body y.
Proof.
  intros Hfv HX Hforall.
  destruct (fresh_forall_expr_result_to_let_result_world_renamed
    X e D body m Hfv HX Hforall) as [L [HL Huse]].
  exists L. split; [exact HL |].
  intros y Hy Hfresh Hresult Hante Hbody.
  apply Hbody.
  eapply Huse; eauto.
Qed.

Definition expr_result_equiv_in_world
    (X : aset) (n : WfWorld) (e e' : tm) : Prop :=
  fv_tm e ∪ fv_tm e' ⊆ X ∧
  X ⊆ world_dom (n : World) ∧
  ∀ σ v,
    (n : World) σ →
    (subst_map (store_restrict σ X) e →* tret v ↔
     subst_map (store_restrict σ X) e' →* tret v).

Definition expr_result_equiv_future
    (X : aset) (m : WfWorld) (e e' : tm) : Prop :=
  ∀ n, m ⊑ n → expr_result_equiv_in_world X n e e'.

Lemma expr_result_equiv_in_world_refl X (n : WfWorld) e :
  fv_tm e ⊆ X →
  X ⊆ world_dom (n : World) →
  expr_result_equiv_in_world X n e e.
Proof.
  intros Hfv HX. split; [set_solver |].
  split; [exact HX |].
  intros σ v _; split; intros Hsteps; exact Hsteps.
Qed.

Lemma expr_result_equiv_in_world_sym X (n : WfWorld) e e' :
  expr_result_equiv_in_world X n e e' →
  expr_result_equiv_in_world X n e' e.
Proof.
  intros [Hfv [HX Heq]]. split; [set_solver |].
  split; [exact HX |].
  intros σ v Hσ. symmetry. apply Heq. exact Hσ.
Qed.

Lemma expr_result_equiv_in_world_trans X (n : WfWorld) e1 e2 e3 :
  expr_result_equiv_in_world X n e1 e2 →
  expr_result_equiv_in_world X n e2 e3 →
  expr_result_equiv_in_world X n e1 e3.
Proof.
  intros [Hfv12 [HX H12]] [Hfv23 [_ H23]].
  split; [set_solver |]. split; [exact HX |].
  intros σ v Hσ. split; intros Hsteps.
  - apply (proj1 (H23 σ v Hσ)).
    apply (proj1 (H12 σ v Hσ)). exact Hsteps.
  - apply (proj2 (H12 σ v Hσ)).
    apply (proj2 (H23 σ v Hσ)). exact Hsteps.
Qed.

Lemma expr_result_equiv_on_to_in_world X (n : WfWorld) e e' :
  expr_result_equiv_on X e e' →
  X ⊆ world_dom (n : World) →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  expr_result_equiv_in_world X n e e'.
Proof.
  intros [[Hfv12 H12] [Hfv21 H21]] HX Hclosed.
  split; [exact Hfv12 |]. split; [exact HX |].
  intros σ v Hσ.
  assert (Hdom : dom (store_restrict σ X) = X).
  {
    rewrite store_restrict_dom.
    pose proof (wfworld_store_dom n σ Hσ) as Hσdom.
    set_solver.
  }
  split; intros Hsteps.
  - apply H12; [exact Hdom | apply Hclosed; exact Hσ | exact Hsteps].
  - apply H21; [exact Hdom | apply Hclosed; exact Hσ | exact Hsteps].
Qed.

Lemma let_result_world_on_expr_result_equiv_in_world
    X e e' x (n : WfWorld) Hfresh Hresult Hresult' :
  expr_result_equiv_in_world X n e e' →
  let_result_world_on X e x n Hfresh Hresult =
  let_result_world_on X e' x n Hfresh Hresult'.
Proof.
  intros [_ [_ Hequiv]].
  apply wfworld_ext. apply world_ext.
  - simpl. reflexivity.
  - intros σx. simpl. split.
    + intros [σ [vx [Hσ [Hsteps ->]]]].
      exists σ, vx. split; [exact Hσ |]. split.
      * apply (proj1 (Hequiv σ vx Hσ)). exact Hsteps.
      * reflexivity.
    + intros [σ [vx [Hσ [Hsteps ->]]]].
      exists σ, vx. split; [exact Hσ |]. split.
      * apply (proj2 (Hequiv σ vx Hσ)). exact Hsteps.
      * reflexivity.
Qed.

Lemma FExprResultOn_expr_result_equiv_in_world
    X e e' ν (m : WfWorld) :
  fv_tm e ∪ fv_tm e' ⊆ X →
  ν ∉ X →
  X ⊆ world_dom (m : World) →
  expr_result_equiv_in_world X (res_restrict m X) e e' →
  m ⊨ FExprResultOn X e ν →
  m ⊨ FExprResultOn X e' ν.
Proof.
  intros Hfv HνX HXm Hequiv Hmodel.
  pose proof (proj1 (FExprResultOn_iff_let_result_world_on
    X e ν m ltac:(set_solver) HνX HXm) Hmodel)
    as [Hfresh [Hresult Heq]].
  assert (Hresult' :
    ∀ σ, (res_restrict m X : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e' →* tret vx).
  {
    intros σ Hσ.
    destruct (Hresult σ Hσ) as [vx Hsteps].
    exists vx.
    apply (proj1 (proj2 (proj2 Hequiv) σ vx Hσ)).
    exact Hsteps.
  }
  apply (proj2 (FExprResultOn_iff_let_result_world_on
    X e' ν m ltac:(set_solver) HνX HXm)).
  exists Hfresh, Hresult'.
  rewrite Heq.
  apply let_result_world_on_expr_result_equiv_in_world.
  exact Hequiv.
Qed.

Lemma FExprResultOn_expr_result_equiv_future
    X e e' ν (m : WfWorld) :
  fv_tm e ∪ fv_tm e' ⊆ X →
  ν ∉ X →
  X ⊆ world_dom (m : World) →
  expr_result_equiv_future X (res_restrict m X) e e' →
  m ⊨ FExprResultOn X e ν →
  m ⊨ FExprResultOn X e' ν.
Proof.
  intros Hfv HνX HXm Hfuture Hmodel.
  eapply FExprResultOn_expr_result_equiv_in_world.
  - exact Hfv.
  - exact HνX.
  - exact HXm.
  - apply Hfuture. reflexivity.
  - exact Hmodel.
Qed.
