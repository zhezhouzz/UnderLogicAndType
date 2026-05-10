(** * ChoiceTyping.ExprResultEquiv

    Resource-relative equivalence for expression results.

    [expr_result_equiv_in_world X n e e'] compares [e] and [e'] only on the
    stores that actually occur in the resource [n], after restricting those
    stores to the input coordinates [X].  This is weaker than the global
    [expr_result_equiv_on] relation, but it is the shape needed for rewriting
    expression-result atoms inside Kripke/resource proofs. *)

From CoreLang Require Import Instantiation InstantiationProps.
From ChoiceTyping Require Import ResultWorldBridge.
From ChoiceType Require Import BasicStore.

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
  lc_tm e →
  lc_tm e' →
  ν ∉ X →
  X ⊆ world_dom (m : World) →
  world_store_closed_on X m →
  expr_result_equiv_in_world X (res_restrict m X) e e' →
  m ⊨ FExprResultOn X e ν →
  m ⊨ FExprResultOn X e' ν.
Proof.
  intros Hfv Hlce Hlce' HνX HXm Hclosed Hequiv Hmodel.
  pose proof (proj1 (FExprResultOn_iff_let_result_world_on
    X e ν m ltac:(set_solver) Hlce HνX HXm Hclosed) Hmodel)
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
    X e' ν m ltac:(set_solver) Hlce' HνX HXm Hclosed)).
  exists Hfresh, Hresult'.
  rewrite Heq.
  apply let_result_world_on_expr_result_equiv_in_world.
  exact Hequiv.
Qed.

Lemma FExprResultOn_expr_result_equiv_future
    X e e' ν (m : WfWorld) :
  fv_tm e ∪ fv_tm e' ⊆ X →
  lc_tm e →
  lc_tm e' →
  ν ∉ X →
  X ⊆ world_dom (m : World) →
  world_store_closed_on X m →
  expr_result_equiv_future X (res_restrict m X) e e' →
  m ⊨ FExprResultOn X e ν →
  m ⊨ FExprResultOn X e' ν.
Proof.
  intros Hfv Hlce Hlce' HνX HXm Hclosed Hfuture Hmodel.
  eapply FExprResultOn_expr_result_equiv_in_world.
  - exact Hfv.
  - exact Hlce.
  - exact Hlce'.
  - exact HνX.
  - exact HXm.
  - exact Hclosed.
  - apply Hfuture. reflexivity.
  - exact Hmodel.
Qed.
