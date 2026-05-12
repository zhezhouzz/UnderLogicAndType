(** * ChoiceType.DenotationFibers

    Fiber modality helpers for ChoiceType denotations. *)

From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.
From LocallyNameless Require Import Tactics.
From ChoiceType Require Export Syntax.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Local Notation FQ := FormulaQ.

Notation "m ⊨ φ" :=
  (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Notation "φ ⊫ ψ" :=
  (entails φ ψ)
  (at level 85, ψ at level 84, no associativity).

Definition fib_vars_obligation_step
    (x : atom)
    (R : Store → WfWorld → Prop)
    (ρ : Store) (m : WfWorld) : Prop :=
  dom ρ ## {[x]} ∧
  ∀ σ (Hproj : res_restrict m {[x]} σ),
    R (ρ ∪ σ) (res_fiber_from_projection m {[x]} σ Hproj).

Definition fib_vars_acc_step
    (x : atom)
    (acc : FQ * (Store → WfWorld → Prop))
    : FQ * (Store → WfWorld → Prop) :=
  let '(p, R) := acc in
  (FFib x p, fib_vars_obligation_step x R).

Definition fib_vars_acc
    (X : aset) (p : FQ) : FQ * (Store → WfWorld → Prop) :=
  set_fold fib_vars_acc_step
    (p, fun ρ m => res_models_with_store ρ m p) X.

Definition fib_vars (X : aset) (p : FQ) : FQ :=
  fst (fib_vars_acc X p).

Definition fib_vars_obligation
    (X : aset) (p : FQ) (ρ : Store) (m : WfWorld) : Prop :=
  snd (fib_vars_acc X p) ρ m.

Lemma fib_vars_obligation_step_commute x y R ρ (m : WfWorld) :
  x ≠ y →
  x ∈ world_dom (m : World) →
  y ∈ world_dom (m : World) →
  fib_vars_obligation_step y (fib_vars_obligation_step x R) ρ m →
  fib_vars_obligation_step x (fib_vars_obligation_step y R) ρ m.
Proof.
  intros Hxy Hxm Hym [Hρy Hy].
  unfold fib_vars_obligation_step in *.
  split.
  - destruct (world_wf m) as [[σ Hσ] _].
    set (σy := store_restrict σ {[y]}).
    assert (Hprojy : res_restrict m {[y]} σy).
    { exists σ. split; [exact Hσ | reflexivity]. }
    destruct (Hy σy Hprojy) as [Hρσy_x _].
    subst σy.
    rewrite dom_union_L in Hρσy_x.
    rewrite store_restrict_dom in Hρσy_x.
    set_solver.
  - intros σx Hprojx.
    split.
    + rewrite dom_union_L.
      destruct Hprojx as [σ [Hσ Hσx]].
      assert (Hdomσx : dom σx ⊆ {[x]}).
      { rewrite <- Hσx, store_restrict_dom. set_solver. }
      set_solver.
    + intros σy Hprojy_after_x.
      pose proof (res_projection_from_fiber_projection
        m {[x]} {[y]} σx σy Hprojx Hprojy_after_x) as Hprojy.
      assert (Hprojx_after_y :
        res_restrict
          (res_fiber_from_projection m {[y]} σy Hprojy) {[x]} σx).
      {
        assert (Hdomσx : dom σx = {[x]}).
        {
          destruct Hprojx as [σ0 [Hσ0 Hσ0x]].
          rewrite <- Hσ0x, store_restrict_dom.
          pose proof (wfworld_store_dom m σ0 Hσ0) as Hdomσ0.
          set_solver.
        }
        destruct Hprojy_after_x as [σ [Hσfiber_x Hσy]].
        destruct Hσfiber_x as [Hσm Hσx].
        exists σ. split.
        - apply res_fiber_from_projection_member; [exact Hσm | exact Hσy].
        - rewrite <- Hdomσx. exact Hσx.
      }
      destruct (Hy σy Hprojy) as [_ Hyx].
      specialize (Hyx σx Hprojx_after_y).
      assert (Hfib_eq :
        res_fiber_from_projection
          (res_fiber_from_projection m {[y]} σy Hprojy) {[x]} σx Hprojx_after_y =
        res_fiber_from_projection
          (res_fiber_from_projection m {[x]} σx Hprojx) {[y]} σy Hprojy_after_x).
      {
        apply wfworld_ext. apply world_ext.
        - reflexivity.
        - intros τ. simpl. tauto.
      }
      replace (ρ ∪ σx ∪ σy) with (ρ ∪ σy ∪ σx).
      2:{
        assert (Hdomσx : dom σx = {[x]}).
        {
          destruct Hprojx as [σ0 [Hσ0 Hσ0x]].
          rewrite <- Hσ0x, store_restrict_dom.
          pose proof (wfworld_store_dom m σ0 Hσ0) as Hdomσ0.
          set_solver.
        }
        assert (Hdomσy : dom σy = {[y]}).
        {
          destruct Hprojy as [σ0 [Hσ0 Hσ0y]].
          rewrite <- Hσ0y, store_restrict_dom.
          pose proof (wfworld_store_dom m σ0 Hσ0) as Hdomσ0.
          set_solver.
        }
        assert (Hdisj_xy : σx ##ₘ σy).
        {
          apply map_disjoint_dom.
          rewrite Hdomσx, Hdomσy. set_solver.
        }
        rewrite <- (assoc_L (∪) ρ σx σy).
        rewrite <- (assoc_L (∪) ρ σy σx).
        f_equal. symmetry. apply map_union_comm. exact Hdisj_xy.
      }
      rewrite <- Hfib_eq. exact Hyx.
Qed.

Lemma fib_vars_singleton x p :
  fib_vars {[x]} p = FFib x p.
Proof.
  unfold fib_vars, fib_vars_acc.
  rewrite set_fold_singleton. reflexivity.
Qed.

Lemma fib_vars_formula_fv_subset X p :
  formula_fv (fib_vars X p) ⊆ X ∪ formula_fv p.
Proof.
  unfold fib_vars, fib_vars_acc.
  apply (set_fold_ind_L
    (fun acc Y => formula_fv (fst acc) ⊆ Y ∪ formula_fv p)).
  - simpl. set_solver.
  - intros x Y acc Hx HY.
    destruct acc as [q R]. simpl in *.
    intros z Hz.
    apply elem_of_union in Hz as [Hzx | Hzq].
    + set_solver.
    + apply HY in Hzq. set_solver.
Qed.

Lemma fib_vars_formula_fv X p :
  formula_fv (fib_vars X p) = X ∪ formula_fv p.
Proof.
  unfold fib_vars, fib_vars_acc.
  apply (set_fold_ind_L
    (fun acc Y => formula_fv (fst acc) = Y ∪ formula_fv p)).
  - simpl. set_solver.
  - intros x Y acc Hx HY.
    destruct acc as [q R]. simpl in *.
    rewrite HY. set_solver.
Qed.

Lemma formula_rename_atom_fib_vars_fresh a b X p :
  a ∉ X →
  b ∉ X →
  fib_vars X (formula_rename_atom a b p) =
  formula_rename_atom a b (fib_vars X p).
Proof.
  intros Ha Hb.
  unfold fib_vars, fib_vars_acc.
  set (Rel := fun acc1 acc2 : FormulaQ * (Store → WfWorld → Prop) =>
    fst acc1 = fst acc2).
  change (Rel
    (set_fold fib_vars_acc_step
       (formula_rename_atom a b p,
        fun ρ m => res_models_with_store ρ m (formula_rename_atom a b p)) X)
    ((formula_rename_atom a b
        (set_fold fib_vars_acc_step
          (p, fun ρ m => res_models_with_store ρ m p) X).1),
      fun ρ m => res_models_with_store ρ m
        (formula_rename_atom a b
          (set_fold fib_vars_acc_step
            (p, fun ρ m => res_models_with_store ρ m p) X).1))).
  eapply (set_fold_comm_acc_strong Rel fib_vars_acc_step
    (fun acc : FormulaQ * (Store → WfWorld → Prop) =>
       (formula_rename_atom a b (fst acc),
        fun ρ m => res_models_with_store ρ m
          (formula_rename_atom a b (fst acc))))
    (p, fun ρ m => res_models_with_store ρ m p) X).
  - intros x [p1 R1] [p2 R2] Hrel.
    unfold Rel in *. simpl in *. rewrite Hrel. reflexivity.
  - intros x [q R] Hx. unfold Rel. simpl.
    rewrite atom_swap_fresh by set_solver. reflexivity.
  Unshelve.
  constructor.
  + intros [? ?]. reflexivity.
  + intros [? ?] [? ?] [? ?] H12 H23. simpl in *. congruence.
Qed.

Lemma fib_vars_models_elim X p ρ m :
  res_models_with_store ρ m (fib_vars X p) →
  fib_vars_obligation X p ρ m.
Proof.
  unfold fib_vars, fib_vars_obligation, fib_vars_acc.
  apply (set_fold_ind_L
    (fun acc _ =>
      ∀ ρ m, res_models_with_store ρ m (fst acc) → snd acc ρ m)).
  - simpl. auto.
  - intros x Y acc Hx IH ρ0 m0 Hm.
    destruct acc as [q R]. simpl in *.
    unfold fib_vars_obligation_step.
    unfold res_models_with_store in Hm. simpl in Hm.
    destruct Hm as [_ [Hdisj Hfib]].
    split; [exact Hdisj |].
    intros σ Hproj.
    specialize (Hfib σ Hproj).
    eapply IH.
    models_fuel_irrel Hfib.
Qed.

Lemma fib_vars_models_intro X p ρ m :
  formula_scoped_in_world ρ m (fib_vars X p) →
  fib_vars_obligation X p ρ m →
  res_models_with_store ρ m (fib_vars X p).
Proof.
  unfold fib_vars, fib_vars_obligation, fib_vars_acc.
  apply (set_fold_ind_L
    (fun acc _ =>
      ∀ ρ m,
        formula_scoped_in_world ρ m (fst acc) →
        snd acc ρ m →
        res_models_with_store ρ m (fst acc))).
  - simpl. auto.
  - intros x Y acc Hx IH ρ0 m0 Hscope Hobl.
    destruct acc as [q R]. simpl in *.
    unfold fib_vars_obligation_step in Hobl.
    destruct Hobl as [Hdisj Hfib].
    unfold res_models_with_store. simpl.
    split; [exact Hscope |].
    split; [exact Hdisj |].
    intros σ Hproj.
    specialize (Hfib σ Hproj).
    assert (Hscope_q :
      formula_scoped_in_world (ρ0 ∪ σ)
        (res_fiber_from_projection m0 {[x]} σ Hproj) q).
    {
      unfold formula_scoped_in_world in *.
      simpl in Hscope.
      pose proof (wfworld_store_dom (res_restrict m0 {[x]}) σ Hproj) as Hdomσ.
      simpl in Hdomσ.
      rewrite dom_union_L.
      intros z Hz.
      apply elem_of_union in Hz as [Hzρσ | Hzq].
      - apply elem_of_union in Hzρσ as [Hzρ | Hzσ].
        + assert (Hzscope : z ∈ dom ρ0 ∪ ({[x]} ∪ formula_fv q)).
          { set_solver. }
          pose proof (Hscope z Hzscope) as Hzdom.
          simpl in Hzdom. exact Hzdom.
        + rewrite Hdomσ in Hzσ.
          pose proof (Hscope z ltac:(set_solver)) as Hzdom.
          simpl in Hzdom. exact Hzdom.
      - assert (Hzscope : z ∈ dom ρ0 ∪ ({[x]} ∪ formula_fv q)).
        { set_solver. }
        pose proof (Hscope z Hzscope) as Hzdom.
        simpl in Hzdom. exact Hzdom.
    }
    eapply IH; eauto.
Qed.

Lemma fib_vars_obligation_insert_fresh_to_fib
    X x p ρ (m : WfWorld) :
  x ∉ X →
  X ∪ {[x]} ⊆ world_dom (m : World) →
  fib_vars_obligation (X ∪ {[x]}) p ρ m →
  fib_vars_obligation X (FFib x p) ρ m.
Proof.
(** Open: as stated this lemma only has the obligation generated by
    [fib_vars_obligation], but the target base formula is [FFib x p], whose
    satisfaction also needs a scoped model of the fiber formula.  The usable
    version should either take a full model
    [res_models_with_store ρ m (fib_vars (X ∪ {[x]}) p)] or add an explicit
    scopedness invariant for the accumulated fold. *)
Admitted.
