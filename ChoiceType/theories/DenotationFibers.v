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

Definition fib_vars_obligation
    (X : aset) (p : FQ) (ρ : Store) (m : WfWorld) : Prop :=
  dom ρ ## X ∧
  ∀ σ (Hproj : res_restrict m X σ),
    res_models_with_store (ρ ∪ σ)
      (res_fiber_from_projection m X σ Hproj) p.

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

Lemma fib_vars_singleton x (p : FQ) :
  FFibVars {[LVFree x]} p = FFibVars {[LVFree x]} p.
Proof.
  reflexivity.
Qed.

Lemma fib_vars_formula_fv_subset D (p : FQ) :
  formula_fv (FFibVars D p) ⊆ lvars_fv D ∪ formula_fv p.
Proof.
  simpl. set_solver.
Qed.

Lemma fib_vars_formula_fv D (p : FQ) :
  formula_fv (FFibVars D p) = lvars_fv D ∪ formula_fv p.
Proof.
  simpl. reflexivity.
Qed.

Lemma formula_rename_atom_fib_vars_fresh a b X (p : FQ) :
  a ∉ X →
  b ∉ X →
  FFibVars (lvars_of_atoms X) (formula_rename_atom a b p) =
  formula_rename_atom a b (FFibVars (lvars_of_atoms X) p).
Proof.
  (* Legacy explicit-swap lemma; superseded by LN opening. *)
Admitted.

Lemma fib_vars_models_elim D (p : FQ) ρ m :
  res_models_with_store ρ m (FFibVars D p) →
  fib_vars_obligation (lvars_fv D) p ρ m.
Proof.
  unfold fib_vars_obligation.
  unfold res_models_with_store. simpl.
  intros Hm. destruct Hm as [_ [Hdisj Hfib]].
  split; [exact Hdisj |].
  intros σ Hproj. models_fuel_irrel (Hfib σ Hproj).
Qed.

Lemma fib_vars_models_intro D (p : FQ) ρ m :
  formula_scoped_in_world ρ m (FFibVars D p) →
  fib_vars_obligation (lvars_fv D) p ρ m →
  res_models_with_store ρ m (FFibVars D p).
Proof.
  unfold fib_vars_obligation.
  intros Hscope [Hdisj Hfib].
  unfold res_models_with_store. simpl.
  split; [exact Hscope |].
  split; [exact Hdisj |].
  intros σ Hproj.
  specialize (Hfib σ Hproj).
  models_fuel_irrel Hfib.
Qed.

Lemma fib_vars_obligation_insert_fresh_to_fib
    X x p ρ (m : WfWorld) :
  x ∉ X →
  X ∪ {[x]} ⊆ world_dom (m : World) →
  fib_vars_obligation (X ∪ {[x]}) p ρ m →
  fib_vars_obligation X (FFibVars (lvars_of_atoms {[x]}) p) ρ m.
Proof.
(** Open: as stated this lemma only has the obligation generated by
    [fib_vars_obligation], but the target base formula is another primitive
    multi-fiber.  The usable version should either take a full model
    [res_models_with_store ρ m (FFibVars (lvars_of_atoms (X ∪ {[x]})) p)] or add an explicit
    scopedness invariant for the accumulated fiber. *)
Admitted.
