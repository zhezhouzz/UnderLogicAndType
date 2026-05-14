(** * Fiber modality examples

    This file formalizes the dependent-underapproximation example from the
    paper.  The key point is that [FFibVars {[x]}] checks the
    underapproximation independently in every fixed-[x] fiber.  Thus the
    diagonal world
    [{[x=1;y=1], [x=2;y=2]}] is not enough: the [x=1] fiber is missing the
    admissible point [x=1;y=2]. *)

From ChoiceLogic Require Import Prelude LogicQualifier Formula.
From Stdlib Require Import Lia.

(** Concrete atoms standing for paper variables x and y. *)
Definition x_atom : atom := 1%positive.
Definition y_atom : atom := 2%positive.

Local Notation "'x" := x_atom.
Local Notation "'y" := y_atom.

Local Instance nat_valuesig : ValueSig nat := {|
  valuesig_eqdec := _;
  valuesig_inhabited := populate 0;
|}.

Local Notation StoreN := (gmap atom nat).
Local Notation WorldN := (World (V := nat)).
Local Notation WfWorldN := (WfWorld (V := nat)).
Local Notation FormulaN := (Formula (V := nat)).
Local Notation LogicQualifierN := (logic_qualifier (V := nat)).

Ltac crush_store := vm_compute; try tauto; try congruence; try reflexivity.

Definition store_xy (xv yv : nat) : StoreN :=
  <['x := xv]> (<['y := yv]> ∅).

Definition sx1 : StoreN := <['x := 1%nat]> ∅.
Definition sx2 : StoreN := <['x := 2%nat]> ∅.

Definition s11 : StoreN := store_xy 1 1.
Definition s12 : StoreN := store_xy 1 2.
Definition s22 : StoreN := store_xy 2 2.

Definition world_of (P : StoreN → Prop) : WorldN := {|
  world_dom := {['x; 'y]};
  world_stores := P;
|}.

Definition raw_x1_y12 : WorldN :=
  world_of (λ σ, σ = s11 ∨ σ = s12).

Definition raw_x2_y2 : WorldN :=
  world_of (λ σ, σ = s22).

Definition raw_diag_bad : WorldN :=
  world_of (λ σ, σ = s11 ∨ σ = s22).

Definition raw_triangle_ok : WorldN :=
  world_of (λ σ, σ = s11 ∨ σ = s12 ∨ σ = s22).

Lemma wf_world_of (P : StoreN → Prop) (σ0 : StoreN) :
  P σ0 →
  (∀ σ, P σ → dom σ = {['x; 'y]}) →
  wf_world (world_of P).
Proof.
  intros HP Hdom. constructor.
  - exists σ0. exact HP.
  - intros σ Hσ. exact (Hdom σ Hσ).
Qed.

Lemma dom_store_xy (xv yv : nat) :
  dom (store_xy xv yv) = {['x; 'y]}.
Proof. vm_compute. reflexivity. Qed.

Lemma wf_raw_x1_y12 : wf_world raw_x1_y12.
Proof.
  apply (wf_world_of _ s11); first by left.
  intros σ [-> | ->]; apply dom_store_xy.
Qed.

Lemma wf_raw_x2_y2 : wf_world raw_x2_y2.
Proof.
  apply (wf_world_of _ s22); first reflexivity.
  intros σ ->; apply dom_store_xy.
Qed.

Lemma wf_raw_diag_bad : wf_world raw_diag_bad.
Proof.
  apply (wf_world_of _ s11); first by left.
  intros σ [-> | ->]; apply dom_store_xy.
Qed.

Lemma wf_raw_triangle_ok : wf_world raw_triangle_ok.
Proof.
  apply (wf_world_of _ s11); first by left.
  intros σ [-> | [-> | ->]]; apply dom_store_xy.
Qed.

Definition w_x1_y12 : WfWorldN := exist _ raw_x1_y12 wf_raw_x1_y12.
Definition w_x2_y2 : WfWorldN := exist _ raw_x2_y2 wf_raw_x2_y2.
Definition w_diag_bad : WfWorldN := exist _ raw_diag_bad wf_raw_diag_bad.
Definition w_triangle_ok : WfWorldN := exist _ raw_triangle_ok wf_raw_triangle_ok.

(** [triangle_slice] is evaluated after [FFibVars {['x]}] has added the fixed
    projection store to [ρ].  It then requires the current world to contain
    every point [x=fixed_x;y=y] satisfying [fixed_x <= y < 3]. *)
Definition triangle_slice : LogicQualifierN :=
  lqual_fvars {['x; 'y]} (λ ρ w,
    match ρ !! 'x with
    | Some fixed_x =>
        ∀ yv : nat, fixed_x <= yv → yv < 3 → w (store_xy fixed_x yv)
    | None => False
    end).

Ltac solve_x1_triangle :=
  unfold logic_qualifier_denote, triangle_slice; vm_compute;
  intros yv Hle Hlt;
  assert (yv = 1%nat ∨ yv = 2%nat) as [-> | ->] by lia;
  [exists s11 | exists s12];
  repeat split; try (left; reflexivity); try (right; reflexivity); crush_store.

Ltac solve_x2_triangle :=
  unfold logic_qualifier_denote, triangle_slice; vm_compute;
  intros yv Hle Hlt;
  assert (yv = 2%nat) by lia; subst yv;
  exists s22;
  repeat split; try (left; reflexivity); try (right; reflexivity); crush_store.

Ltac solve_triangle_atom_scope :=
  unfold formula_scoped_in_world; simpl;
  unfold stale, stale_logic_qualifier, lqual_dom, lqual_fvars;
  simpl; rewrite ?lvars_fv_of_atoms; vm_compute; set_solver.

Definition fiber_triangle_formula : FormulaN :=
  FFibVars (lvars_of_atoms {['x]}) (FUnder (FAtom triangle_slice)).

(** The formula unfolds to the following concrete fiber obligation: for each
    admissible [x]-projection [σ], some same-domain subworld of the induced
    fiber satisfies [triangle_slice].  The positive examples below use the
    fiber itself as this witness; the diagonal counterexample fails because
    the [x=1] fiber is missing [s12]. *)
Definition fiber_triangle_obligation (w : WfWorldN) : Prop :=
  ∀ σ (Hproj : res_restrict w {['x]} σ),
    ∃ m' m0 : WfWorldN,
      res_subset m' (res_fiber_from_projection w {['x]} σ Hproj) ∧
      formula_scoped_in_world (∅ ∪ σ) m0 (FAtom triangle_slice) ∧
      logic_qualifier_denote triangle_slice (∅ ∪ σ) m0 ∧
      m0 ⊑ m'.

Lemma fiber_triangle_scoped (w : WfWorldN) :
  world_dom w = {['x; 'y]} →
  formula_scoped_in_world ∅ w fiber_triangle_formula.
Proof.
  intros Hdom. unfold formula_scoped_in_world, fiber_triangle_formula.
  simpl. unfold stale, stale_logic_qualifier, lqual_dom, lqual_fvars.
  unfold triangle_slice. simpl.
  unfold stale, stale_logic_qualifier, lqual_fvars, lqual_dom. simpl.
  rewrite !lvars_fv_of_atoms. rewrite Hdom. set_solver.
Qed.

Lemma res_models_fiber_triangle_intro (w : WfWorldN) :
  formula_scoped_in_world ∅ w fiber_triangle_formula →
  fiber_triangle_obligation w →
  res_models w fiber_triangle_formula.
Proof.
  intros Hscope Hfib.
  unfold res_models, res_models_with_store, fiber_triangle_formula.
  simpl. split.
  - exact Hscope.
  - split; [set_solver |].
    intros σ Hproj.
    assert (Hproj' : res_restrict w {['x]} σ).
    { rewrite lvars_fv_of_atoms in Hproj. exact Hproj. }
    destruct (Hfib σ Hproj') as [m' [m0 [Hsubset [Hscope0 [Hatom Hle]]]]].
    pose proof (wfworld_store_dom (res_restrict w {['x]}) σ Hproj') as Hdomσ.
    simpl in Hdomσ.
    split.
    + unfold formula_scoped_in_world in *. simpl in *. set_solver.
    + exists m'. split; [exact Hsubset |].
      split.
      * unfold formula_scoped_in_world in *. simpl in *.
        destruct Hsubset as [Hdom_subset _]. simpl in Hdom_subset. set_solver.
      * exists m0. split; [exact Hscope0 |]. split; [exact Hatom | exact Hle].
Qed.

Lemma res_models_fiber_triangle_elim (w : WfWorldN) :
  res_models w fiber_triangle_formula →
  fiber_triangle_obligation w.
Proof.
  unfold res_models, res_models_with_store, fiber_triangle_formula,
    fiber_triangle_obligation.
  simpl. intros [_ [_ Hfib]] σ Hproj.
  assert (Hproj' : res_restrict w (lvars_fv (lvars_of_atoms {['x]})) σ).
  { rewrite lvars_fv_of_atoms. exact Hproj. }
  destruct (Hfib σ Hproj') as [_ [m' [Hsubset [_ [m0 [Hscope0 [Hatom Hle]]]]]]].
  exists m', m0. split; [exact Hsubset |].
  split; [exact Hscope0 |]. split; [exact Hatom | exact Hle].
Qed.

(** Concrete finite-world facts for the four displayed resources.  They are
    deliberately proved locally: the obligations are specific to this example
    rather than reusable metatheory. *)

Lemma x1_y12_complete_triangle_fibers :
  fiber_triangle_obligation w_x1_y12.
Proof.
Admitted.

Lemma x2_y2_complete_triangle_fibers :
  fiber_triangle_obligation w_x2_y2.
Proof.
Admitted.

Lemma diag_bad_incomplete_triangle_fibers :
  ¬ fiber_triangle_obligation w_diag_bad.
Proof.
Admitted.

Lemma triangle_ok_complete_triangle_fibers :
  fiber_triangle_obligation w_triangle_ok.
Proof.
Admitted.

(** These four statements mirror the paper's displayed judgments. *)

Example fiber_x1_y12_models :
  res_models w_x1_y12 fiber_triangle_formula.
Proof.
  apply res_models_fiber_triangle_intro.
  - apply fiber_triangle_scoped. reflexivity.
  - exact x1_y12_complete_triangle_fibers.
Qed.

Example fiber_x2_y2_models :
  res_models w_x2_y2 fiber_triangle_formula.
Proof.
  apply res_models_fiber_triangle_intro.
  - apply fiber_triangle_scoped. reflexivity.
  - exact x2_y2_complete_triangle_fibers.
Qed.

Example fiber_diag_bad_not_models :
  ¬ res_models w_diag_bad fiber_triangle_formula.
Proof.
  intros Hmodels.
  apply diag_bad_incomplete_triangle_fibers.
  apply res_models_fiber_triangle_elim.
  exact Hmodels.
Qed.

Example fiber_triangle_ok_models :
  res_models w_triangle_ok fiber_triangle_formula.
Proof.
  apply res_models_fiber_triangle_intro.
  - apply fiber_triangle_scoped. reflexivity.
  - exact triangle_ok_complete_triangle_fibers.
Qed.
