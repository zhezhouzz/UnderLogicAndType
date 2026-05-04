(** * Fiber modality examples

    This file formalizes the dependent-underapproximation example from the
    paper.  The key point is that [FFib x] checks the underapproximation
    independently in every fixed-[x] fiber.  Thus the diagonal world
    [{[x=1;y=1], [x=2;y=2]}] is not enough: the [x=1] fiber is missing the
    admissible point [x=1;y=2]. *)

From ChoiceLogic Require Import Prelude LogicQualifier Formula.

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

Definition store_xy (xv yv : nat) : StoreN :=
  <['x := xv]> (<['y := yv]> ∅).

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

(** [triangle_slice] is evaluated after [FFib 'x] has added the fixed
    projection store to [ρ].  It then requires the current world to contain
    every point [x=fixed_x;y=y] satisfying [fixed_x <= y < 3]. *)
Definition triangle_slice : LogicQualifierN :=
  lqual {['x; 'y]} (λ ρ w,
    match ρ !! 'x with
    | Some fixed_x =>
        ∀ yv : nat, fixed_x <= yv → yv < 3 → w (store_xy fixed_x yv)
    | None => False
    end).

Definition fiber_triangle_formula : FormulaN :=
  FFib 'x (FUnder (FAtom triangle_slice)).

(** These four statements mirror the paper's displayed judgments:
    the two single-fiber worlds pass, the diagonal world fails, and the
    combined triangle world passes.  The proofs are intentionally left as
    example obligations; the definitions above are the sanity check payload. *)

Example fiber_x1_y12_models :
  res_models w_x1_y12 fiber_triangle_formula.
Proof. Admitted.

Example fiber_x2_y2_models :
  res_models w_x2_y2 fiber_triangle_formula.
Proof. Admitted.

Example fiber_diag_bad_not_models :
  ¬ res_models w_diag_bad fiber_triangle_formula.
Proof. Admitted.

Example fiber_triangle_ok_models :
  res_models w_triangle_ok fiber_triangle_formula.
Proof. Admitted.
