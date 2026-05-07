(** * ChoiceType.Denotation

    Denotational semantics for the choice type system (§1.5 of the paper).

    The interpretation is given as formulas in [Choice Logic] whose atoms are
    logic qualifiers.  Core expressions are embedded through
    [expr_logic_qual], and type qualifiers are embedded through
    [lift_type_qualifier_to_logic] after they have been opened to closed
    atom-based qualifiers.

    The satisfaction notation [m ⊨ φ] is the central judgment used by
    the typing rules and the fundamental theorem. *)

From LocallyNameless Require Import Tactics.
From ChoiceType Require Export Syntax.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

(** ** ChoiceLogic satisfaction, instantiated for qualifiers *)

(** Local abbreviation for the ChoiceType formula instantiation.  The exported
    name from [Prelude] is [FormulaQ]. *)
Local Notation FQ := FormulaQ.

(** Satisfaction: [m ⊨ φ]  ↔  [res_models m φ] *)
Notation "m ⊨ φ" :=
  (res_models m φ)
  (at level 70, format "m  ⊨  φ").

(** Entailment shorthand: [φ ⊫ ψ]  ↔  [∀ m, m ⊨ φ → m ⊨ ψ] *)
Notation "φ ⊫ ψ" :=
  (entails φ ψ)
  (at level 85, ψ at level 84, no associativity).

(** ** Logic atoms and fresh variable helpers for denotation *)

Definition fib_vars (X : aset) (p : FQ) : FQ :=
  set_fold FFib p X.

Lemma fib_vars_formula_fv_subset X p :
  formula_fv (fib_vars X p) ⊆ X ∪ formula_fv p.
Proof.
  unfold fib_vars.
  apply (set_fold_ind_L (fun r Y => formula_fv r ⊆ Y ∪ formula_fv p));
    simpl; set_solver.
Qed.

Definition expr_logic_qual (e : tm) (ν : atom) : logic_qualifier :=
  lqual (stale e ∪ {[ν]}) (fun σ (w : WfWorld) =>
    ∀ σw,
      (w : World) σw →
      ∃ v,
        σw !! ν = Some v ∧
        subst_map σw (subst_map σ e) →* tret v).

(** ** Type measure for denotation fuel

    As in HATs' denotation, the first argument of [denot_ty_fuel] is an
    over-approximation of the syntactic size of the type.  This lets the
    denotation recurse on opened locally-nameless bodies such as
    [{0 ~> x} τ], which are not syntactic subterms accepted by Rocq's
    structural termination checker. *)
Fixpoint cty_measure (τ : choice_ty) : nat :=
  match τ with
  | CTOver _ _ | CTUnder _ _ => 1
  | CTInter τ1 τ2
  | CTUnion τ1 τ2
  | CTSum τ1 τ2
  | CTArrow τ1 τ2
  | CTWand τ1 τ2 => 1 + cty_measure τ1 + cty_measure τ2
  end.

Lemma cty_measure_gt_0 τ : cty_measure τ > 0.
Proof. induction τ; simpl; lia. Qed.

Lemma cty_open_preserves_measure τ k x :
  cty_measure ({k ~> x} τ) = cty_measure τ.
Proof. induction τ in k |- *; simpl; eauto; lia. Qed.

Lemma cty_swap_preserves_measure x y τ :
  cty_measure (cty_swap_atom x y τ) = cty_measure τ.
Proof. induction τ; simpl; eauto; lia. Qed.

(** ** Type denotation

    [denot_ty_fuel gas D Σ τ e] encodes the proposition "expression [e] has
    type [τ]" as a Choice Logic formula under erased basic environment [Σ].
    The finite set [D] is an avoidance set for generated binder
    representatives.  These names only make the syntax concrete:
    [FForall]'s cofinite semantics interprets each binder by renaming the
    representative to every sufficiently fresh atom. *)

Fixpoint denot_ty_fuel
    (gas : nat) (D : aset) (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  match gas with
  | 0 => FFalse
  | S gas' =>
  match τ with

  (** {ν:b | φ}  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ◁φ
      [fib_vars (fv φ)] iterates the single-variable fiber modality over
      φ's free variables. *)
  | CTOver b φ =>
      fresh_forall (D ∪ fv_tm e ∪ qual_dom φ) (fun ν =>
      let φν := qual_open_atom 0 ν φ in
        (FImpl (FAtom (expr_logic_qual e ν))
               (FAnd
                 (basic_world_formula (<[ν := TBase b]> Σ) ({[ν]} ∪ qual_dom φν))
                 (fib_vars (qual_dom φν)
                   (FOver (FAtom (lift_type_qualifier_to_logic φν)))))))

  (** [ν:b | φ]  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ▷φ *)
  | CTUnder b φ =>
      fresh_forall (D ∪ fv_tm e ∪ qual_dom φ) (fun ν =>
      let φν := qual_open_atom 0 ν φ in
        (FImpl (FAtom (expr_logic_qual e ν))
               (FAnd
                 (basic_world_formula (<[ν := TBase b]> Σ) ({[ν]} ∪ qual_dom φν))
                 (fib_vars (qual_dom φν)
                   (FUnder (FAtom (lift_type_qualifier_to_logic φν)))))))

  (** τ1 ⊓ τ2  ≝  ⟦τ1⟧ e ∧ ⟦τ2⟧ e *)
  | CTInter τ1 τ2 =>
      FAnd (denot_ty_fuel gas' D Σ τ1 e) (denot_ty_fuel gas' D Σ τ2 e)

  (** τ1 ⊔ τ2  ≝  ⟦τ1⟧ e ∨ ⟦τ2⟧ e *)
  | CTUnion τ1 τ2 =>
      FOr (denot_ty_fuel gas' D Σ τ1 e) (denot_ty_fuel gas' D Σ τ2 e)

  (** τ1 ⊕ τ2  ≝  ⟦τ1⟧ e ⊕ ⟦τ2⟧ e *)
  | CTSum τ1 τ2 =>
      FPlus (denot_ty_fuel gas' D Σ τ1 e) (denot_ty_fuel gas' D Σ τ2 e)

  (** τ_x →, τ  ≝  ∀y. ⟦e⟧_y ⇒ ∀{y}.∀x.(⟦τ_x⟧ x ⇒ ⟦τ[x]⟧ (y x)). *)
  | CTArrow τx τ =>
      let Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ in
      fresh_forall Dy (fun y =>
      let Dx := {[y]} ∪ Dy in
        (FImpl
          (FAtom (expr_logic_qual e y))
          (fresh_forall Dx (fun x =>
          let D2 := {[x]} ∪ Dx in
            FFib y
              (FImpl
                (denot_ty_fuel gas' D2 (<[x := erase_ty τx]> Σ) τx (tret (vfvar x)))
                (denot_ty_fuel gas' D2 (<[x := erase_ty τx]> Σ) ({0 ~> x} τ)
                   (tapp (vfvar y) (vfvar x))))))))

  (** τ_x ⊸ τ  ≝  ∀y. ⟦e⟧_y ⇒ ∀{y}.∀x.(⟦τ_x⟧ x −∗ ⟦τ[x]⟧ (y x)). *)
  | CTWand τx τ =>
      let Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ in
      fresh_forall Dy (fun y =>
      let Dx := {[y]} ∪ Dy in
        (FImpl
          (FAtom (expr_logic_qual e y))
          (fresh_forall Dx (fun x =>
          let D2 := {[x]} ∪ Dx in
            FFib y
              (FWand
                (denot_ty_fuel gas' D2 (<[x := erase_ty τx]> Σ) τx (tret (vfvar x)))
                (denot_ty_fuel gas' D2 (<[x := erase_ty τx]> Σ) ({0 ~> x} τ)
                   (tapp (vfvar y) (vfvar x))))))))

  end
  end.

Definition denot_ty_avoiding
    (D : aset) (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_fuel (cty_measure τ) D Σ τ e.

Definition denot_ty_under (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_avoiding (fv_cty τ ∪ fv_tm e) Σ τ e.

Definition denot_ty (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under ∅ τ e.

Definition denot_ty_in_ctx (Γ : ctx) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under (erase_ctx Γ) τ e.

Definition ty_env_agree_on (X : aset) (Σ1 Σ2 : gmap atom ty) : Prop :=
  ∀ x, x ∈ X → Σ1 !! x = Σ2 !! x.

Lemma ty_env_agree_on_mono X Y Σ1 Σ2 :
  X ⊆ Y →
  ty_env_agree_on Y Σ1 Σ2 →
  ty_env_agree_on X Σ1 Σ2.
Proof.
  intros HXY Hagree z Hz. apply Hagree. apply HXY. exact Hz.
Qed.

Lemma ty_env_agree_on_insert_same X Σ1 Σ2 x T :
  ty_env_agree_on (X ∖ {[x]}) Σ1 Σ2 →
  ty_env_agree_on X (<[x := T]> Σ1) (<[x := T]> Σ2).
Proof.
  intros Hagree z Hz.
  destruct (decide (z = x)) as [->|Hne].
  - rewrite !(lookup_insert_eq _ x T). reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    apply Hagree. set_solver.
Qed.

Lemma ty_env_agree_on_insert_same_keep X Σ1 Σ2 x T :
  ty_env_agree_on X Σ1 Σ2 →
  ty_env_agree_on (X ∪ {[x]}) (<[x := T]> Σ1) (<[x := T]> Σ2).
Proof.
  intros Hagree.
  apply ty_env_agree_on_insert_same.
  intros z Hz. apply Hagree. set_solver.
Qed.

Lemma ty_env_agree_on_open_qual_result D Σ1 Σ2 b φ ν :
  ty_env_agree_on (D ∪ qual_dom φ) Σ1 Σ2 →
  ty_env_agree_on ({[ν]} ∪ qual_dom (qual_open_atom 0 ν φ))
    (<[ν := TBase b]> Σ1) (<[ν := TBase b]> Σ2).
Proof.
  intros Hagree z Hz.
  destruct (decide (z = ν)) as [->|Hne].
  - rewrite !(lookup_insert_eq _ ν (TBase b)). reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    apply Hagree.
    pose proof (qual_open_atom_dom_subset 0 ν φ z) as Hdom.
    set_solver.
Qed.

Definition formula_equiv (φ ψ : FQ) : Prop :=
  (φ ⊫ ψ) ∧ (ψ ⊫ φ).

Notation "φ '⊣⊢' ψ" := (formula_equiv φ ψ)
  (at level 85, no associativity).

Lemma formula_equiv_refl φ : φ ⊣⊢ φ.
Proof. split; intros m Hm; exact Hm. Qed.

Lemma formula_equiv_sym φ ψ :
  φ ⊣⊢ ψ → ψ ⊣⊢ φ.
Proof. intros [H1 H2]. split; assumption. Qed.

Lemma formula_equiv_trans φ ψ χ :
  φ ⊣⊢ ψ → ψ ⊣⊢ χ → φ ⊣⊢ χ.
Proof.
  intros [Hφψ Hψφ] [Hψχ Hχψ]. split; intros m Hm; eauto.
Qed.

Lemma denot_ty_fuel_env_agree gas D Σ1 Σ2 τ e :
  ty_env_agree_on (fv_cty τ) Σ1 Σ2 →
  denot_ty_fuel gas D Σ1 τ e = denot_ty_fuel gas D Σ2 τ e.
Proof.
  revert D Σ1 Σ2 τ e.
  induction gas as [|gas IH]; intros D Σ1 Σ2 τ e Hagree; [reflexivity |].
  destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ]; simpl in *.
  - unfold fresh_forall.
    set (ν := fresh_for (D ∪ fv_tm e ∪ qual_dom φ)).
    set (φν := qual_open_atom 0 ν φ).
    assert (Hbasic :
      basic_world_formula (<[ν:=TBase b]> Σ1) ({[ν]} ∪ qual_dom φν) =
      basic_world_formula (<[ν:=TBase b]> Σ2) ({[ν]} ∪ qual_dom φν)).
    {
      apply basic_world_formula_agree.
      intros z Hz.
      destruct (decide (z = ν)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree.
        pose proof (qual_open_atom_dom_subset 0 ν φ z) as Hdom.
        set_solver.
    }
    rewrite Hbasic. reflexivity.
  - unfold fresh_forall.
    set (ν := fresh_for (D ∪ fv_tm e ∪ qual_dom φ)).
    set (φν := qual_open_atom 0 ν φ).
    assert (Hbasic :
      basic_world_formula (<[ν:=TBase b]> Σ1) ({[ν]} ∪ qual_dom φν) =
      basic_world_formula (<[ν:=TBase b]> Σ2) ({[ν]} ∪ qual_dom φν)).
    {
      apply basic_world_formula_agree.
      intros z Hz.
      destruct (decide (z = ν)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree.
        pose proof (qual_open_atom_dom_subset 0 ν φ z) as Hdom.
        set_solver.
    }
    rewrite Hbasic. reflexivity.
  - rewrite (IH D Σ1 Σ2 τ1 e).
    + rewrite (IH D Σ1 Σ2 τ2 e); [reflexivity |].
      intros z Hz. apply Hagree. set_solver.
    + intros z Hz. apply Hagree. set_solver.
  - rewrite (IH D Σ1 Σ2 τ1 e).
    + rewrite (IH D Σ1 Σ2 τ2 e); [reflexivity |].
      intros z Hz. apply Hagree. set_solver.
    + intros z Hz. apply Hagree. set_solver.
  - rewrite (IH D Σ1 Σ2 τ1 e).
    + rewrite (IH D Σ1 Σ2 τ2 e); [reflexivity |].
      intros z Hz. apply Hagree. set_solver.
    + intros z Hz. apply Hagree. set_solver.
  - unfold fresh_forall.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    set (Dx := {[y]} ∪ Dy).
    set (x := fresh_for Dx).
    set (D2 := {[x]} ∪ Dx).
    assert (Harg :
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ1) τx (tret (vfvar x)) =
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ2) τx (tret (vfvar x))).
    {
      apply IH.
      intros z Hz.
      destruct (decide (z = x)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree. simpl in Hz. set_solver.
    }
    assert (Hres :
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ1) ({0 ~> x} τ)
        (tapp (vfvar y) (vfvar x)) =
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ2) ({0 ~> x} τ)
        (tapp (vfvar y) (vfvar x))).
    {
      apply IH.
      intros z Hz.
      destruct (decide (z = x)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree.
        pose proof (cty_open_fv_subset 0 x τ) as Hopen.
        simpl in Hz. set_solver.
    }
    repeat (f_equal; try assumption).
  - unfold fresh_forall.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    set (Dx := {[y]} ∪ Dy).
    set (x := fresh_for Dx).
    set (D2 := {[x]} ∪ Dx).
    assert (Harg :
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ1) τx (tret (vfvar x)) =
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ2) τx (tret (vfvar x))).
    {
      apply IH.
      intros z Hz.
      destruct (decide (z = x)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree. simpl in Hz. set_solver.
    }
    assert (Hres :
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ1) ({0 ~> x} τ)
        (tapp (vfvar y) (vfvar x)) =
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ2) ({0 ~> x} τ)
        (tapp (vfvar y) (vfvar x))).
    {
      apply IH.
      intros z Hz.
      destruct (decide (z = x)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree.
        pose proof (cty_open_fv_subset 0 x τ) as Hopen.
        simpl in Hz. set_solver.
    }
    repeat (f_equal; try assumption).
Qed.

Lemma denot_ty_under_env_agree Σ1 Σ2 τ e :
  ty_env_agree_on (fv_cty τ) Σ1 Σ2 →
  denot_ty_under Σ1 τ e = denot_ty_under Σ2 τ e.
Proof.
  intros Hagree.
  unfold denot_ty_under, denot_ty_avoiding.
  apply denot_ty_fuel_env_agree. exact Hagree.
Qed.

Lemma denot_ty_under_env_equiv Σ1 Σ2 τ e :
  ty_env_agree_on (fv_cty τ) Σ1 Σ2 →
  denot_ty_under Σ1 τ e ⊣⊢ denot_ty_under Σ2 τ e.
Proof.
  intros Hagree.
  rewrite (denot_ty_under_env_agree Σ1 Σ2 τ e Hagree).
  apply formula_equiv_refl.
Qed.

Lemma denot_ty_in_ctx_env_agree Γ1 Γ2 τ e :
  ty_env_agree_on (fv_cty τ) (erase_ctx Γ1) (erase_ctx Γ2) →
  denot_ty_in_ctx Γ1 τ e = denot_ty_in_ctx Γ2 τ e.
Proof.
  unfold denot_ty_in_ctx. apply denot_ty_under_env_agree.
Qed.

Lemma denot_ty_in_ctx_env_equiv Γ1 Γ2 τ e :
  ty_env_agree_on (fv_cty τ) (erase_ctx Γ1) (erase_ctx Γ2) →
  denot_ty_in_ctx Γ1 τ e ⊣⊢ denot_ty_in_ctx Γ2 τ e.
Proof.
  unfold denot_ty_in_ctx. apply denot_ty_under_env_equiv.
Qed.

(** ** Denotation scoping regularity

    These syntactic facts isolate the variable-accounting needed by semantic
    subtyping reflexivity.  They are intentionally stated at the denotation
    layer: typing proofs should consume these regularity lemmas rather than
    unfolding the formula generated for each type constructor. *)

Lemma denot_ty_formula_fv_subset τ e :
  formula_fv (denot_ty τ e) ⊆ fv_tm e ∪ fv_cty τ.
Proof. Admitted.

Lemma denot_ty_fuel_formula_fv_env_agree gas D Σ1 Σ2 τ e :
  formula_fv (denot_ty_fuel gas D Σ1 τ e) =
  formula_fv (denot_ty_fuel gas D Σ2 τ e).
Proof.
  revert D Σ1 Σ2 τ e.
  induction gas as [|gas IH]; intros D Σ1 Σ2 τ e; [reflexivity |].
  destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ]; simpl in *.
  - unfold fresh_forall.
    set (ν := fresh_for (D ∪ fv_tm e ∪ qual_dom φ)).
    set (φν := qual_open_atom 0 ν φ).
    reflexivity.
  - unfold fresh_forall.
    set (ν := fresh_for (D ∪ fv_tm e ∪ qual_dom φ)).
    set (φν := qual_open_atom 0 ν φ).
    reflexivity.
  - rewrite (IH D Σ1 Σ2 τ1 e), (IH D Σ1 Σ2 τ2 e). reflexivity.
  - rewrite (IH D Σ1 Σ2 τ1 e), (IH D Σ1 Σ2 τ2 e). reflexivity.
  - rewrite (IH D Σ1 Σ2 τ1 e), (IH D Σ1 Σ2 τ2 e). reflexivity.
  - unfold fresh_forall.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    set (Dx := {[y]} ∪ Dy).
    set (x := fresh_for Dx).
    set (D2 := {[x]} ∪ Dx).
    rewrite (IH D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      τx (tret (vfvar x))).
    rewrite (IH D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      ({0 ~> x} τ) (tapp (vfvar y) (vfvar x))).
    reflexivity.
  - unfold fresh_forall.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    set (Dx := {[y]} ∪ Dy).
    set (x := fresh_for Dx).
    set (D2 := {[x]} ∪ Dx).
    rewrite (IH D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      τx (tret (vfvar x))).
    rewrite (IH D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      ({0 ~> x} τ) (tapp (vfvar y) (vfvar x))).
    reflexivity.
Qed.

Lemma denot_ty_under_formula_fv_subset Σ τ e :
  formula_fv (denot_ty_under Σ τ e) ⊆ fv_tm e ∪ fv_cty τ.
Proof.
  unfold denot_ty_under, denot_ty_avoiding.
  rewrite (denot_ty_fuel_formula_fv_env_agree
    (cty_measure τ) (fv_cty τ ∪ fv_tm e) Σ ∅ τ e).
  exact (denot_ty_formula_fv_subset τ e).
Qed.

Lemma denot_ty_under_result_atom_fv Σ x τ :
  x ∈ formula_fv (denot_ty_under Σ τ (tret (vfvar x))).
Proof.
  unfold denot_ty_under, denot_ty_avoiding.
  assert (Hfuel :
    ∀ gas D Σ0 τ0 z,
      cty_measure τ0 <= gas →
      z ∈ D →
      z ∈ formula_fv (denot_ty_fuel gas D Σ0 τ0 (tret (vfvar z)))).
  {
    induction gas as [|gas IH]; intros D Σ0 τ0 z Hgas HzD.
    { pose proof (cty_measure_gt_0 τ0). lia. }
    destruct τ0 as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τ1 τ2|τ1 τ2]; simpl in *.
    - unfold fresh_forall. simpl.
      set (ν := fresh_for (D ∪ {[z]} ∪ qual_dom φ)).
      assert (Hzν : z ≠ ν).
      {
        subst ν. pose proof (fresh_for_not_in (D ∪ {[z]} ∪ qual_dom φ)).
        set_solver.
      }
      apply elem_of_difference. split.
      + apply elem_of_union. left.
        change (z ∈ fv_tm (tret (vfvar z)) ∪ {[ν]}). simpl. set_solver.
      + intros Hzνin. apply elem_of_singleton in Hzνin.
        exact (Hzν Hzνin).
    - unfold fresh_forall. simpl.
      set (ν := fresh_for (D ∪ {[z]} ∪ qual_dom φ)).
      assert (Hzν : z ≠ ν).
      {
        subst ν. pose proof (fresh_for_not_in (D ∪ {[z]} ∪ qual_dom φ)).
        set_solver.
      }
      apply elem_of_difference. split.
      + apply elem_of_union. left.
        change (z ∈ fv_tm (tret (vfvar z)) ∪ {[ν]}). simpl. set_solver.
      + intros Hzνin. apply elem_of_singleton in Hzνin.
        exact (Hzν Hzνin).
    - apply elem_of_union. left.
      apply IH; [lia | exact HzD].
    - apply elem_of_union. left.
      apply IH; [lia | exact HzD].
    - apply elem_of_union. left.
      apply IH; [lia | exact HzD].
    - unfold fresh_forall. simpl.
      set (y := fresh_for (D ∪ {[z]} ∪ fv_cty τ1 ∪ fv_cty τ2)).
      assert (Hzy : z ≠ y).
      {
        subst y. pose proof (fresh_for_not_in (D ∪ {[z]} ∪ fv_cty τ1 ∪ fv_cty τ2)).
        set_solver.
      }
      apply elem_of_difference. split.
      + apply elem_of_union. left.
        change (z ∈ fv_tm (tret (vfvar z)) ∪ {[y]}). simpl. set_solver.
      + intros Hzyin. apply elem_of_singleton in Hzyin.
        exact (Hzy Hzyin).
    - unfold fresh_forall. simpl.
      set (y := fresh_for (D ∪ {[z]} ∪ fv_cty τ1 ∪ fv_cty τ2)).
      assert (Hzy : z ≠ y).
      {
        subst y. pose proof (fresh_for_not_in (D ∪ {[z]} ∪ fv_cty τ1 ∪ fv_cty τ2)).
        set_solver.
      }
      apply elem_of_difference. split.
      + apply elem_of_union. left.
        change (z ∈ fv_tm (tret (vfvar z)) ∪ {[y]}). simpl. set_solver.
      + intros Hzyin. apply elem_of_singleton in Hzyin.
        exact (Hzy Hzyin).
  }
  apply Hfuel.
  - reflexivity.
  - simpl. set_solver.
Qed.

Lemma denot_ty_result_atom_fv x τ :
  x ∈ formula_fv (denot_ty τ (tret (vfvar x))).
Proof. apply denot_ty_under_result_atom_fv. Qed.

Lemma denot_ty_restrict_fv τ e m :
  m ⊨ denot_ty τ e →
  res_restrict m (fv_tm e ∪ fv_cty τ) ⊨ denot_ty τ e.
Proof.
  intros Hm.
  eapply res_models_kripke.
  - apply res_restrict_mono. apply denot_ty_formula_fv_subset.
  - apply res_models_restrict_fv. exact Hm.
Qed.

Lemma denot_ty_under_restrict_fv Σ τ e m :
  m ⊨ denot_ty_under Σ τ e →
  res_restrict m (fv_tm e ∪ fv_cty τ) ⊨ denot_ty_under Σ τ e.
Proof.
  intros Hm.
  eapply res_models_kripke.
  - apply res_restrict_mono. apply denot_ty_under_formula_fv_subset.
  - apply res_models_restrict_fv. exact Hm.
Qed.

(** ** Context denotation

    [denot_ctx_under Σ Γ] is the formula that holds when [Γ] is satisfied
    under the ambient erased basic environment [Σ].  The public
    [denot_ctx Γ] instantiates [Σ] with [erase_ctx Γ], so later binders in a
    comma context can be checked against earlier erased bindings. *)
Fixpoint denot_ctx_under (Σ : gmap atom ty) (Γ : ctx) : FQ :=
  match Γ with
  | CtxEmpty        => FTrue
  | CtxBind x τ    => denot_ty_under Σ τ (tret (vfvar x))
  | CtxComma Γ1 Γ2 => FAnd  (denot_ctx_under Σ Γ1) (denot_ctx_under Σ Γ2)
  | CtxStar  Γ1 Γ2 => FStar (denot_ctx_under Σ Γ1) (denot_ctx_under Σ Γ2)
  | CtxSum   Γ1 Γ2 => FPlus (denot_ctx_under Σ Γ1) (denot_ctx_under Σ Γ2)
  end.

Definition denot_ctx (Γ : ctx) : FQ :=
  denot_ctx_under (erase_ctx Γ) Γ.

(** ** Typeclass instances for [⟦⟧] notation *)

#[global] Instance denot_cty_inst :
    Denotation choice_ty (tm → FQ) := denot_ty.
#[global] Instance denot_ctx_inst :
    Denotation ctx FQ := denot_ctx.
Arguments denot_cty_inst /.
Arguments denot_ctx_inst /.

Lemma denot_ctx_under_dom_subset_formula_fv Σ Γ :
  ctx_dom Γ ⊆ formula_fv (denot_ctx_under Σ Γ).
Proof.
  induction Γ; simpl; try set_solver.
  intros z Hz. apply elem_of_singleton in Hz. subst.
  apply denot_ty_under_result_atom_fv.
Qed.

Lemma denot_ctx_dom_subset_formula_fv Γ :
  ctx_dom Γ ⊆ formula_fv (denot_ctx Γ).
Proof.
  unfold denot_ctx. apply denot_ctx_under_dom_subset_formula_fv.
Qed.

Lemma denot_ctx_models_dom Γ m :
  m ⊨ ⟦Γ⟧ →
  ctx_dom Γ ⊆ world_dom m.
Proof.
  intros Hmodels z Hz.
  pose proof (res_models_with_store_fuel_scoped
    (formula_measure (denot_ctx Γ)) ∅ m (denot_ctx Γ) Hmodels) as Hscope.
  unfold formula_scoped_in_world in Hscope.
  apply Hscope.
  pose proof (denot_ctx_dom_subset_formula_fv Γ z Hz).
  set_solver.
Qed.

(** With these instances:
      [⟦τ⟧ e]  unfolds to [denot_ty τ e]
      [⟦Γ⟧]    unfolds to [denot_ctx Γ]              *)

(** ** Key semantic lemmas *)

Local Ltac solve_ctx_fuel Γ1 Γ2 :=
  unfold denote, denot_ctx_inst in *;
  simpl;
  repeat rewrite Nat.add_0_l;
  repeat rewrite Nat.add_0_r;
  pose proof (formula_measure_pos (denot_ctx Γ1));
  pose proof (formula_measure_pos (denot_ctx Γ2));
  lia.

Local Ltac change_ctx_fuel H Γ1 Γ2 :=
  match type of H with
  | res_models_with_store_fuel ?gas ?ρ ?m ?φ =>
      eapply (res_models_with_store_fuel_irrel gas _ ρ m φ);
      [solve_ctx_fuel Γ1 Γ2 | solve_ctx_fuel Γ1 Γ2 | exact H]
  end.

(** Monotonicity: if m ⊨ ⟦Γ⟧ and m ≤ m', then m' ⊨ ⟦Γ⟧ for comma contexts. *)
Lemma denot_ctx_mono_comma (Γ : ctx) m m' :
  m ⊨ ⟦Γ⟧ →
  m ⊑ m' →
  m' ⊨ ⟦Γ⟧.
Proof.
  unfold denot_ctx_inst, res_models, res_models_with_store.
  intros Hmodels Hle. eapply res_models_with_store_fuel_kripke; eauto.
Qed.

(** Environment-indexed context denotations distribute structurally when the
    same ambient erased environment is used for both subcontexts. *)
Lemma denot_ctx_under_comma Σ Γ1 Γ2 m :
  m ⊨ denot_ctx_under Σ (CtxComma Γ1 Γ2) ↔
  m ⊨ denot_ctx_under Σ Γ1 ∧ m ⊨ denot_ctx_under Σ Γ2.
Proof.
  unfold res_models, res_models_with_store. simpl.
  split.
  - intros [Hscope [HΓ1 HΓ2]]. split.
    + eapply res_models_with_store_fuel_irrel; [| | exact HΓ1]; simpl; lia.
    + eapply res_models_with_store_fuel_irrel; [| | exact HΓ2]; simpl; lia.
  - intros [HΓ1 HΓ2]. split.
    + unfold formula_scoped_in_world in *. simpl.
      pose proof (res_models_with_store_fuel_scoped _ ∅ m (denot_ctx_under Σ Γ1) HΓ1).
      pose proof (res_models_with_store_fuel_scoped _ ∅ m (denot_ctx_under Σ Γ2) HΓ2).
      set_solver.
    + split.
      * eapply res_models_with_store_fuel_irrel; [| | exact HΓ1]; simpl; lia.
      * eapply res_models_with_store_fuel_irrel; [| | exact HΓ2]; simpl; lia.
Qed.

Lemma denot_ctx_under_star Σ Γ1 Γ2 m :
  m ⊨ denot_ctx_under Σ (CtxStar Γ1 Γ2) ↔
  ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m ∧
    m1 ⊨ denot_ctx_under Σ Γ1 ∧ m2 ⊨ denot_ctx_under Σ Γ2.
Proof.
  unfold res_models, res_models_with_store. simpl.
  split.
  - intros [_ [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]]].
    exists m1, m2, Hc. split; [exact Hprod |]. split.
    + eapply res_models_with_store_fuel_irrel; [| | exact HΓ1]; simpl; lia.
    + eapply res_models_with_store_fuel_irrel; [| | exact HΓ2]; simpl; lia.
  - intros [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]].
    split.
    + unfold formula_scoped_in_world in *. simpl.
      pose proof (res_models_with_store_fuel_scoped _ ∅ m1 (denot_ctx_under Σ Γ1) HΓ1).
      pose proof (res_models_with_store_fuel_scoped _ ∅ m2 (denot_ctx_under Σ Γ2) HΓ2).
      pose proof (raw_le_dom _ _ Hprod). set_solver.
    + exists m1, m2, Hc. split; [exact Hprod |]. split.
      * eapply res_models_with_store_fuel_irrel; [| | exact HΓ1]; simpl; lia.
      * eapply res_models_with_store_fuel_irrel; [| | exact HΓ2]; simpl; lia.
Qed.

Lemma denot_ctx_under_sum Σ Γ1 Γ2 m :
  m ⊨ denot_ctx_under Σ (CtxSum Γ1 Γ2) ↔
  ∃ (m1 m2 : WfWorld) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ m ∧
    m1 ⊨ denot_ctx_under Σ Γ1 ∧ m2 ⊨ denot_ctx_under Σ Γ2.
Proof.
  unfold res_models, res_models_with_store. simpl.
  split.
  - intros [_ [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]]].
    exists m1, m2, Hdef. split; [exact Hsum |]. split.
    + eapply res_models_with_store_fuel_irrel; [| | exact HΓ1]; simpl; lia.
    + eapply res_models_with_store_fuel_irrel; [| | exact HΓ2]; simpl; lia.
  - intros [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]].
    split.
    + unfold formula_scoped_in_world in *. simpl.
      pose proof (res_models_with_store_fuel_scoped _ ∅ m1 (denot_ctx_under Σ Γ1) HΓ1) as Hscope1.
      pose proof (res_models_with_store_fuel_scoped _ ∅ m2 (denot_ctx_under Σ Γ2) HΓ2) as Hscope2.
      pose proof (raw_le_dom _ _ Hsum) as Hdom_sum_m.
      unfold raw_sum_defined in Hdef. simpl in Hdom_sum_m.
      intros z Hz. apply elem_of_union in Hz as [Hzempty | Hzfv]; [set_solver |].
      apply elem_of_union in Hzfv as [Hz | Hz].
      * apply Hdom_sum_m. apply Hscope1. set_solver.
      * apply Hdom_sum_m. rewrite Hdef. apply Hscope2. set_solver.
    + exists m1, m2, Hdef. split; [exact Hsum |]. split.
      * eapply res_models_with_store_fuel_irrel; [| | exact HΓ1]; simpl; lia.
      * eapply res_models_with_store_fuel_irrel; [| | exact HΓ2]; simpl; lia.
Qed.

Lemma denot_ctx_under_bind Σ x τ m :
  m ⊨ denot_ctx_under Σ (CtxBind x τ) ↔
  m ⊨ denot_ty_under Σ τ (tret (vfvar x)).
Proof. reflexivity. Qed.

Lemma denot_ctx_under_env_equiv Σ1 Σ2 Γ :
  ty_env_agree_on (ctx_stale Γ) Σ1 Σ2 →
  denot_ctx_under Σ1 Γ ⊣⊢ denot_ctx_under Σ2 Γ.
Proof.
  induction Γ in Σ1, Σ2 |- *; intros Hagree.
  - apply formula_equiv_refl.
  - simpl in Hagree.
    apply denot_ty_under_env_equiv.
    intros z Hz. apply Hagree. simpl. set_solver.
  - simpl in Hagree.
    pose proof (IHΓ1 Σ1 Σ2 ltac:(intros z Hz; apply Hagree; set_solver))
      as [H12_1 H21_1].
    pose proof (IHΓ2 Σ1 Σ2 ltac:(intros z Hz; apply Hagree; set_solver))
      as [H12_2 H21_2].
    split; intros m Hm.
    + apply denot_ctx_under_comma in Hm as [HΓ1 HΓ2].
      apply denot_ctx_under_comma. split; eauto.
    + apply denot_ctx_under_comma in Hm as [HΓ1 HΓ2].
      apply denot_ctx_under_comma. split; eauto.
  - simpl in Hagree.
    pose proof (IHΓ1 Σ1 Σ2 ltac:(intros z Hz; apply Hagree; set_solver))
      as [H12_1 H21_1].
    pose proof (IHΓ2 Σ1 Σ2 ltac:(intros z Hz; apply Hagree; set_solver))
      as [H12_2 H21_2].
    split; intros m Hm.
    + apply denot_ctx_under_star in Hm as [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]].
      apply denot_ctx_under_star.
      exists m1, m2, Hc. split; [exact Hprod |]. split; eauto.
    + apply denot_ctx_under_star in Hm as [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]].
      apply denot_ctx_under_star.
      exists m1, m2, Hc. split; [exact Hprod |]. split; eauto.
  - simpl in Hagree.
    pose proof (IHΓ1 Σ1 Σ2 ltac:(intros z Hz; apply Hagree; set_solver))
      as [H12_1 H21_1].
    pose proof (IHΓ2 Σ1 Σ2 ltac:(intros z Hz; apply Hagree; set_solver))
      as [H12_2 H21_2].
    split; intros m Hm.
    + apply denot_ctx_under_sum in Hm as [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]].
      apply denot_ctx_under_sum.
      exists m1, m2, Hdef. split; [exact Hsum |]. split; eauto.
    + apply denot_ctx_under_sum in Hm as [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]].
      apply denot_ctx_under_sum.
      exists m1, m2, Hdef. split; [exact Hsum |]. split; eauto.
Qed.

(** The public context denotation uses each context's own erased environment.
    These wrappers require environment-locality facts to bridge from the
    ambient environment of the compound context to the standalone subcontext
    environments. *)
Lemma denot_ctx_comma_agree Γ1 Γ2 m :
  ty_env_agree_on (ctx_stale Γ1) (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ1) →
  ty_env_agree_on (ctx_stale Γ2) (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ2) →
  m ⊨ ⟦CtxComma Γ1 Γ2⟧ ↔ m ⊨ ⟦Γ1⟧ ∧ m ⊨ ⟦Γ2⟧.
Proof.
  intros Hagree1 Hagree2.
  change (m ⊨ denot_ctx_under (erase_ctx (CtxComma Γ1 Γ2)) (CtxComma Γ1 Γ2) ↔
    m ⊨ ⟦Γ1⟧ ∧ m ⊨ ⟦Γ2⟧).
  rewrite denot_ctx_under_comma.
  split.
  - intros [HΓ1 HΓ2]. split.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ1) Γ1 Hagree1) as [H _].
      apply H. exact HΓ1.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ2) Γ2 Hagree2) as [H _].
      apply H. exact HΓ2.
  - intros [HΓ1 HΓ2]. split.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ1) Γ1 Hagree1) as [_ H].
      apply H. exact HΓ1.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ2) Γ2 Hagree2) as [_ H].
      apply H. exact HΓ2.
Qed.

Lemma denot_ctx_star_agree Γ1 Γ2 m :
  ty_env_agree_on (ctx_stale Γ1) (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ1) →
  ty_env_agree_on (ctx_stale Γ2) (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ2) →
  m ⊨ ⟦CtxStar Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof.
  intros Hagree1 Hagree2.
  change (m ⊨ denot_ctx_under (erase_ctx (CtxStar Γ1 Γ2)) (CtxStar Γ1 Γ2) ↔
    ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
      res_product m1 m2 Hc ⊑ m ∧
      m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧).
  rewrite denot_ctx_under_star.
  split.
  - intros [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]].
    exists m1, m2, Hc. split; [exact Hprod |]. split.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ1) Γ1 Hagree1) as [H _].
      apply H. exact HΓ1.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ2) Γ2 Hagree2) as [H _].
      apply H. exact HΓ2.
  - intros [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]].
    exists m1, m2, Hc. split; [exact Hprod |]. split.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ1) Γ1 Hagree1) as [_ H].
      apply H. exact HΓ1.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ2) Γ2 Hagree2) as [_ H].
      apply H. exact HΓ2.
Qed.

Lemma denot_ctx_sum_agree Γ1 Γ2 m :
  ty_env_agree_on (ctx_stale Γ1) (erase_ctx (CtxSum Γ1 Γ2)) (erase_ctx Γ1) →
  ty_env_agree_on (ctx_stale Γ2) (erase_ctx (CtxSum Γ1 Γ2)) (erase_ctx Γ2) →
  m ⊨ ⟦CtxSum Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof.
  intros Hagree1 Hagree2.
  change (m ⊨ denot_ctx_under (erase_ctx (CtxSum Γ1 Γ2)) (CtxSum Γ1 Γ2) ↔
    ∃ (m1 m2 : WfWorld) (Hdef : raw_sum_defined m1 m2),
      res_sum m1 m2 Hdef ⊑ m ∧
      m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧).
  rewrite denot_ctx_under_sum.
  split.
  - intros [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]].
    exists m1, m2, Hdef. split; [exact Hsum |]. split.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxSum Γ1 Γ2)) (erase_ctx Γ1) Γ1 Hagree1) as [H _].
      apply H. exact HΓ1.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxSum Γ1 Γ2)) (erase_ctx Γ2) Γ2 Hagree2) as [H _].
      apply H. exact HΓ2.
  - intros [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]].
    exists m1, m2, Hdef. split; [exact Hsum |]. split.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxSum Γ1 Γ2)) (erase_ctx Γ1) Γ1 Hagree1) as [_ H].
      apply H. exact HΓ1.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxSum Γ1 Γ2)) (erase_ctx Γ2) Γ2 Hagree2) as [_ H].
      apply H. exact HΓ2.
Qed.

Lemma denot_ctx_comma Γ1 Γ2 m :
  m ⊨ ⟦CtxComma Γ1 Γ2⟧ ↔ m ⊨ ⟦Γ1⟧ ∧ m ⊨ ⟦Γ2⟧.
Proof. Admitted.

(** The context denotation of a star-context distributes over FStar. *)
Lemma denot_ctx_star Γ1 Γ2 m :
  m ⊨ ⟦CtxStar Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof. Admitted.

(** The context denotation of a sum-context distributes over FPlus. *)
Lemma denot_ctx_sum Γ1 Γ2 m :
  m ⊨ ⟦CtxSum Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof. Admitted.

(** [⟦CtxBind x τ⟧] is [⟦τ⟧ (return x)]. *)
Lemma denot_ctx_bind x τ m :
  m ⊨ ⟦CtxBind x τ⟧ ↔
  m ⊨ denot_ty_in_ctx (CtxBind x τ) τ (tret (vfvar x)).
Proof. reflexivity. Qed.

Lemma denot_ctx_restrict_stale Γ m :
  m ⊨ ⟦Γ⟧ →
  res_restrict m (ctx_stale Γ) ⊨ ⟦Γ⟧.
Proof.
  induction Γ in m |- *; simpl.
  - intros _. unfold res_models, res_models_with_store. simpl.
    split; [unfold formula_scoped_in_world; simpl; set_solver | exact I].
  - intros Hbind. apply denot_ty_under_restrict_fv. exact Hbind.
  - intros Hctx.
    apply denot_ctx_comma in Hctx as [HΓ1 HΓ2].
    apply denot_ctx_comma. split.
    + eapply res_models_kripke; [| exact (IHΓ1 m HΓ1)].
      apply res_restrict_mono. set_solver.
    + eapply res_models_kripke; [| exact (IHΓ2 m HΓ2)].
      apply res_restrict_mono. set_solver.
  - intros Hctx.
    apply denot_ctx_star in Hctx as [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]].
    apply denot_ctx_star.
    set (r1 := res_restrict m1 (ctx_stale Γ1)).
    set (r2 := res_restrict m2 (ctx_stale Γ2)).
    assert (Hc' : world_compat r1 r2).
    {
      subst r1 r2.
      eapply world_compat_le_l.
      - apply res_restrict_le.
      - eapply world_compat_le_r.
        + apply res_restrict_le.
        + exact Hc.
    }
    exists r1, r2, Hc'. split.
    + eapply res_le_restrict.
      * etrans.
        -- eapply (res_product_le_mono r1 r2 m1 m2 Hc' Hc);
             apply res_restrict_le.
        -- exact Hprod.
      * subst r1 r2. simpl. set_solver.
    + split; [apply IHΓ1 | apply IHΓ2]; assumption.
  - intros Hctx.
    apply denot_ctx_sum in Hctx as [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]].
    apply denot_ctx_sum.
    set (S := ctx_stale Γ1 ∪ ctx_stale Γ2).
    set (r1 := res_restrict m1 S).
    set (r2 := res_restrict m2 S).
    assert (Hdef' : raw_sum_defined r1 r2).
    {
      subst r1 r2 S. unfold raw_sum_defined. simpl.
      rewrite Hdef. reflexivity.
    }
    exists r1, r2, Hdef'. split.
    + eapply res_le_restrict.
      * etrans.
        -- eapply (res_sum_le_mono r1 r2 m1 m2 Hdef' Hdef);
             apply res_restrict_le.
        -- exact Hsum.
      * subst r1 r2 S. simpl. set_solver.
    + split.
      * eapply res_models_kripke; [| exact (IHΓ1 m1 HΓ1)].
        subst r1 S. apply res_restrict_mono. set_solver.
      * eapply res_models_kripke; [| exact (IHΓ2 m2 HΓ2)].
        subst r2 S. apply res_restrict_mono. set_solver.
Qed.
