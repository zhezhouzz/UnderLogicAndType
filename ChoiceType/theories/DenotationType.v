(** * ChoiceType.DenotationType

    Choice-type denotation and formula-locality lemmas. *)

From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  OperationalProps.
From ChoiceType Require Export DenotationExprProps.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Local Notation FQ := FormulaQ.

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

    [denot_ty_fuel gas X D Σ τ e] encodes the proposition "expression [e] has
    type [τ]" as a Choice Logic formula under erased basic environment [Σ].
    [X] is the common input domain used to interpret expression-result atoms.
    The finite set [D] is an avoidance set for generated binder
    representatives.  These names only make the syntax concrete:
    [FForall]'s cofinite semantics interprets each binder by renaming the
    representative to every sufficiently fresh atom. *)

Fixpoint denot_ty_fuel
    (gas : nat) (X D : aset) (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  match gas with
  | 0 => FFalse
  | S gas' =>
  match τ with

  (** {ν:b | φ}  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ◁φ
      [fib_vars (fv φ)] iterates the single-variable fiber modality over
      φ's free variables. *)
  | CTOver b φ =>
      fresh_forall (D ∪ X ∪ fv_tm e ∪ qual_dom φ) (fun ν =>
      let φν := qual_open_atom 0 ν φ in
	        (FImpl (FExprResult e ν)
	               (FAnd
	                 (basic_world_formula (<[ν := TBase b]> Σ) ({[ν]} ∪ qual_dom φν))
	                 (fib_vars (qual_dom φν)
	                   (FOver (FAtom (lift_type_qualifier_to_logic φν)))))))

  (** [ν:b | φ]  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ▷φ *)
  | CTUnder b φ =>
      fresh_forall (D ∪ X ∪ fv_tm e ∪ qual_dom φ) (fun ν =>
      let φν := qual_open_atom 0 ν φ in
	        (FImpl (FExprResult e ν)
	               (FAnd
	                 (basic_world_formula (<[ν := TBase b]> Σ) ({[ν]} ∪ qual_dom φν))
	                 (fib_vars (qual_dom φν)
	                   (FUnder (FAtom (lift_type_qualifier_to_logic φν)))))))

  (** τ1 ⊓ τ2  ≝  ⟦τ1⟧ e ∧ ⟦τ2⟧ e *)
  | CTInter τ1 τ2 =>
      FAnd (denot_ty_fuel gas' X D Σ τ1 e) (denot_ty_fuel gas' X D Σ τ2 e)

  (** τ1 ⊔ τ2  ≝  ⟦τ1⟧ e ∨ ⟦τ2⟧ e *)
  | CTUnion τ1 τ2 =>
      FOr (denot_ty_fuel gas' X D Σ τ1 e) (denot_ty_fuel gas' X D Σ τ2 e)

  (** τ1 ⊕ τ2  ≝  ⟦τ1⟧ e ⊕ ⟦τ2⟧ e *)
  | CTSum τ1 τ2 =>
      FPlus (denot_ty_fuel gas' X D Σ τ1 e) (denot_ty_fuel gas' X D Σ τ2 e)

  (** τ_x →, τ  ≝  ∀y. ⟦e⟧_y ⇒ ∀{y}.∀x.(⟦τ_x⟧ x ⇒ ⟦τ[x]⟧ (y x)). *)
  | CTArrow τx τ =>
      let Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ in
      fresh_forall Dy (fun y =>
      let Dx := {[y]} ∪ Dy in
        (FImpl
	          (FExprResult e y)
          (fresh_forall Dx (fun x =>
          let D2 := {[x]} ∪ Dx in
          let X2 := X ∪ {[y]} ∪ {[x]} in
            FFib y
              (FImpl
                (denot_ty_fuel gas' X2 D2 (<[x := erase_ty τx]> Σ) τx (tret (vfvar x)))
                (denot_ty_fuel gas' X2 D2 (<[x := erase_ty τx]> Σ) ({0 ~> x} τ)
                   (tapp (vfvar y) (vfvar x))))))))

  (** τ_x ⊸ τ  ≝  ∀y. ⟦e⟧_y ⇒ ∀{y}.∀x.(⟦τ_x⟧ x −∗ ⟦τ[x]⟧ (y x)). *)
  | CTWand τx τ =>
      let Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ in
      fresh_forall Dy (fun y =>
      let Dx := {[y]} ∪ Dy in
        (FImpl
	          (FExprResult e y)
          (fresh_forall Dx (fun x =>
          let D2 := {[x]} ∪ Dx in
          let X2 := X ∪ {[y]} ∪ {[x]} in
            FFib y
              (FWand
                (denot_ty_fuel gas' X2 D2 (<[x := erase_ty τx]> Σ) τx (tret (vfvar x)))
                (denot_ty_fuel gas' X2 D2 (<[x := erase_ty τx]> Σ) ({0 ~> x} τ)
                   (tapp (vfvar y) (vfvar x))))))))

  end
  end.

Definition denot_ty_avoiding
    (X D : aset) (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_fuel (cty_measure τ) X D Σ τ e.

Definition denot_ty_on
    (X : aset) (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_avoiding X (dom Σ ∪ fv_cty τ ∪ fv_tm e ∪ X) Σ τ e.

Definition denot_ty_under (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_on (fv_tm e) Σ τ e.

Definition denot_ty (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under ∅ τ e.

Definition denot_ty_in_ctx (Γ : ctx) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under (erase_ctx Γ) τ e.

Definition erase_ctx_under (Σ : gmap atom ty) (Γ : ctx) : gmap atom ty :=
  Σ ∪ erase_ctx Γ.

Definition denot_ty_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_on (dom (erase_ctx_under Σ Γ)) (erase_ctx_under Σ Γ) τ e.

Definition denot_ty_total_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm)
    (m : WfWorld) : Prop :=
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ∧
  expr_total_on (dom (erase_ctx_under Σ Γ)) e m.

Definition entails_total (φ : FQ) (P : WfWorld → Prop) : Prop :=
  ∀ m, m ⊨ φ → P m.

Lemma denot_ty_total_formula Σ Γ τ e m :
  denot_ty_total_in_ctx_under Σ Γ τ e m →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e.
Proof. intros [H _]. exact H. Qed.

Lemma denot_ty_total_expr_total Σ Γ τ e m :
  denot_ty_total_in_ctx_under Σ Γ τ e m →
  expr_total_on (dom (erase_ctx_under Σ Γ)) e m.
Proof. intros [_ H]. exact H. Qed.

Definition ty_env_agree_on (X : aset) (Σ1 Σ2 : gmap atom ty) : Prop :=
  ∀ x, x ∈ X → Σ1 !! x = Σ2 !! x.

Lemma ty_env_agree_on_mono X Y Σ1 Σ2 :
  X ⊆ Y →
  ty_env_agree_on Y Σ1 Σ2 →
  ty_env_agree_on X Σ1 Σ2.
Proof. unfold ty_env_agree_on. hauto. Qed.

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

Definition formula_store_equiv (φ ψ : FQ) : Prop :=
  ∀ ρ m, res_models_with_store ρ m φ ↔ res_models_with_store ρ m ψ.

Lemma formula_equiv_refl φ : φ ⊣⊢ φ.
Proof. unfold formula_equiv, entails. hauto. Qed.

Lemma formula_equiv_sym φ ψ :
  φ ⊣⊢ ψ → ψ ⊣⊢ φ.
Proof. unfold formula_equiv. hauto. Qed.

Lemma formula_equiv_trans φ ψ χ :
  φ ⊣⊢ ψ → ψ ⊣⊢ χ → φ ⊣⊢ χ.
Proof. unfold formula_equiv, entails. hauto. Qed.

Lemma formula_store_equiv_refl φ : formula_store_equiv φ φ.
Proof. unfold formula_store_equiv. hauto. Qed.

Lemma formula_store_equiv_sym φ ψ :
  formula_store_equiv φ ψ → formula_store_equiv ψ φ.
Proof. unfold formula_store_equiv. hauto. Qed.

Lemma formula_store_equiv_trans φ ψ χ :
  formula_store_equiv φ ψ →
  formula_store_equiv ψ χ →
  formula_store_equiv φ χ.
Proof. unfold formula_store_equiv. hauto. Qed.

Lemma formula_store_equiv_and φ1 φ2 ψ1 ψ2 :
  formula_fv φ1 = formula_fv ψ1 →
  formula_fv φ2 = formula_fv ψ2 →
  formula_store_equiv φ1 ψ1 →
  formula_store_equiv φ2 ψ2 →
  formula_store_equiv (FAnd φ1 φ2) (FAnd ψ1 ψ2).
Proof.
  intros Hfv1 Hfv2 H1 H2 ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite <- Hfv1, <- Hfv2. exact Hscope.
  - destruct Hmodel as [Hφ1 Hφ2]. split.
    + pose proof (proj1 (H1 ρ m)) as H.
      assert (Hφ1_exact : res_models_with_store ρ m φ1).
      { models_fuel_irrel Hφ1. }
      models_fuel_irrel (H Hφ1_exact).
    + pose proof (proj1 (H2 ρ m)) as H.
      assert (Hφ2_exact : res_models_with_store ρ m φ2).
      { models_fuel_irrel Hφ2. }
      models_fuel_irrel (H Hφ2_exact).
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite Hfv1, Hfv2. exact Hscope.
  - destruct Hmodel as [Hψ1 Hψ2]. split.
    + pose proof (proj2 (H1 ρ m)) as H.
      assert (Hψ1_exact : res_models_with_store ρ m ψ1).
      { models_fuel_irrel Hψ1. }
      models_fuel_irrel (H Hψ1_exact).
    + pose proof (proj2 (H2 ρ m)) as H.
      assert (Hψ2_exact : res_models_with_store ρ m ψ2).
      { models_fuel_irrel Hψ2. }
      models_fuel_irrel (H Hψ2_exact).
Qed.

Lemma formula_store_equiv_over φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_store_equiv (FOver φ) (FOver ψ).
Proof.
  intros Hfv Heq ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope [m0 [Hsub Hφ]]]; split.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite <- Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj1 (Heq ρ m0)) as H.
    assert (Hφ_exact : res_models_with_store ρ m0 φ).
    { models_fuel_irrel Hφ. }
    models_fuel_irrel (H Hφ_exact).
  - unfold formula_scoped_in_world in *. simpl in *. rewrite Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj2 (Heq ρ m0)) as H.
    assert (Hψ_exact : res_models_with_store ρ m0 ψ).
    { models_fuel_irrel Hφ. }
    models_fuel_irrel (H Hψ_exact).
Qed.

Lemma formula_store_equiv_under φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_store_equiv (FUnder φ) (FUnder ψ).
Proof.
  intros Hfv Heq ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope [m0 [Hsub Hφ]]]; split.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite <- Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj1 (Heq ρ m0)) as H.
    assert (Hφ_exact : res_models_with_store ρ m0 φ).
    { models_fuel_irrel Hφ. }
    models_fuel_irrel (H Hφ_exact).
  - unfold formula_scoped_in_world in *. simpl in *. rewrite Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj2 (Heq ρ m0)) as H.
    assert (Hψ_exact : res_models_with_store ρ m0 ψ).
    { models_fuel_irrel Hφ. }
    models_fuel_irrel (H Hψ_exact).
Qed.

Lemma formula_store_equiv_fib x φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_store_equiv (FFib x φ) (FFib x ψ).
Proof.
  intros Hfv Heq ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope [Hdisj Hfib]]; split.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite <- Hfv. exact Hscope.
  - split; [exact Hdisj |].
    intros σ Hproj.
    pose proof (Hfib σ Hproj) as Hφ.
    pose proof (proj1 (Heq (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj))) as H.
    assert (Hφ_exact : res_models_with_store (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj) φ).
    { models_fuel_irrel Hφ. }
    models_fuel_irrel (H Hφ_exact).
  - unfold formula_scoped_in_world in *. simpl in *. rewrite Hfv. exact Hscope.
  - split; [exact Hdisj |].
    intros σ Hproj.
    pose proof (Hfib σ Hproj) as Hψ.
    pose proof (proj2 (Heq (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj))) as H.
    assert (Hψ_exact : res_models_with_store (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj) ψ).
    { models_fuel_irrel Hψ. }
    models_fuel_irrel (H Hψ_exact).
Qed.

Lemma foldr_fib_store_equiv xs φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_fv (foldr FFib φ xs) = formula_fv (foldr FFib ψ xs) ∧
  formula_store_equiv (foldr FFib φ xs) (foldr FFib ψ xs).
Proof.
  induction xs as [|x xs IH]; simpl; intros Hfv Heq.
  - split; [exact Hfv | exact Heq].
  - destruct (IH Hfv Heq) as [Hfv' Heq'].
    split.
    + simpl. rewrite Hfv'. reflexivity.
    + apply formula_store_equiv_fib; assumption.
Qed.

Lemma fib_vars_store_equiv X φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_fv (fib_vars X φ) = formula_fv (fib_vars X ψ) ∧
  formula_store_equiv (fib_vars X φ) (fib_vars X ψ).
Proof.
  intros Hfv Heq.
  unfold fib_vars, fib_vars_acc, set_fold.
  simpl.
  rewrite !foldr_fib_vars_acc_fst.
  apply foldr_fib_store_equiv; assumption.
Qed.

Lemma denot_ty_fuel_env_agree gas X D Σ1 Σ2 τ e :
  ty_env_agree_on (fv_cty τ) Σ1 Σ2 →
  denot_ty_fuel gas X D Σ1 τ e = denot_ty_fuel gas X D Σ2 τ e.
Proof.
  revert X D Σ1 Σ2 τ e.
  induction gas as [|gas IH]; intros X D Σ1 Σ2 τ e Hagree; [reflexivity |].
  destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ]; simpl in *.
  - unfold fresh_forall.
    set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
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
    set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
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
  - rewrite (IH X D Σ1 Σ2 τ1 e).
    + rewrite (IH X D Σ1 Σ2 τ2 e); [reflexivity |].
      intros z Hz. apply Hagree. set_solver.
    + intros z Hz. apply Hagree. set_solver.
  - rewrite (IH X D Σ1 Σ2 τ1 e).
    + rewrite (IH X D Σ1 Σ2 τ2 e); [reflexivity |].
      intros z Hz. apply Hagree. set_solver.
    + intros z Hz. apply Hagree. set_solver.
  - rewrite (IH X D Σ1 Σ2 τ1 e).
    + rewrite (IH X D Σ1 Σ2 τ2 e); [reflexivity |].
      intros z Hz. apply Hagree. set_solver.
    + intros z Hz. apply Hagree. set_solver.
  - unfold fresh_forall.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    set (Dx := {[y]} ∪ Dy).
    set (x := fresh_for Dx).
    set (D2 := {[x]} ∪ Dx).
    set (X2 := X ∪ {[y]} ∪ {[x]}).
    assert (Harg :
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ1) τx (tret (vfvar x)) =
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ2) τx (tret (vfvar x))).
    {
      apply IH.
      intros z Hz.
      destruct (decide (z = x)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree. simpl in Hz. set_solver.
    }
    assert (Hres :
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ1) ({0 ~> x} τ)
        (tapp (vfvar y) (vfvar x)) =
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ2) ({0 ~> x} τ)
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
    set (X2 := X ∪ {[y]} ∪ {[x]}).
    assert (Harg :
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ1) τx (tret (vfvar x)) =
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ2) τx (tret (vfvar x))).
    {
      apply IH.
      intros z Hz.
      destruct (decide (z = x)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree. simpl in Hz. set_solver.
    }
    assert (Hres :
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ1) ({0 ~> x} τ)
        (tapp (vfvar y) (vfvar x)) =
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ2) ({0 ~> x} τ)
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
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (fv_cty τ) Σ1 Σ2 →
  denot_ty_under Σ1 τ e = denot_ty_under Σ2 τ e.
Proof.
  intros Hdom Hagree.
  unfold denot_ty_under, denot_ty_on, denot_ty_avoiding.
  rewrite Hdom.
  apply denot_ty_fuel_env_agree. exact Hagree.
Qed.

Lemma denot_ty_under_env_equiv Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (fv_cty τ) Σ1 Σ2 →
  denot_ty_under Σ1 τ e ⊣⊢ denot_ty_under Σ2 τ e.
Proof.
  intros Hdom Hagree.
  rewrite (denot_ty_under_env_agree Σ1 Σ2 τ e Hdom Hagree).
  apply formula_equiv_refl.
Qed.

Lemma denot_ty_in_ctx_env_agree Γ1 Γ2 τ e :
  dom (erase_ctx Γ1) = dom (erase_ctx Γ2) →
  ty_env_agree_on (fv_cty τ) (erase_ctx Γ1) (erase_ctx Γ2) →
  denot_ty_in_ctx Γ1 τ e = denot_ty_in_ctx Γ2 τ e.
Proof.
  intros Hdom Hagree. unfold denot_ty_in_ctx.
  apply denot_ty_under_env_agree.
  - exact Hdom.
  - exact Hagree.
Qed.

Lemma denot_ty_in_ctx_env_equiv Γ1 Γ2 τ e :
  dom (erase_ctx Γ1) = dom (erase_ctx Γ2) →
  ty_env_agree_on (fv_cty τ) (erase_ctx Γ1) (erase_ctx Γ2) →
  denot_ty_in_ctx Γ1 τ e ⊣⊢ denot_ty_in_ctx Γ2 τ e.
Proof.
  intros Hdom Hagree. unfold denot_ty_in_ctx.
  apply denot_ty_under_env_equiv.
  - exact Hdom.
  - exact Hagree.
Qed.

(** ** Denotation scoping regularity

    These syntactic facts isolate the variable-accounting needed by semantic
    subtyping reflexivity.  They are intentionally stated at the denotation
    layer: typing proofs should consume these regularity lemmas rather than
    unfolding the formula generated for each type constructor. *)

Lemma denot_ty_fuel_formula_fv_subset gas X D Σ τ e :
  cty_measure τ <= gas →
  formula_fv (denot_ty_fuel gas X D Σ τ e) ⊆
    D ∪ X ∪ fv_tm e ∪ fv_cty τ.
Proof.
  revert X D Σ τ e.
  induction gas as [|gas IH]; intros X D Σ τ e Hgas.
  - destruct τ; simpl in Hgas; lia.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ]; simpl in *.
    + unfold fresh_forall.
      set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
      set (φν := qual_open_atom 0 ν φ).
      assert (Hφν : qual_dom φν ⊆ qual_dom φ ∪ {[ν]})
        by (subst φν; apply qual_open_atom_dom_subset).
      rewrite fib_vars_formula_fv. simpl.
      unfold stale, stale_logic_qualifier. simpl.
      change (stale e) with (fv_tm e).
      rewrite lqual_dom_lift_type_qualifier_to_logic.
	      pose proof (FExprResult_fv_exact_domain e ν) as Hres_fv.
	      intros z Hz.
	      apply elem_of_difference in Hz as [Hz Hzν].
	      set_solver.
    + unfold fresh_forall.
      set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
      set (φν := qual_open_atom 0 ν φ).
      assert (Hφν : qual_dom φν ⊆ qual_dom φ ∪ {[ν]})
        by (subst φν; apply qual_open_atom_dom_subset).
      rewrite fib_vars_formula_fv. simpl.
      unfold stale, stale_logic_qualifier. simpl.
      change (stale e) with (fv_tm e).
      rewrite lqual_dom_lift_type_qualifier_to_logic.
	      pose proof (FExprResult_fv_exact_domain e ν) as Hres_fv.
	      intros z Hz.
	      apply elem_of_difference in Hz as [Hz Hzν].
	      set_solver.
    + pose proof (IH X D Σ τ1 e ltac:(lia)) as H1.
      pose proof (IH X D Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    + pose proof (IH X D Σ τ1 e ltac:(lia)) as H1.
      pose proof (IH X D Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    + pose proof (IH X D Σ τ1 e ltac:(lia)) as H1.
      pose proof (IH X D Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    + unfold fresh_forall.
      set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
      set (y := fresh_for Dy).
      set (Dx := {[y]} ∪ Dy).
      set (x := fresh_for Dx).
      set (D2 := {[x]} ∪ Dx).
      set (X2 := X ∪ {[y]} ∪ {[x]}).
      pose proof (IH X2 D2 (<[x := erase_ty τx]> Σ)
        τx (tret (vfvar x)) ltac:(lia)) as Harg.
      pose proof (IH X2 D2 (<[x := erase_ty τx]> Σ)
        ({0 ~> x} τ) (tapp (vfvar y) (vfvar x))
        ltac:(rewrite cty_open_preserves_measure; lia)) as Hres.
      pose proof (cty_open_fv_subset 0 x τ) as Hopen.
      intros z Hz.
      apply elem_of_difference in Hz as [Hz Hzy].
      apply elem_of_union in Hz as [Hzres_e | Hzrest].
	      * pose proof (FExprResult_fv_exact_domain e y) as Hres_fv.
	        apply Hres_fv in Hzres_e. set_solver.
      * apply elem_of_difference in Hzrest as [Hzrest Hzx].
        apply elem_of_union in Hzrest as [Hzy0 | Hzrest].
        { set_solver. }
        apply elem_of_union in Hzrest as [Hzarg | Hzbody].
        -- apply Harg in Hzarg. simpl in Hzarg. set_solver.
        -- apply Hres in Hzbody. simpl in Hzbody. set_solver.
    + unfold fresh_forall.
      set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
      set (y := fresh_for Dy).
      set (Dx := {[y]} ∪ Dy).
      set (x := fresh_for Dx).
      set (D2 := {[x]} ∪ Dx).
      set (X2 := X ∪ {[y]} ∪ {[x]}).
      pose proof (IH X2 D2 (<[x := erase_ty τx]> Σ)
        τx (tret (vfvar x)) ltac:(lia)) as Harg.
      pose proof (IH X2 D2 (<[x := erase_ty τx]> Σ)
        ({0 ~> x} τ) (tapp (vfvar y) (vfvar x))
        ltac:(rewrite cty_open_preserves_measure; lia)) as Hres.
      pose proof (cty_open_fv_subset 0 x τ) as Hopen.
      intros z Hz.
      apply elem_of_difference in Hz as [Hz Hzy].
      apply elem_of_union in Hz as [Hzres_e | Hzrest].
	      * pose proof (FExprResult_fv_exact_domain e y) as Hres_fv.
	        apply Hres_fv in Hzres_e. set_solver.
      * apply elem_of_difference in Hzrest as [Hzrest Hzx].
        apply elem_of_union in Hzrest as [Hzy0 | Hzrest].
        { set_solver. }
        apply elem_of_union in Hzrest as [Hzarg | Hzbody].
        -- apply Harg in Hzarg. simpl in Hzarg. set_solver.
        -- apply Hres in Hzbody. simpl in Hzbody. set_solver.
Qed.

Lemma denot_ty_formula_fv_subset τ e :
  formula_fv (denot_ty τ e) ⊆ fv_tm e ∪ fv_cty τ.
Proof.
  unfold denot_ty, denot_ty_under, denot_ty_on, denot_ty_avoiding.
  pose proof (denot_ty_fuel_formula_fv_subset
    (cty_measure τ) (fv_tm e) (dom (∅ : gmap atom ty) ∪ fv_cty τ ∪ fv_tm e ∪ fv_tm e) ∅ τ e ltac:(lia)) as Hfv.
  replace (fv_cty τ ∪ fv_tm e ∪ ∅) with (fv_cty τ ∪ fv_tm e) by set_solver.
  intros z Hz. apply Hfv in Hz. set_solver.
Qed.

Lemma denot_ty_fuel_formula_fv_env_agree gas X D Σ1 Σ2 τ e :
  formula_fv (denot_ty_fuel gas X D Σ1 τ e) =
  formula_fv (denot_ty_fuel gas X D Σ2 τ e).
Proof.
  revert X D Σ1 Σ2 τ e.
  induction gas as [|gas IH]; intros X D Σ1 Σ2 τ e; [reflexivity |].
  destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ]; simpl in *.
  - unfold fresh_forall.
    set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
    set (φν := qual_open_atom 0 ν φ).
    reflexivity.
  - unfold fresh_forall.
    set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
    set (φν := qual_open_atom 0 ν φ).
    reflexivity.
  - rewrite (IH X D Σ1 Σ2 τ1 e), (IH X D Σ1 Σ2 τ2 e). reflexivity.
  - rewrite (IH X D Σ1 Σ2 τ1 e), (IH X D Σ1 Σ2 τ2 e). reflexivity.
  - rewrite (IH X D Σ1 Σ2 τ1 e), (IH X D Σ1 Σ2 τ2 e). reflexivity.
  - unfold fresh_forall.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    set (Dx := {[y]} ∪ Dy).
    set (x := fresh_for Dx).
    set (D2 := {[x]} ∪ Dx).
    set (X2 := X ∪ {[y]} ∪ {[x]}).
    rewrite (IH X2 D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      τx (tret (vfvar x))).
    rewrite (IH X2 D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      ({0 ~> x} τ) (tapp (vfvar y) (vfvar x))).
    reflexivity.
  - unfold fresh_forall.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    set (Dx := {[y]} ∪ Dy).
    set (x := fresh_for Dx).
    set (D2 := {[x]} ∪ Dx).
    set (X2 := X ∪ {[y]} ∪ {[x]}).
    rewrite (IH X2 D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      τx (tret (vfvar x))).
    rewrite (IH X2 D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      ({0 ~> x} τ) (tapp (vfvar y) (vfvar x))).
    reflexivity.
Qed.

Lemma denot_ty_under_formula_fv_subset Σ τ e :
  formula_fv (denot_ty_under Σ τ e) ⊆ dom Σ ∪ fv_tm e ∪ fv_cty τ.
Proof.
  unfold denot_ty_under, denot_ty_on, denot_ty_avoiding.
  pose proof (denot_ty_fuel_formula_fv_subset
    (cty_measure τ) (fv_tm e)
    (dom Σ ∪ fv_cty τ ∪ fv_tm e ∪ fv_tm e) Σ τ e ltac:(lia)) as Hfv.
  intros z Hz. apply Hfv in Hz. set_solver.
Qed.

Lemma denot_ty_on_formula_fv_subset X Σ τ e :
  formula_fv (denot_ty_on X Σ τ e) ⊆ dom Σ ∪ X ∪ fv_tm e ∪ fv_cty τ.
Proof.
  unfold denot_ty_on, denot_ty_avoiding.
  pose proof (denot_ty_fuel_formula_fv_subset
    (cty_measure τ) X (dom Σ ∪ fv_cty τ ∪ fv_tm e ∪ X)
    Σ τ e ltac:(lia)) as Hfv.
  intros z Hz. apply Hfv in Hz. set_solver.
Qed.

Lemma denot_ty_in_ctx_under_formula_fv_subset Σ Γ τ e :
  formula_fv (denot_ty_in_ctx_under Σ Γ τ e) ⊆
    dom (erase_ctx_under Σ Γ) ∪ fv_tm e ∪ fv_cty τ.
Proof.
  unfold denot_ty_in_ctx_under, denot_ty_on, denot_ty_avoiding.
  pose proof (denot_ty_fuel_formula_fv_subset
    (cty_measure τ) (dom (erase_ctx_under Σ Γ))
    (dom (erase_ctx_under Σ Γ) ∪ fv_cty τ ∪ fv_tm e ∪ dom (erase_ctx_under Σ Γ))
    (erase_ctx_under Σ Γ) τ e ltac:(lia)) as Hfv.
  intros z Hz. apply Hfv in Hz. set_solver.
Qed.

Lemma denot_ty_fuel_expr_fv_subset gas X D Σ τ e :
  cty_measure τ <= gas →
  fv_tm e ⊆ X →
  fv_tm e ⊆ formula_fv (denot_ty_fuel gas X D Σ τ e).
Proof.
  revert X D Σ τ e.
  induction gas as [|gas IH]; intros X D Σ τ e Hgas Hfv.
  - destruct τ; simpl in Hgas; lia.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ]; simpl in *.
    + unfold fresh_forall.
      set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
      assert (Hνe : ν ∉ fv_tm e)
        by (subst ν; pose proof (fresh_for_not_in (D ∪ X ∪ fv_tm e ∪ qual_dom φ)); set_solver).
	      pose proof (FExprResult_expr_fv_subset X e ν Hfv) as Hres_fv.
	      intros z Hz. apply elem_of_difference. split; [set_solver |].
	      intros Hzν. apply elem_of_singleton in Hzν. subst z. exact (Hνe Hz).
    + unfold fresh_forall.
      set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
      assert (Hνe : ν ∉ fv_tm e)
        by (subst ν; pose proof (fresh_for_not_in (D ∪ X ∪ fv_tm e ∪ qual_dom φ)); set_solver).
	      pose proof (FExprResult_expr_fv_subset X e ν Hfv) as Hres_fv.
	      intros z Hz. apply elem_of_difference. split; [set_solver |].
	      intros Hzν. apply elem_of_singleton in Hzν. subst z. exact (Hνe Hz).
    + pose proof (IH X D Σ τ1 e ltac:(lia) Hfv) as H1.
      set_solver.
    + pose proof (IH X D Σ τ1 e ltac:(lia) Hfv) as H1.
      set_solver.
    + pose proof (IH X D Σ τ1 e ltac:(lia) Hfv) as H1.
      set_solver.
    + unfold fresh_forall.
      set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
      set (y := fresh_for Dy).
      assert (Hye : y ∉ fv_tm e)
        by (subst y Dy; pose proof (fresh_for_not_in (D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ)); set_solver).
	      pose proof (FExprResult_expr_fv_subset X e y Hfv) as Hres_fv.
	      intros z Hz. apply elem_of_difference. split; [set_solver |].
	      intros Hzy. apply elem_of_singleton in Hzy. subst z. exact (Hye Hz).
    + unfold fresh_forall.
      set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
      set (y := fresh_for Dy).
      assert (Hye : y ∉ fv_tm e)
        by (subst y Dy; pose proof (fresh_for_not_in (D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ)); set_solver).
	      pose proof (FExprResult_expr_fv_subset X e y Hfv) as Hres_fv.
	      intros z Hz. apply elem_of_difference. split; [set_solver |].
	      intros Hzy. apply elem_of_singleton in Hzy. subst z. exact (Hye Hz).
Qed.

Lemma denot_ty_under_result_atom_fv Σ x τ :
  x ∈ formula_fv (denot_ty_under Σ τ (tret (vfvar x))).
Proof.
  unfold denot_ty_under, denot_ty_on, denot_ty_avoiding.
  pose proof (denot_ty_fuel_expr_fv_subset
    (cty_measure τ) (fv_tm (tret (vfvar x)))
    (dom Σ ∪ fv_cty τ ∪ fv_tm (tret (vfvar x)) ∪ fv_tm (tret (vfvar x))) Σ τ
    (tret (vfvar x)) ltac:(lia) ltac:(set_solver)) as Hfv.
  apply Hfv. simpl. set_solver.
Qed.

Lemma denot_ty_on_result_atom_fv X Σ x τ :
  x ∈ X →
  x ∈ formula_fv (denot_ty_on X Σ τ (tret (vfvar x))).
Proof.
  intros Hx.
  unfold denot_ty_on, denot_ty_avoiding.
  pose proof (denot_ty_fuel_expr_fv_subset
    (cty_measure τ) X
    (dom Σ ∪ fv_cty τ ∪ fv_tm (tret (vfvar x)) ∪ X) Σ τ
    (tret (vfvar x)) ltac:(lia) ltac:(simpl; set_solver)) as Hfv.
  apply Hfv. simpl. set_solver.
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
  res_restrict m (dom Σ ∪ fv_tm e ∪ fv_cty τ) ⊨ denot_ty_under Σ τ e.
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
