(** * ChoiceType.DenotationType

    Choice-type denotation and formula-locality lemmas. *)

From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  OperationalProps StrongNormalization Sugar.
From ChoiceType Require Export DenotationFormulaEquiv.
From ChoiceType Require Import BasicStore BasicTyping LocallyNamelessProps.

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

    [denot_ty_fuel gas Σ τ e] is the recursive semantic content of
    "expression [e] has type [τ]" under erased basic environment [Σ],
    including the uniform obligations every denotation needs: basic typing,
    closed resources, and strong totality.

    Keeping the obligations in the recursive formula itself avoids the previous
    [denot_ty_result] wrapper style: recursive calls are ordinary full
    formulas, and helper lemmas can reason with Choice Logic connectives
    directly.  [denot_ty_fuel_body] is only a one-step view used by proofs to
    peel the outer obligation layer; it is not recursive by itself.
    Expression-result atoms and fresh representatives are driven by [dom Σ].
    The regularity assumptions that [fv_tm e] and [fv_cty τ] are contained in
    [dom Σ] are supplied by the basic typing conjunct. *)

Definition expr_total_with_store (X : aset) (e : tm)
    (ρ : Store) (m : WfWorld) : Prop :=
  (∀ σ, (m : World) σ → store_closed (store_restrict (ρ ∪ σ) X)) ∧
  ∃ n, ∀ σ, (m : World) σ →
    strongly_normalizing_fuel n (subst_map (store_restrict (ρ ∪ σ) X) e).

Definition FBasicTypingIn (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  FPure (basic_choice_ty (dom Σ) τ ∧ Σ ⊢ₑ e ⋮ erase_ty τ).

Definition FClosedResourceIn (Σ : gmap atom ty) : FQ :=
  FResourceAtom (dom Σ) (world_closed_on (dom Σ)).

Definition FStrongTotalIn (Σ : gmap atom ty) (e : tm) : FQ :=
  FStoreResourceAtom (dom Σ)
    (fun ρ m => expr_total_with_store (dom Σ) e ρ m).

Lemma expr_total_with_store_empty_restrict X e m :
  world_closed_on X m →
  expr_total_on X e m →
  expr_total_with_store X e ∅ (res_restrict m X).
Proof.
  intros Hclosed [_ [n Htotal]].
  split.
  - intros σ Hσ.
    destruct (res_restrict_lift_store m X σ Hσ) as [σm [Hσm Hrestrict]].
    assert (Heq : store_restrict ((∅ : Store) ∪ σ) X = store_restrict σm X).
    { rewrite map_empty_union.
      rewrite <- Hrestrict.
      rewrite store_restrict_restrict.
      replace (X ∩ X) with X by set_solver.
      reflexivity. }
    rewrite Heq. apply Hclosed. exact Hσm.
  - exists n. intros σ Hσ.
    destruct (res_restrict_lift_store m X σ Hσ) as [σm [Hσm Hrestrict]].
    assert (Heq : store_restrict ((∅ : Store) ∪ σ) X = store_restrict σm X).
    { rewrite map_empty_union.
      rewrite <- Hrestrict.
      rewrite store_restrict_restrict.
      replace (X ∩ X) with X by set_solver.
      reflexivity. }
    rewrite Heq. apply Htotal. exact Hσm.
Unshelve.
  all: try typeclasses eauto; try set_solver.
Qed.

Definition denot_ty_obligations
    (Σ : gmap atom ty) (τ : choice_ty) (e : tm) (φ : FQ) : FQ :=
  FAnd (FBasicTypingIn Σ τ e)
    (FAnd (FClosedResourceIn Σ)
      (FAnd (FStrongTotalIn Σ e) φ)).

Fixpoint denot_ty_fuel
    (gas : nat) (Σ : gmap atom ty) (τ : choice_ty) (e : tm)
    : FQ :=
  denot_ty_obligations Σ τ e (
    match gas with
    | 0 => FFalse
    | S gas' =>
    match τ with

  (** {ν:b | φ}  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ◁φ
      [fib_vars (fv φ)] iterates the single-variable fiber modality over
      φ's free variables. *)
  | CTOver b φ =>
      FExprContIn Σ e (fun ν =>
      let φν := qual_open_atom 0 ν φ in
        FAnd
          (basic_world_formula (<[ν := TBase b]> Σ) ({[ν]} ∪ qual_dom φν))
          (fib_vars (qual_dom φν)
            (FOver (FTypeQualifier φν))))

  (** [ν:b | φ]  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ▷φ *)
  | CTUnder b φ =>
      FExprContIn Σ e (fun ν =>
      let φν := qual_open_atom 0 ν φ in
        FAnd
          (basic_world_formula (<[ν := TBase b]> Σ) ({[ν]} ∪ qual_dom φν))
          (fib_vars (qual_dom φν)
            (FUnder (FTypeQualifier φν))))

  (** τ1 ⊓ τ2  ≝  ⟦τ1⟧ e ∧ ⟦τ2⟧ e *)
  | CTInter τ1 τ2 =>
      FAnd
        (denot_ty_fuel gas' Σ τ1 e)
        (denot_ty_fuel gas' Σ τ2 e)

  (** τ1 ⊔ τ2  ≝  ⟦τ1⟧ e ∨ ⟦τ2⟧ e *)
  | CTUnion τ1 τ2 =>
      FOr
        (denot_ty_fuel gas' Σ τ1 e)
        (denot_ty_fuel gas' Σ τ2 e)

  (** τ1 ⊕ τ2  ≝  ⟦τ1⟧ e ⊕ ⟦τ2⟧ e *)
  | CTSum τ1 τ2 =>
      FPlus
        (denot_ty_fuel gas' Σ τ1 e)
        (denot_ty_fuel gas' Σ τ2 e)

  (** τ_x →, τ  ≝  ∀x.(⟦τ_x⟧ x ⇒ ⟦τ[x]⟧ (e x)).

      The application [e x] is represented by the derived core term
      [tapp_tm e (vfvar x)], which first evaluates [e] to a function value and
      then applies it to [x].  We intentionally do not allocate a separate
      logic coordinate for the function result here. *)
  | CTArrow τx τ =>
      fresh_forall (dom Σ) (fun x =>
        let Σx := <[x := erase_ty τx]> Σ in
          FImpl
            (denot_ty_fuel gas' Σx τx (tret (vfvar x)))
            (denot_ty_fuel gas' Σx ({0 ~> x} τ)
              (tapp_tm e (vfvar x))))

  (** τ_x ⊸ τ  ≝  ∀x.(⟦τ_x⟧ x −∗ ⟦τ[x]⟧ (e x)). *)
  | CTWand τx τ =>
      fresh_forall (dom Σ) (fun x =>
        let Σx := <[x := erase_ty τx]> Σ in
          FWand
            (denot_ty_fuel gas' Σx τx (tret (vfvar x)))
            (denot_ty_fuel gas' Σx ({0 ~> x} τ)
              (tapp_tm e (vfvar x))))

    end
    end).

Definition denot_ty_fuel_body
    (gas : nat) (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  match gas with
  | 0 => FFalse
  | S gas' =>
  match τ with
  | CTOver b φ =>
      FExprContIn Σ e (fun ν =>
      let φν := qual_open_atom 0 ν φ in
        FAnd
          (basic_world_formula (<[ν := TBase b]> Σ) ({[ν]} ∪ qual_dom φν))
          (fib_vars (qual_dom φν)
            (FOver (FTypeQualifier φν))))
  | CTUnder b φ =>
      FExprContIn Σ e (fun ν =>
      let φν := qual_open_atom 0 ν φ in
        FAnd
          (basic_world_formula (<[ν := TBase b]> Σ) ({[ν]} ∪ qual_dom φν))
          (fib_vars (qual_dom φν)
            (FUnder (FTypeQualifier φν))))
  | CTInter τ1 τ2 =>
      FAnd
        (denot_ty_fuel gas' Σ τ1 e)
        (denot_ty_fuel gas' Σ τ2 e)
  | CTUnion τ1 τ2 =>
      FOr
        (denot_ty_fuel gas' Σ τ1 e)
        (denot_ty_fuel gas' Σ τ2 e)
  | CTSum τ1 τ2 =>
      FPlus
        (denot_ty_fuel gas' Σ τ1 e)
        (denot_ty_fuel gas' Σ τ2 e)
  | CTArrow τx τ =>
      fresh_forall (dom Σ) (fun x =>
        let Σx := <[x := erase_ty τx]> Σ in
          FImpl
            (denot_ty_fuel gas' Σx τx (tret (vfvar x)))
            (denot_ty_fuel gas' Σx ({0 ~> x} τ)
              (tapp_tm e (vfvar x))))
  | CTWand τx τ =>
      fresh_forall (dom Σ) (fun x =>
        let Σx := <[x := erase_ty τx]> Σ in
          FWand
            (denot_ty_fuel gas' Σx τx (tret (vfvar x)))
            (denot_ty_fuel gas' Σx ({0 ~> x} τ)
              (tapp_tm e (vfvar x))))
  end
  end.

Lemma denot_ty_fuel_unfold gas Σ τ e :
  denot_ty_fuel gas Σ τ e =
  denot_ty_obligations Σ τ e (denot_ty_fuel_body gas Σ τ e).
Proof.
  destruct gas as [|gas]; [reflexivity |].
  destruct τ; reflexivity.
Qed.

Definition denot_ty_on
    (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_fuel (cty_measure τ) Σ τ e.

Definition denot_ty_under (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_on Σ τ e.

Definition denot_ty (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under ∅ τ e.

Definition denot_ty_in_ctx (Γ : ctx) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under (erase_ctx Γ) τ e.

Definition erase_ctx_under (Σ : gmap atom ty) (Γ : ctx) : gmap atom ty :=
  Σ ∪ erase_ctx Γ.

Definition denot_ty_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_on (erase_ctx_under Σ Γ) τ e.

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

Lemma denot_ty_fuel_env_agree gas Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (fv_cty τ ∪ fv_tm e) Σ1 Σ2 →
  denot_ty_fuel gas Σ1 τ e = denot_ty_fuel gas Σ2 τ e.
Proof.
Admitted.

Lemma denot_ty_under_env_agree Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (fv_cty τ ∪ fv_tm e) Σ1 Σ2 →
  denot_ty_under Σ1 τ e = denot_ty_under Σ2 τ e.
Proof.
  intros Hdom Hagree.
  unfold denot_ty_under, denot_ty_on.
  apply denot_ty_fuel_env_agree; assumption.
Qed.

Lemma denot_ty_under_env_equiv Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (fv_cty τ ∪ fv_tm e) Σ1 Σ2 →
  denot_ty_under Σ1 τ e ⊣⊢ denot_ty_under Σ2 τ e.
Proof.
  intros Hdom Hagree.
  rewrite (denot_ty_under_env_agree Σ1 Σ2 τ e Hdom Hagree).
  apply formula_equiv_refl.
Qed.

Lemma denot_ty_in_ctx_env_agree Γ1 Γ2 τ e :
  dom (erase_ctx Γ1) = dom (erase_ctx Γ2) →
  ty_env_agree_on (fv_cty τ ∪ fv_tm e) (erase_ctx Γ1) (erase_ctx Γ2) →
  denot_ty_in_ctx Γ1 τ e = denot_ty_in_ctx Γ2 τ e.
Proof.
  intros Hdom Hagree. unfold denot_ty_in_ctx.
  apply denot_ty_under_env_agree.
  - exact Hdom.
  - exact Hagree.
Qed.

Lemma denot_ty_in_ctx_env_equiv Γ1 Γ2 τ e :
  dom (erase_ctx Γ1) = dom (erase_ctx Γ2) →
  ty_env_agree_on (fv_cty τ ∪ fv_tm e) (erase_ctx Γ1) (erase_ctx Γ2) →
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

Lemma denot_ty_obligations_formula_fv_subset Σ τ e φ S :
  dom Σ ∪ formula_fv φ ⊆ S →
  formula_fv (denot_ty_obligations Σ τ e φ) ⊆ S.
Proof.
  unfold denot_ty_obligations, FBasicTypingIn, FClosedResourceIn,
    FStrongTotalIn, FPure, FResourceAtom, FStoreResourceAtom.
  simpl. unfold stale, stale_logic_qualifier. simpl.
  set_solver.
Qed.

Lemma denot_ty_fuel_formula_fv_subset gas Σ τ e :
  cty_measure τ <= gas →
  formula_fv (denot_ty_fuel gas Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  revert Σ τ e.
  induction gas as [|gas IH]; intros Σ τ e Hgas.
  - pose proof (cty_measure_gt_0 τ). lia.
  - rewrite denot_ty_fuel_unfold.
  apply denot_ty_obligations_formula_fv_subset.
    destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ];
      cbn [denot_ty_fuel_body cty_measure fv_cty] in *.
    + assert (Hbody :
        formula_fv
          (FExprContIn Σ e (λ ν : atom,
             let φν := qual_open_atom 0 ν φ in
             FAnd
               (basic_world_formula (<[ν:=TBase b]> Σ)
                 ({[ν]} ∪ qual_dom φν))
               (fib_vars (qual_dom φν)
                 (FOver (FTypeQualifier φν)))))
        ⊆ dom Σ ∪ fv_cty (CTOver b φ)).
      {
        apply FExprContIn_formula_fv_subset; first set_solver.
        intros ν _.
        cbn [formula_fv].
        rewrite basic_world_formula_fv.
        rewrite fib_vars_formula_fv.
        destruct φ as [B d p].
        unfold qual_open_atom, FTypeQualifier, qual_dom in *; simpl in *.
        destruct (decide (0 ∈ B)); simpl.
        all: unfold stale, stale_logic_qualifier; simpl; set_solver.
      }
      set_solver.
    + assert (Hbody :
        formula_fv
          (FExprContIn Σ e (λ ν : atom,
             let φν := qual_open_atom 0 ν φ in
             FAnd
               (basic_world_formula (<[ν:=TBase b]> Σ)
                 ({[ν]} ∪ qual_dom φν))
               (fib_vars (qual_dom φν)
                 (FUnder (FTypeQualifier φν)))))
        ⊆ dom Σ ∪ fv_cty (CTUnder b φ)).
      {
        apply FExprContIn_formula_fv_subset; first set_solver.
        intros ν _.
        cbn [formula_fv].
        rewrite basic_world_formula_fv.
        rewrite fib_vars_formula_fv.
        destruct φ as [B d p].
        unfold qual_open_atom, FTypeQualifier, qual_dom in *; simpl in *.
        destruct (decide (0 ∈ B)); simpl.
        all: unfold stale, stale_logic_qualifier; simpl; set_solver.
      }
      set_solver.
    + pose proof (IH Σ τ1 e ltac:(lia)) as H1.
      pose proof (IH Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    + pose proof (IH Σ τ1 e ltac:(lia)) as H1.
      pose proof (IH Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    + pose proof (IH Σ τ1 e ltac:(lia)) as H1.
      pose proof (IH Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    + assert (Hbody :
        formula_fv
          (fresh_forall (dom Σ) (λ x : atom,
             let Σx := <[x:=erase_ty τx]> Σ in
             FImpl
               (denot_ty_fuel gas Σx τx (tret (vfvar x)))
               (denot_ty_fuel gas Σx ({0 ~> x} τ)
                 (tapp_tm e (vfvar x)))))
        ⊆ dom Σ ∪ (fv_cty τx ∪ fv_cty τ)).
      {
        apply fresh_forall_formula_fv_subset
          with (S := dom Σ ∪ (fv_cty τx ∪ fv_cty τ)).
        - set_solver.
        - intros x Hx.
          set (Σx := <[x:=erase_ty τx]> Σ).
          pose proof (IH Σx τx (tret (vfvar x)) ltac:(lia)) as Harg.
          pose proof (IH Σx ({0 ~> x} τ)
            (tapp_tm e (vfvar x)) ltac:(rewrite cty_open_preserves_measure; lia))
            as Hres.
          pose proof (cty_open_fv_subset 0 x τ) as Hopen.
          unfold Σx in *.
          rewrite !dom_insert_L in *.
          set_solver.
      }
      set_solver.
    + assert (Hbody :
        formula_fv
          (fresh_forall (dom Σ) (λ x : atom,
             let Σx := <[x:=erase_ty τx]> Σ in
             FWand
               (denot_ty_fuel gas Σx τx (tret (vfvar x)))
               (denot_ty_fuel gas Σx ({0 ~> x} τ)
                 (tapp_tm e (vfvar x)))))
        ⊆ dom Σ ∪ (fv_cty τx ∪ fv_cty τ)).
      {
        apply fresh_forall_formula_fv_subset
          with (S := dom Σ ∪ (fv_cty τx ∪ fv_cty τ)).
        - set_solver.
        - intros x Hx.
          set (Σx := <[x:=erase_ty τx]> Σ).
          pose proof (IH Σx τx (tret (vfvar x)) ltac:(lia)) as Harg.
          pose proof (IH Σx ({0 ~> x} τ)
            (tapp_tm e (vfvar x)) ltac:(rewrite cty_open_preserves_measure; lia))
            as Hres.
          pose proof (cty_open_fv_subset 0 x τ) as Hopen.
          unfold Σx in *.
          rewrite !dom_insert_L in *.
          set_solver.
      }
      set_solver.
Qed.

Lemma denot_ty_fuel_body_formula_fv_subset gas Σ τ e :
  cty_measure τ <= gas →
  formula_fv (denot_ty_fuel_body gas Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  intros Hgas.
  destruct gas as [|gas].
  - pose proof (cty_measure_gt_0 τ). lia.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ];
      cbn [denot_ty_fuel_body cty_measure fv_cty] in *.
    + apply FExprContIn_formula_fv_subset; first set_solver.
      intros ν _.
      cbn [formula_fv].
      rewrite basic_world_formula_fv.
      rewrite fib_vars_formula_fv.
      destruct φ as [B d p].
      unfold qual_open_atom, FTypeQualifier, qual_dom in *; simpl in *.
      destruct (decide (0 ∈ B)); simpl.
      all: unfold stale, stale_logic_qualifier; simpl; set_solver.
    + apply FExprContIn_formula_fv_subset; first set_solver.
      intros ν _.
      cbn [formula_fv].
      rewrite basic_world_formula_fv.
      rewrite fib_vars_formula_fv.
      destruct φ as [B d p].
      unfold qual_open_atom, FTypeQualifier, qual_dom in *; simpl in *.
      destruct (decide (0 ∈ B)); simpl.
      all: unfold stale, stale_logic_qualifier; simpl; set_solver.
    + pose proof (denot_ty_fuel_formula_fv_subset gas Σ τ1 e ltac:(lia)) as H1.
      pose proof (denot_ty_fuel_formula_fv_subset gas Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    + pose proof (denot_ty_fuel_formula_fv_subset gas Σ τ1 e ltac:(lia)) as H1.
      pose proof (denot_ty_fuel_formula_fv_subset gas Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    + pose proof (denot_ty_fuel_formula_fv_subset gas Σ τ1 e ltac:(lia)) as H1.
      pose proof (denot_ty_fuel_formula_fv_subset gas Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    + apply fresh_forall_formula_fv_subset
        with (S := dom Σ ∪ (fv_cty τx ∪ fv_cty τ)).
      * set_solver.
      * intros x Hx.
        set (Σx := <[x:=erase_ty τx]> Σ).
        pose proof (denot_ty_fuel_formula_fv_subset gas Σx τx
          (tret (vfvar x)) ltac:(lia)) as Harg.
        pose proof (denot_ty_fuel_formula_fv_subset gas Σx ({0 ~> x} τ)
          (tapp_tm e (vfvar x)) ltac:(rewrite cty_open_preserves_measure; lia))
          as Hres.
        pose proof (cty_open_fv_subset 0 x τ) as Hopen.
        unfold Σx in *.
        rewrite !dom_insert_L in *.
        set_solver.
    + apply fresh_forall_formula_fv_subset
        with (S := dom Σ ∪ (fv_cty τx ∪ fv_cty τ)).
      * set_solver.
      * intros x Hx.
        set (Σx := <[x:=erase_ty τx]> Σ).
        pose proof (denot_ty_fuel_formula_fv_subset gas Σx τx
          (tret (vfvar x)) ltac:(lia)) as Harg.
        pose proof (denot_ty_fuel_formula_fv_subset gas Σx ({0 ~> x} τ)
          (tapp_tm e (vfvar x)) ltac:(rewrite cty_open_preserves_measure; lia))
          as Hres.
        pose proof (cty_open_fv_subset 0 x τ) as Hopen.
        unfold Σx in *.
        rewrite !dom_insert_L in *.
        set_solver.
Qed.

Lemma denot_ty_fuel_formula_fv_subset_env
    gas (Σ : gmap atom ty) (τ : choice_ty) e :
  cty_measure τ <= gas →
  fv_cty τ ⊆ dom Σ →
  formula_fv (denot_ty_fuel gas Σ τ e) ⊆ dom Σ.
Proof.
  intros Hgas Hfv.
  pose proof (denot_ty_fuel_formula_fv_subset gas Σ τ e Hgas) as Hφ.
  set_solver.
Qed.

Lemma denot_ty_fuel_body_formula_fv_subset_env
    gas (Σ : gmap atom ty) (τ : choice_ty) e :
  cty_measure τ <= gas →
  fv_cty τ ⊆ dom Σ →
  formula_fv (denot_ty_fuel_body gas Σ τ e) ⊆ dom Σ.
Proof.
  intros Hgas Hfv.
  pose proof (denot_ty_fuel_body_formula_fv_subset gas Σ τ e Hgas) as Hφ.
  set_solver.
Qed.

Lemma denot_ty_formula_fv_subset τ e :
  formula_fv (denot_ty τ e) ⊆ fv_cty τ.
Proof.
  unfold denot_ty, denot_ty_under, denot_ty_on.
  pose proof (denot_ty_fuel_formula_fv_subset
    (cty_measure τ) ∅ τ e ltac:(lia)) as Hfv.
  intros z Hz. apply Hfv in Hz. set_solver.
Qed.

Lemma denot_ty_fuel_formula_fv_env_agree gas Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  formula_fv (denot_ty_fuel gas Σ1 τ e) =
  formula_fv (denot_ty_fuel gas Σ2 τ e).
Proof.
Admitted.

Lemma denot_ty_under_formula_fv_subset Σ τ e :
  formula_fv (denot_ty_under Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  unfold denot_ty_under, denot_ty_on.
  pose proof (denot_ty_fuel_formula_fv_subset
    (cty_measure τ) Σ τ e ltac:(lia)) as Hfv.
  intros z Hz. apply Hfv in Hz. set_solver.
Qed.

Lemma denot_ty_on_formula_fv_subset Σ τ e :
  formula_fv (denot_ty_on Σ τ e) ⊆ dom Σ ∪ fv_cty τ.
Proof.
  apply denot_ty_under_formula_fv_subset.
Qed.

Lemma denot_ty_in_ctx_under_formula_fv_subset Σ Γ τ e :
  formula_fv (denot_ty_in_ctx_under Σ Γ τ e) ⊆
    dom (erase_ctx_under Σ Γ) ∪ fv_cty τ.
Proof.
  unfold denot_ty_in_ctx_under.
  apply denot_ty_on_formula_fv_subset.
Qed.

Lemma denot_ty_fuel_env_fv_subset gas Σ τ e :
  cty_measure τ <= gas →
  dom Σ ⊆ formula_fv (denot_ty_fuel gas Σ τ e).
Proof.
  intros _.
  rewrite denot_ty_fuel_unfold.
  unfold denot_ty_obligations,
      FBasicTypingIn, FClosedResourceIn, FStrongTotalIn,
      FPure, FResourceAtom, FStoreResourceAtom;
    simpl; unfold stale, stale_logic_qualifier; simpl; set_solver.
Qed.

Lemma denot_ty_under_result_atom_fv Σ x τ :
  x ∈ dom Σ →
  x ∈ formula_fv (denot_ty_under Σ τ (tret (vfvar x))).
Proof.
  intros Hx.
  unfold denot_ty_under, denot_ty_on.
  pose proof (denot_ty_fuel_env_fv_subset
    (cty_measure τ) Σ τ (tret (vfvar x)) ltac:(lia)) as Hfv.
  apply Hfv. exact Hx.
Qed.

Lemma denot_ty_on_result_atom_fv Σ x τ :
  x ∈ dom Σ →
  x ∈ formula_fv (denot_ty_on Σ τ (tret (vfvar x))).
Proof.
  apply denot_ty_under_result_atom_fv.
Qed.

Lemma denot_ty_restrict_fv τ e m :
  m ⊨ denot_ty τ e →
  res_restrict m (fv_cty τ) ⊨ denot_ty τ e.
Proof.
  intros Hm.
  eapply res_models_kripke.
  - apply res_restrict_mono. apply denot_ty_formula_fv_subset.
  - apply res_models_restrict_fv. exact Hm.
Qed.

Lemma denot_ty_under_restrict_fv Σ τ e m :
  m ⊨ denot_ty_under Σ τ e →
  res_restrict m (dom Σ ∪ fv_cty τ) ⊨ denot_ty_under Σ τ e.
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
