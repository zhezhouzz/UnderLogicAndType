(** * ChoiceType.TypeDenotation.LemmasSyntax

    Syntax-level locally-nameless and vars-equivalence helpers used by
    the type-denotation proofs. *)


From Stdlib Require Import Logic.FunctionalExtensionality
  Logic.PropExtensionality Lia.
From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps BasicTypingProps
  Sugar.
From ChoiceLogic Require Import FormulaDerived.
From ChoiceType Require Export TypeDenotation.Definitions.
From ChoiceType Require Import BasicStore BasicTyping LocallyNamelessProps
  TypeDenotation.FormulaEquiv.

Local Notation FQ := FormulaQ.

(** MIGRATION NOTE(TypeLanguage): the following [beta_drop_shift_from],
    [qual_parametric], and [cty_parametric] material belongs to the legacy
    qualifier representation, where qualifier predicates could inspect the
    beta/store arguments directly.  The new TypeLanguage qualifier is
    dependent over its syntactic domain and no longer needs these parametricity
    repair lemmas.  Do not migrate this block into TypeLanguage; keep it only
    as legacy evidence for old TypeDenotation files until that layer is
    rewritten. *)

Lemma beta_drop_shift_from_lookup k β n :
  beta_drop_shift_from k β !! n =
  if decide (n < k) then β !! n else β !! S n.
Proof.
  unfold beta_drop_shift_from.
  refine (fin_maps.map_fold_ind
    (fun β => ∀ n,
      map_fold
        (fun (i : nat) (v : value) (acc : gmap nat value) =>
          if decide (i < k) then <[i:=v]> acc
          else if decide (i = k) then acc
          else <[Nat.pred i:=v]> acc) ∅ β !! n =
      if decide (n < k) then β !! n else β !! S n) _ _ β n).
  - intros n0. rewrite map_fold_empty, !lookup_empty.
    destruct (decide (n0 < k)); reflexivity.
  - intros i v β' Hfresh Hfold IH n0.
    rewrite Hfold.
    destruct (decide (i < k)) as [Hik|Hik].
    + destruct (decide (n0 < k)) as [Hnk|Hnk].
      * destruct (decide (n0 = i)) as [->|Hne].
        -- rewrite !lookup_insert_eq. reflexivity.
        -- rewrite !lookup_insert_ne by congruence.
           rewrite IH. destruct (decide (n0 < k)) as [_|Hbad]; [reflexivity|lia].
      * rewrite lookup_insert_ne by lia.
        rewrite lookup_insert_ne by lia.
        rewrite IH. destruct (decide (n0 < k)) as [Hbad|_]; [lia|reflexivity].
    + destruct (decide (i = k)) as [->|Hik'].
      * destruct (decide (n0 < k)) as [Hnk|Hnk].
        -- rewrite lookup_insert_ne by lia.
           rewrite IH. destruct (decide (n0 < k)) as [_|Hbad]; [reflexivity|lia].
        -- rewrite lookup_insert_ne by lia.
           rewrite IH. destruct (decide (n0 < k)) as [Hbad|_]; [lia|reflexivity].
      * destruct (decide (n0 < k)) as [Hnk|Hnk].
        -- rewrite lookup_insert_ne by lia.
           rewrite lookup_insert_ne by lia.
           rewrite IH. destruct (decide (n0 < k)) as [_|Hbad]; [reflexivity|lia].
        -- destruct (decide (S n0 = i)) as [Hni|Hni].
           ++ assert (Hpred : Nat.pred i = n0) by lia.
              rewrite Hpred, lookup_insert_eq.
              rewrite Hni, lookup_insert_eq. reflexivity.
           ++ assert (Hpred_ne : n0 ≠ Nat.pred i) by lia.
              rewrite lookup_insert_ne by (intros Heq; apply Hpred_ne; symmetry; exact Heq).
              rewrite lookup_insert_ne by (intros Heq; apply Hni; symmetry; exact Heq).
              rewrite IH. destruct (decide (n0 < k)) as [Hbad|_]; [lia|reflexivity].
Qed.

(** The current qualifier syntax is shallow: a qualifier stores an arbitrary
    Rocq predicate [prop] alongside the syntactic support [D].  For strong LN
    equalities, local closure of [D] is not enough; [prop] also has to be
    semantically scoped by [D].  This predicate records that invariant until it
    is folded into the general well-formedness/basic-choice-type layer. *)
Definition qual_parametric (φ : type_qualifier) : Prop :=
  match φ with
  | qual D p =>
      ∀ β1 β2 σ1 σ2 ρ1 ρ2,
        map_restrict value β1 (lvars_bv D) =
        map_restrict value β2 (lvars_bv D) ->
        store_restrict σ1 (lvars_fv D) =
        store_restrict σ2 (lvars_fv D) ->
        store_restrict ρ1 (lvars_fv D) =
        store_restrict ρ2 (lvars_fv D) ->
        (p β1 σ1 ρ1 ↔ p β2 σ2 ρ2)
  end.

Fixpoint cty_parametric (τ : choice_ty) : Prop :=
  match τ with
  | CTOver _ φ => qual_parametric φ
  | CTUnder _ φ => qual_parametric φ
  | CTInter τ1 τ2
  | CTUnion τ1 τ2
  | CTSum τ1 τ2
  | CTArrow τ1 τ2
  | CTWand τ1 τ2 => cty_parametric τ1 ∧ cty_parametric τ2
  end.

Definition qual_bvars_below (k : nat) (φ : type_qualifier) : Prop :=
  ∀ n, n ∈ qual_bvars φ -> n < k.

Fixpoint cty_bvars_below_at (k : nat) (τ : choice_ty) : Prop :=
  match τ with
  | CTOver _ φ => qual_bvars_below (S k) φ
  | CTUnder _ φ => qual_bvars_below (S k) φ
  | CTInter τ1 τ2
  | CTUnion τ1 τ2
  | CTSum τ1 τ2 => cty_bvars_below_at k τ1 ∧ cty_bvars_below_at k τ2
  | CTArrow τ1 τ2
  | CTWand τ1 τ2 => cty_bvars_below_at k τ1 ∧ cty_bvars_below_at (S k) τ2
  end.

Lemma map_restrict_beta_drop_shift_from_below k β B :
  (∀ n, n ∈ B -> n < k) ->
  map_restrict value (beta_drop_shift_from k β) B =
    map_restrict value β B.
Proof.
  intros Hbelow.
  apply map_eq. intros n.
  unfold map_restrict.
  destruct (decide (n ∈ B)) as [Hn|Hn].
  - pose proof (Hbelow n Hn) as Hlt.
    destruct (β !! n) as [v|] eqn:Hβ.
    + transitivity (Some v).
      * apply map_lookup_filter_Some_2; [| exact Hn].
        rewrite beta_drop_shift_from_lookup.
        destruct (decide (n < k)) as [_|Hbad]; [|lia].
        exact Hβ.
      * symmetry. apply map_lookup_filter_Some_2; [exact Hβ | exact Hn].
    + transitivity (@None value).
      * apply map_lookup_filter_None_2. left.
        rewrite beta_drop_shift_from_lookup.
        destruct (decide (n < k)) as [_|Hbad]; [|lia].
        exact Hβ.
      * symmetry. apply map_lookup_filter_None_2. left. exact Hβ.
  - transitivity (@None value).
    + apply map_lookup_filter_None_2. right.
      intros v Hv Hn'. exact (Hn Hn').
    + symmetry. apply map_lookup_filter_None_2. right.
      intros v Hv Hn'. exact (Hn Hn').
Qed.

Lemma lvars_shift_from_below_id k D :
  (∀ n, n ∈ lvars_bv D -> n < k) ->
  lvars_shift_from k D = D.
Proof.
  intros Hbelow.
  apply set_eq. intros v.
  split.
  - intros Hv.
    unfold lvars_shift_from in Hv.
    apply elem_of_map in Hv as [u [-> Hu]].
    destruct u as [n|a]; cbn [shift_at shift_logic_var_inst logic_var_shift_from].
    + destruct (decide (k <= n)) as [Hbad|_].
      * exfalso. pose proof (Hbelow n ltac:(apply lvars_bv_elem; exact Hu)).
        lia.
      * exact Hu.
    + exact Hu.
  - intros Hv.
    unfold lvars_shift_from.
    apply elem_of_map.
    exists v. split; [| exact Hv].
    destruct v as [n|a]; cbn [shift_at shift_logic_var_inst logic_var_shift_from].
    + destruct (decide (k <= n)) as [Hbad|_].
      * exfalso. pose proof (Hbelow n ltac:(apply lvars_bv_elem; exact Hv)).
        lia.
      * reflexivity.
    + reflexivity.
Qed.

Lemma qual_shift_from_below_parametric_id k φ :
  qual_bvars_below k φ ->
  qual_parametric φ ->
  qual_shift_from k φ = φ.
Proof.
  destruct φ as [D p].
  intros Hbelow Hparam.
  cbn [qual_bvars_below qual_bvars qual_parametric] in *.
  cbn [qual_shift_from].
  rewrite lvars_shift_from_below_id by exact Hbelow.
  f_equal.
  apply functional_extensionality; intro β.
  apply functional_extensionality; intro σ.
  apply functional_extensionality; intro ρ.
  apply propositional_extensionality.
  specialize (Hparam (beta_drop_shift_from k β) β σ σ ρ ρ).
  apply Hparam.
  - apply map_restrict_beta_drop_shift_from_below. exact Hbelow.
  - reflexivity.
  - reflexivity.
Qed.

Lemma qual_open_below_noop k y φ :
  qual_bvars_below k φ ->
  qual_open_atom k y φ = φ.
Proof.
  destruct φ as [D p].
  intros Hbelow.
  cbn [qual_bvars_below qual_bvars] in Hbelow.
  unfold qual_open_atom, qual_bvars.
  destruct (decide (k ∈ lvars_bv D)) as [Hin|Hnot].
  - exfalso. pose proof (Hbelow k Hin). lia.
  - reflexivity.
Qed.

Lemma qual_bvars_below_body φ :
  body_qualifier φ ->
  qual_bvars_below 1 φ.
Proof.
  intros [L Hbody].
  pose (y := fresh_for L).
  assert (Hy : y ∉ L) by (subst y; apply fresh_for_not_in).
  specialize (Hbody y Hy).
  destruct φ as [D p].
  cbn [qual_bvars_below qual_bvars lc_qualifier qual_open_atom
    qual_bvars] in *.
  destruct (decide (0 ∈ lvars_bv D)) as [H0|H0].
  - change (lvars_bv (lvars_open 0 y D) = ∅) in Hbody.
    rewrite lvars_bv_open in Hbody.
    intros n Hn.
    destruct (decide (n = 0)) as [->|Hne]; [lia|].
    assert (n ∈ (∅ : gset nat)) as Hempty.
    { rewrite <- Hbody. set_solver. }
    set_solver.
  - intros n Hn.
    change (lvars_bv D = ∅) in Hbody.
    assert (n ∈ (∅ : gset nat)) as Hempty.
    { rewrite <- Hbody. exact Hn. }
    set_solver.
Qed.

Lemma qual_bvars_below_open_inv k y φ :
  qual_bvars_below k (qual_open_atom k y φ) ->
  qual_bvars_below (S k) φ.
Proof.
  destruct φ as [D p].
  cbn [qual_bvars_below qual_bvars qual_open_atom].
  destruct (decide (k ∈ lvars_bv D)) as [Hk|Hk].
  - intros Hbelow n Hn.
    destruct (decide (n = k)) as [->|Hne]; [lia|].
    assert (n ∈ lvars_bv D ∖ {[k]}) by set_solver.
    assert (n ∈ qual_bvars
      (qual (lvars_open k y D)
        (λ β σ a,
          ∃ v : value,
            σ !! y = Some v ∧
            p (<[k := v]> β) (store_restrict σ (lvars_fv D))
              (store_restrict a (lvars_fv D))))) as Hopen.
    { cbn [qual_bvars]. rewrite lvars_bv_open. exact H. }
    pose proof (Hbelow n Hopen) as Hlt. lia.
  - intros Hbelow n Hn.
    pose proof (Hbelow n Hn) as Hlt. lia.
Qed.

Lemma cty_bvars_below_at_open_inv k y τ :
  cty_bvars_below_at k ({k ~> y} τ) ->
  cty_bvars_below_at (S k) τ.
Proof.
  induction τ in k |- *; cbn [cty_bvars_below_at open_one
    open_cty_atom_inst cty_open]; intros Hbelow.
  - apply qual_bvars_below_open_inv with (y := y). exact Hbelow.
  - apply qual_bvars_below_open_inv with (y := y). exact Hbelow.
  - destruct Hbelow as [Hbelow1 Hbelow2]. split; eauto.
  - destruct Hbelow as [Hbelow1 Hbelow2]. split; eauto.
  - destruct Hbelow as [Hbelow1 Hbelow2]. split; eauto.
  - destruct Hbelow as [Hbelow1 Hbelow2]. split; eauto.
  - destruct Hbelow as [Hbelow1 Hbelow2]. split; eauto.
Qed.

Lemma cty_shift_below_parametric_id k τ :
  cty_bvars_below_at k τ ->
  cty_parametric τ ->
  cty_shift k τ = τ.
Proof.
  induction τ in k |- *; cbn [cty_bvars_below_at cty_parametric cty_shift];
    intros Hbelow Hparam.
  - rewrite qual_shift_from_below_parametric_id by assumption. reflexivity.
  - rewrite qual_shift_from_below_parametric_id by assumption. reflexivity.
  - destruct Hbelow as [Hbelow1 Hbelow2].
    destruct Hparam as [Hparam1 Hparam2].
    rewrite IHτ1 by assumption.
    rewrite IHτ2 by assumption.
    reflexivity.
  - destruct Hbelow as [Hbelow1 Hbelow2].
    destruct Hparam as [Hparam1 Hparam2].
    rewrite IHτ1 by assumption.
    rewrite IHτ2 by assumption.
    reflexivity.
  - destruct Hbelow as [Hbelow1 Hbelow2].
    destruct Hparam as [Hparam1 Hparam2].
    rewrite IHτ1 by assumption.
    rewrite IHτ2 by assumption.
    reflexivity.
  - destruct Hbelow as [Hbelow1 Hbelow2].
    destruct Hparam as [Hparam1 Hparam2].
    rewrite IHτ1 by assumption.
    rewrite IHτ2 by assumption.
    reflexivity.
  - destruct Hbelow as [Hbelow1 Hbelow2].
    destruct Hparam as [Hparam1 Hparam2].
    rewrite IHτ1 by assumption.
    rewrite IHτ2 by assumption.
    reflexivity.
Qed.

Lemma cty_open_below_noop k y τ :
  cty_bvars_below_at k τ ->
  {k ~> y} τ = τ.
Proof.
  induction τ in k |- *; cbn [cty_bvars_below_at open_one open_cty_atom_inst cty_open];
    intros Hbelow.
  - rewrite qual_open_below_noop by exact Hbelow. reflexivity.
  - rewrite qual_open_below_noop by exact Hbelow. reflexivity.
  - destruct Hbelow as [Hbelow1 Hbelow2].
    rewrite IHτ1 by assumption.
    rewrite IHτ2 by assumption.
    reflexivity.
  - destruct Hbelow as [Hbelow1 Hbelow2].
    rewrite IHτ1 by assumption.
    rewrite IHτ2 by assumption.
    reflexivity.
  - destruct Hbelow as [Hbelow1 Hbelow2].
    rewrite IHτ1 by assumption.
    rewrite IHτ2 by assumption.
    reflexivity.
  - destruct Hbelow as [Hbelow1 Hbelow2].
    rewrite IHτ1 by assumption.
    rewrite IHτ2 by assumption.
    reflexivity.
  - destruct Hbelow as [Hbelow1 Hbelow2].
    rewrite IHτ1 by assumption.
    rewrite IHτ2 by assumption.
    reflexivity.
Qed.

Lemma cty_bvars_below_at_lc0 τ :
  lc_choice_ty τ ->
  cty_bvars_below_at 0 τ.
Proof.
  intros Hlc.
  induction Hlc; cbn [cty_bvars_below_at].
  - apply qual_bvars_below_body. exact H.
  - apply qual_bvars_below_body. exact H.
  - split; assumption.
  - split; assumption.
  - split; assumption.
  - split; [assumption|].
    pose (y := fresh_for L).
    assert (Hy : y ∉ L) by (subst y; apply fresh_for_not_in).
    specialize (H0 y Hy).
    apply cty_bvars_below_at_open_inv with (y := y).
    exact H0.
  - split; [assumption|].
    pose (y := fresh_for L).
    assert (Hy : y ∉ L) by (subst y; apply fresh_for_not_in).
    specialize (H0 y Hy).
    apply cty_bvars_below_at_open_inv with (y := y).
    exact H0.
Qed.

Lemma qual_parametric_open k y φ :
  qual_parametric φ ->
  qual_parametric (qual_open_atom k y φ).
Proof.
  destruct φ as [D p].
  intros Hparam.
  cbn [qual_parametric qual_open_atom qual_bvars].
  destruct (decide (k ∈ lvars_bv D)) as [Hk|Hk].
  2:{ exact Hparam. }
  intros β1 β2 σ1 σ2 ρ1 ρ2 Hβ Hσ Hρ.
  assert (Hfv_sub : lvars_fv D ⊆ lvars_fv (lvars_open k y D)).
  {
    intros z Hz.
    rewrite lvars_fv_open_has_bv by exact Hk.
    apply elem_of_union_l. exact Hz.
  }
  assert (Hy : y ∈ lvars_fv (lvars_open k y D)).
  {
    rewrite lvars_fv_open_has_bv by exact Hk.
    apply elem_of_union_r. apply elem_of_singleton. reflexivity.
  }
  assert (HσD : σ1 |ₛ lvars_fv D = σ2 |ₛ lvars_fv D).
  {
    apply store_restrict_eq_mono with
      (Y := lvars_fv (lvars_open k y D)); assumption.
  }
  assert (HρD : ρ1 |ₛ lvars_fv D = ρ2 |ₛ lvars_fv D).
  {
    apply store_restrict_eq_mono with
      (Y := lvars_fv (lvars_open k y D)); assumption.
  }
  split; intros (v & Hv & Hp); exists v.
  - split.
    + eapply store_restrict_lookup_transport.
      * exact Hy.
      * exact Hσ.
      * exact Hv.
    + pose proof (Hparam (<[k := v]> β1) (<[k := v]> β2)
        (store_restrict σ1 (lvars_fv D))
        (store_restrict σ2 (lvars_fv D))
        (store_restrict ρ1 (lvars_fv D))
        (store_restrict ρ2 (lvars_fv D))) as Hiff.
      assert (Hiff' :
        p (<[k:=v]> β1) (σ1 |ₛ lvars_fv D) (ρ1 |ₛ lvars_fv D) <->
        p (<[k:=v]> β2) (σ2 |ₛ lvars_fv D) (ρ2 |ₛ lvars_fv D)).
      {
        apply Hiff.
        - rewrite <- (map_restrict_insert_open_bv β1 k y D v Hk).
          rewrite <- (map_restrict_insert_open_bv β2 k y D v Hk).
          rewrite Hβ. reflexivity.
        - rewrite !store_restrict_twice_same. exact HσD.
        - rewrite !store_restrict_twice_same. exact HρD.
      }
      exact (proj1 Hiff' Hp).
  - split.
    + eapply store_restrict_lookup_transport.
      * exact Hy.
      * symmetry. exact Hσ.
      * exact Hv.
    + pose proof (Hparam (<[k := v]> β1) (<[k := v]> β2)
        (store_restrict σ1 (lvars_fv D))
        (store_restrict σ2 (lvars_fv D))
        (store_restrict ρ1 (lvars_fv D))
        (store_restrict ρ2 (lvars_fv D))) as Hiff.
      assert (Hiff' :
        p (<[k:=v]> β1) (σ1 |ₛ lvars_fv D) (ρ1 |ₛ lvars_fv D) <->
        p (<[k:=v]> β2) (σ2 |ₛ lvars_fv D) (ρ2 |ₛ lvars_fv D)).
      {
        apply Hiff.
        - rewrite <- (map_restrict_insert_open_bv β1 k y D v Hk).
          rewrite <- (map_restrict_insert_open_bv β2 k y D v Hk).
          rewrite Hβ. reflexivity.
        - rewrite !store_restrict_twice_same. exact HσD.
        - rewrite !store_restrict_twice_same. exact HρD.
      }
      exact (proj2 Hiff' Hp).
Qed.

Lemma cty_parametric_open k y τ :
  cty_parametric τ ->
  cty_parametric ({k ~> y} τ).
Proof.
  induction τ in k |- *; cbn [cty_parametric open_one open_cty_atom_inst cty_open];
    intros Hparam.
  - apply qual_parametric_open. exact Hparam.
  - apply qual_parametric_open. exact Hparam.
  - destruct Hparam as [H1 H2]. split; [apply IHτ1 | apply IHτ2]; assumption.
  - destruct Hparam as [H1 H2]. split; [apply IHτ1 | apply IHτ2]; assumption.
  - destruct Hparam as [H1 H2]. split; [apply IHτ1 | apply IHτ2]; assumption.
  - destruct Hparam as [H1 H2]. split; [apply IHτ1 | apply IHτ2]; assumption.
  - destruct Hparam as [H1 H2]. split; [apply IHτ1 | apply IHτ2]; assumption.
Qed.

Lemma cty_open_shift0_lc_parametric y τ :
  lc_choice_ty τ ->
  cty_parametric τ ->
  {0 ~> y} (↑[0] τ) = τ.
Proof.
  intros Hlc Hparam.
  pose proof (cty_bvars_below_at_lc0 τ Hlc) as Hbelow.
  change ({0 ~> y} (↑[0] τ)) with ({0 ~> y} (cty_shift 0 τ)).
  rewrite (cty_shift_below_parametric_id 0 τ Hbelow Hparam).
  apply cty_open_below_noop. exact Hbelow.
Qed.

Fixpoint cty_vars_equiv (τ1 τ2 : choice_ty) : Prop :=
  match τ1, τ2 with
  | CTOver b1 φ1, CTOver b2 φ2 =>
      b1 = b2 ∧ qual_vars φ1 = qual_vars φ2
  | CTUnder b1 φ1, CTUnder b2 φ2 =>
      b1 = b2 ∧ qual_vars φ1 = qual_vars φ2
  | CTInter τ11 τ12, CTInter τ21 τ22
  | CTUnion τ11 τ12, CTUnion τ21 τ22
  | CTSum τ11 τ12, CTSum τ21 τ22
  | CTArrow τ11 τ12, CTArrow τ21 τ22
  | CTWand τ11 τ12, CTWand τ21 τ22 =>
      cty_vars_equiv τ11 τ21 ∧ cty_vars_equiv τ12 τ22
  | _, _ => False
  end.

Notation "τ1 ≡τv τ2" := (cty_vars_equiv τ1 τ2)
  (at level 70, no associativity).

Class VarsEquiv (A : Type) := vars_equiv : relation A.

Notation "x ≈v y" := (vars_equiv x y)
  (at level 70, no associativity).

#[global] Instance vars_equiv_choice_ty : VarsEquiv choice_ty :=
  cty_vars_equiv.

#[global] Instance cty_vars_equiv_equivalence : Equivalence cty_vars_equiv.
Proof.
  split.
  - intro τ. induction τ; cbn [cty_vars_equiv]; try split; eauto.
  - intros τ1 τ2. induction τ1 in τ2 |- *.
    all: destruct τ2; cbn [cty_vars_equiv]; try tauto;
      intros H; destruct H as [H1 H2]; split; try congruence;
      try symmetry; eauto.
  - intros τ1 τ2 τ3. induction τ1 in τ2, τ3 |- *.
    all: destruct τ2, τ3; cbn [cty_vars_equiv]; try tauto;
      intros Hxy Hyz; destruct Hxy as [Hxy1 Hxy2];
      destruct Hyz as [Hyz1 Hyz2]; split; try congruence;
      try etransitivity; eauto.
Qed.

#[global] Instance cty_vars_equiv_preorder : PreOrder cty_vars_equiv.
Proof.
  split.
  - intro τ. reflexivity.
  - intros τ1 τ2 τ3 H12 H23. transitivity τ2; assumption.
Qed.

#[global] Instance vars_equiv_choice_ty_equivalence :
  Equivalence (@vars_equiv choice_ty vars_equiv_choice_ty).
Proof. apply cty_vars_equiv_equivalence. Qed.

#[global] Instance vars_equiv_choice_ty_preorder :
  PreOrder (@vars_equiv choice_ty vars_equiv_choice_ty).
Proof. apply cty_vars_equiv_preorder. Qed.

Lemma cty_vars_equiv_erase τ1 τ2 :
  τ1 ≡τv τ2 →
  erase_ty τ1 = erase_ty τ2.
Proof.
  induction τ1 in τ2 |- *; destruct τ2; cbn [cty_vars_equiv erase_ty];
    try tauto; intros H; destruct H as [H1 H2]; subst; eauto;
    rewrite ?(IHτ1_1 _ H1), ?(IHτ1_2 _ H2); reflexivity.
Qed.

Lemma cty_vars_equiv_open k x τ1 τ2 :
  τ1 ≡τv τ2 →
  {k ~> x} τ1 ≡τv {k ~> x} τ2.
Proof.
  induction τ1 in k, τ2 |- *; destruct τ2;
    cbn [cty_vars_equiv cty_open open_one open_cty_atom_inst];
    try tauto; intros H; destruct H as [H1 H2]; split; try congruence;
    try (rewrite !qual_vars_open_atom, H2; reflexivity);
    try (apply IHτ1_1; exact H1);
    try (apply IHτ1_2; exact H2).
Qed.

Lemma cty_vars_equiv_shift_from k τ1 τ2 :
  τ1 ≡τv τ2 →
  cty_shift k τ1 ≡τv cty_shift k τ2.
Proof.
  induction τ1 in k, τ2 |- *; destruct τ2;
    cbn [cty_vars_equiv cty_shift]; try tauto; intros H;
    destruct H as [H1 H2].
  - split; [congruence |].
    destruct φ, φ0. cbn [qual_shift_from qual_vars] in *.
    subst. reflexivity.
  - split; [congruence |].
    destruct φ, φ0. cbn [qual_shift_from qual_vars] in *.
    subst. reflexivity.
  - split; [apply IHτ1_1 | apply IHτ1_2]; assumption.
  - split; [apply IHτ1_1 | apply IHτ1_2]; assumption.
  - split; [apply IHτ1_1 | apply IHτ1_2]; assumption.
  - split; [apply IHτ1_1 | apply IHτ1_2]; assumption.
  - split; [apply IHτ1_1 | apply IHτ1_2]; assumption.
Qed.

Lemma qual_open_same_index_absorb k x y φ :
  qual_open_atom k y (qual_open_atom k x φ) = qual_open_atom k x φ.
Proof.
  destruct φ as [D p].
  unfold qual_open_atom, qual_bvars.
  destruct (decide (k ∈ lvars_bv D)) as [Hk|Hk].
  - cbn [qual_bvars].
    destruct (decide (k ∈ lvars_bv (lvars_open k x D))) as [Hbad|_].
    + rewrite lvars_bv_open in Hbad. set_solver.
    + reflexivity.
  - cbn [qual_bvars].
    destruct (decide (k ∈ lvars_bv D)) as [Hbad|_]; [set_solver |].
    reflexivity.
Qed.

Lemma map_insert_insert_commute_ne {A} (β : gmap nat A) i j (vi vj : A) :
  i ≠ j →
  <[i:=vi]> (<[j:=vj]> β) = <[j:=vj]> (<[i:=vi]> β).
Proof.
  intros Hij.
  apply map_eq. intros n.
  destruct (decide (n = i)) as [->|Hni].
  - rewrite lookup_insert_eq.
    rewrite lookup_insert_ne by congruence.
    rewrite lookup_insert_eq. reflexivity.
  - destruct (decide (n = j)) as [->|Hnj].
    + rewrite lookup_insert_ne by congruence.
      rewrite lookup_insert_eq.
      rewrite lookup_insert_eq. reflexivity.
    + rewrite !lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma qual_open_commute_fvar i j x y φ :
  i ≠ j →
  qual_open_atom i x (qual_open_atom j y φ) =
  qual_open_atom j y (qual_open_atom i x φ).
Proof.
  intros Hij.
  destruct φ as [D p].
  unfold qual_open_atom, qual_bvars.
  destruct (decide (j ∈ lvars_bv D)) as [Hj|Hj];
    destruct (decide (i ∈ lvars_bv D)) as [Hi|Hi];
    cbn [qual_bvars].
  - destruct (decide (i ∈ lvars_bv (lvars_open j y D))) as [Hi'|Hi'];
      [|rewrite lvars_bv_open in Hi'; set_solver].
    destruct (decide (j ∈ lvars_bv (lvars_open i x D))) as [Hj'|Hj'];
      [|rewrite lvars_bv_open in Hj'; set_solver].
    rewrite lvars_open_commute_fvar by exact Hij.
    f_equal.
    repeat (apply functional_extensionality; intro).
    apply propositional_extensionality. split.
    + intros (vx & Hx & vy & Hy & Hp).
      exists vy. split.
      {
        rewrite store_restrict_lookup in Hy.
        rewrite lvars_fv_open_has_bv in Hy by exact Hj.
        destruct (decide (y ∈ lvars_fv D ∪ {[y]})) as [_|Hbad].
        - exact Hy.
        - set_solver.
      }
      exists vx. split.
      {
        rewrite store_restrict_lookup.
        rewrite lvars_fv_open_has_bv by exact Hi.
        destruct (decide (x ∈ lvars_fv D ∪ {[x]})) as [_|Hbad].
        - exact Hx.
        - set_solver.
      }
      rewrite map_insert_insert_commute_ne by congruence.
      repeat rewrite store_restrict_restrict in *.
      repeat match goal with
      | H : context[lvars_fv (lvars_open ?k ?z ?D0)] |- _ =>
          rewrite (lvars_fv_open k z D0) in H
      | |- context[lvars_fv (lvars_open ?k ?z ?D0)] =>
          rewrite (lvars_fv_open k z D0)
      end.
      repeat match goal with
      | H : context[decide (?P)] |- _ =>
          destruct (decide P); try set_solver
      | |- context[decide (?P)] =>
          destruct (decide P); try set_solver
      end.
      repeat match goal with
      | H : context[?A ∩ ?B] |- _ =>
          replace (A ∩ B) with B in H by set_solver
      | |- context[?A ∩ ?B] =>
          replace (A ∩ B) with B by set_solver
      end.
      exact Hp.
    + intros (vy & Hy & vx & Hx & Hp).
      exists vx. split.
      {
        rewrite store_restrict_lookup in Hx.
        rewrite lvars_fv_open_has_bv in Hx by exact Hi.
        destruct (decide (x ∈ lvars_fv D ∪ {[x]})) as [_|Hbad].
        - exact Hx.
        - set_solver.
      }
      exists vy. split.
      {
        rewrite store_restrict_lookup.
        rewrite lvars_fv_open_has_bv by exact Hj.
        destruct (decide (y ∈ lvars_fv D ∪ {[y]})) as [_|Hbad].
        - exact Hy.
        - set_solver.
      }
      rewrite map_insert_insert_commute_ne by congruence.
      repeat rewrite store_restrict_restrict in *.
      repeat match goal with
      | H : context[lvars_fv (lvars_open ?k ?z ?D0)] |- _ =>
          rewrite (lvars_fv_open k z D0) in H
      | |- context[lvars_fv (lvars_open ?k ?z ?D0)] =>
          rewrite (lvars_fv_open k z D0)
      end.
      repeat match goal with
      | H : context[decide (?P)] |- _ =>
          destruct (decide P); try set_solver
      | |- context[decide (?P)] =>
          destruct (decide P); try set_solver
      end.
      repeat match goal with
      | H : context[?A ∩ ?B] |- _ =>
          replace (A ∩ B) with B in H by set_solver
      | |- context[?A ∩ ?B] =>
          replace (A ∩ B) with B by set_solver
      end.
      exact Hp.
  - destruct (decide (i ∈ lvars_bv (lvars_open j y D))) as [Hi'|Hi'].
    { rewrite lvars_bv_open in Hi'. set_solver. }
    destruct (decide (j ∈ lvars_bv D)) as [_|Hbad]; [|set_solver].
    reflexivity.
  - destruct (decide (j ∈ lvars_bv (lvars_open i x D))) as [Hj'|Hj'].
    { rewrite lvars_bv_open in Hj'. set_solver. }
    destruct (decide (i ∈ lvars_bv D)) as [_|Hbad]; [|set_solver].
    reflexivity.
  - destruct (decide (i ∈ lvars_bv D)) as [Hi'|Hi']; [set_solver|].
    destruct (decide (j ∈ lvars_bv D)) as [Hj'|Hj']; [set_solver|].
    reflexivity.
Qed.

#[global] Instance open_commute_qual_eq :
  OpenCommute type_qualifier qual_open_atom eq.
Proof.
  constructor. intros i j x y q Hij.
  apply qual_open_commute_fvar. exact Hij.
Qed.

Definition qual_open_env (η : gmap nat atom) (q : type_qualifier) :
    type_qualifier :=
  map_fold (fun k x acc => qual_open_atom k x acc) q η.

Lemma qual_open_env_empty q :
  qual_open_env ∅ q = q.
Proof. unfold qual_open_env. rewrite map_fold_empty. reflexivity. Qed.

Lemma qual_open_env_insert_fresh η k x q :
  η !! k = None →
  qual_open_env (<[k := x]> η) q =
  qual_open_atom k x (qual_open_env η q).
Proof.
  intros Hfresh.
  unfold qual_open_env.
  apply (open_map_fold_insert_fresh_eq qual_open_atom).
  exact Hfresh.
Qed.

Lemma cty_open_same_index_absorb k x y τ :
  cty_open k y (cty_open k x τ) = cty_open k x τ.
Proof.
  induction τ in k |- *; cbn [cty_open].
  - rewrite qual_open_same_index_absorb. reflexivity.
  - rewrite qual_open_same_index_absorb. reflexivity.
  - rewrite IHτ1, IHτ2. reflexivity.
  - rewrite IHτ1, IHτ2. reflexivity.
  - rewrite IHτ1, IHτ2. reflexivity.
  - rewrite IHτ1, IHτ2. reflexivity.
  - rewrite IHτ1, IHτ2. reflexivity.
Qed.

Lemma cty_open_commute_fvar i j x y τ :
  i ≠ j →
  cty_open i x (cty_open j y τ) =
  cty_open j y (cty_open i x τ).
Proof.
  induction τ in i, j |- *; intros Hij; cbn [cty_open].
  - rewrite qual_open_commute_fvar by congruence. reflexivity.
  - rewrite qual_open_commute_fvar by congruence. reflexivity.
  - rewrite IHτ1, IHτ2 by exact Hij. reflexivity.
  - rewrite IHτ1, IHτ2 by exact Hij. reflexivity.
  - rewrite IHτ1, IHτ2 by exact Hij. reflexivity.
  - rewrite IHτ1 by exact Hij. rewrite IHτ2 by congruence. reflexivity.
  - rewrite IHτ1 by exact Hij. rewrite IHτ2 by congruence. reflexivity.
Qed.

Lemma cty_open_commute_vars_equiv i j x y τ :
  i ≠ j →
  cty_open i x (cty_open j y τ) ≡τv
  cty_open j y (cty_open i x τ).
Proof.
  induction τ in i, j |- *; intros Hij;
    cbn [cty_vars_equiv cty_open open_one open_cty_atom_inst].
  - split; [reflexivity |].
    rewrite !qual_vars_open_atom.
    apply lvars_open_commute_fvar. congruence.
  - split; [reflexivity |].
    rewrite !qual_vars_open_atom.
    apply lvars_open_commute_fvar. congruence.
  - split; [apply IHτ1 | apply IHτ2]; exact Hij.
  - split; [apply IHτ1 | apply IHτ2]; exact Hij.
  - split; [apply IHτ1 | apply IHτ2]; exact Hij.
  - split; [apply IHτ1; exact Hij | apply IHτ2; congruence].
  - split; [apply IHτ1; exact Hij | apply IHτ2; congruence].
Qed.

#[global] Instance open_proper_cty_vars_equiv :
  OpenProper choice_ty cty_open cty_vars_equiv.
Proof.
  constructor. intros i x τ1 τ2 Hτ.
  apply cty_vars_equiv_open. exact Hτ.
Qed.

#[global] Instance open_commute_cty_vars_equiv :
  OpenCommute choice_ty cty_open cty_vars_equiv.
Proof.
  constructor. intros i j x y τ Hij.
  apply cty_open_commute_vars_equiv. exact Hij.
Qed.

#[global] Instance open_commute_cty_eq :
  OpenCommute choice_ty cty_open eq.
Proof.
  constructor. intros i j x y τ Hij.
  apply cty_open_commute_fvar. exact Hij.
Qed.

Lemma basic_choice_ty_lvar_cty_vars_equiv D τ1 τ2 :
  τ1 ≡τv τ2 →
  basic_choice_ty_lvar D τ1 →
  basic_choice_ty_lvar D τ2.
Proof.
  intros Heq Hbasic.
  revert τ2 Heq.
  induction Hbasic; intros τ' Heq; destruct τ';
    cbn [cty_vars_equiv] in Heq; try tauto.
  - destruct Heq as [-> Hφ]. constructor.
    unfold basic_qualifier_lvar_body in *.
    rewrite <- Hφ. exact H.
  - destruct Heq as [-> Hφ]. constructor.
    unfold basic_qualifier_lvar_body in *.
    rewrite <- Hφ. exact H.
  - destruct Heq as [H1 H2]. constructor; eauto.
  - destruct Heq as [H1 H2]. constructor; eauto.
  - destruct Heq as [H1 H2]. constructor; eauto.
  - destruct Heq as [H1 H2]. constructor; eauto.
  - destruct Heq as [H1 H2]. constructor; eauto.
Qed.

Lemma open_cty_env_cty_vars_equiv η τ1 τ2 :
  τ1 ≡τv τ2 →
  open_cty_env η τ1 ≡τv open_cty_env η τ2.
Proof.
  unfold open_cty_env.
  revert τ1 τ2.
  refine (fin_maps.map_fold_ind
    (fun η => ∀ τ1 τ2,
      τ1 ≡τv τ2 →
      map_fold (fun (k : nat) (x : atom) (acc : choice_ty) =>
        cty_open k x acc) τ1 η ≡τv
      map_fold (fun (k : nat) (x : atom) (acc : choice_ty) =>
        cty_open k x acc) τ2 η) _ _ η).
  - intros τ1 τ2 Hτ. exact Hτ.
  - intros k x η' Hfresh Hfold IH τ1 τ2 Hτ.
    rewrite !Hfold.
    apply cty_vars_equiv_open. apply IH. exact Hτ.
Qed.

Lemma open_cty_env_open_fresh_vars_equiv η k x τ :
  η !! k = None →
  open_cty_env η (cty_open k x τ) ≡τv
  cty_open k x (open_cty_env η τ).
Proof.
  unfold open_cty_env.
  revert τ k x.
  refine (fin_maps.map_fold_ind
    (fun η => ∀ τ k x,
      η !! k = None →
      map_fold (fun (j : nat) (y : atom) (acc : choice_ty) =>
        cty_open j y acc) (cty_open k x τ) η ≡τv
      cty_open k x
        (map_fold (fun (j : nat) (y : atom) (acc : choice_ty) =>
          cty_open j y acc) τ η)) _ _ η).
  - intros τ k x _. reflexivity.
  - intros j y η' Hfresh Hfold IH τ k x Hη.
    rewrite !Hfold.
    assert (Hjk : j ≠ k).
    {
      intros ->. rewrite lookup_insert in Hη.
      destruct (decide (k = k)) as [_|Hbad]; [discriminate|congruence].
    }
    assert (Hη' : η' !! k = None).
    {
      rewrite lookup_insert_ne in Hη by congruence.
      exact Hη.
    }
    transitivity (cty_open j y
      (cty_open k x
        (map_fold (fun (j0 : nat) (y0 : atom) (acc : choice_ty) =>
          cty_open j0 y0 acc) τ η'))).
    + apply cty_vars_equiv_open. apply IH. exact Hη'.
    + apply cty_open_commute_vars_equiv. exact Hjk.
Qed.

Lemma open_cty_env_open_fresh η k x τ :
  η !! k = None →
  open_cty_env η (cty_open k x τ) =
  cty_open k x (open_cty_env η τ).
Proof.
  unfold open_cty_env.
  revert τ k x.
  refine (fin_maps.map_fold_ind
    (fun η => ∀ τ k x,
      η !! k = None →
      map_fold (fun (j : nat) (y : atom) (acc : choice_ty) =>
        cty_open j y acc) (cty_open k x τ) η =
      cty_open k x
        (map_fold (fun (j : nat) (y : atom) (acc : choice_ty) =>
          cty_open j y acc) τ η)) _ _ η).
  - intros τ k x _. rewrite !map_fold_empty. reflexivity.
  - intros j y η' Hfresh Hfold IH τ k x Hη.
    rewrite !Hfold.
    assert (Hjk : j ≠ k).
    {
      intros ->. rewrite lookup_insert in Hη.
      destruct (decide (k = k)) as [_|Hbad]; [discriminate|congruence].
    }
    assert (Hη' : η' !! k = None).
    {
      rewrite lookup_insert_ne in Hη by congruence.
      exact Hη.
    }
    rewrite IH by exact Hη'.
    apply cty_open_commute_fvar. exact Hjk.
Qed.

Lemma open_cty_env_insert_fresh_vars_equiv η k x τ :
  η !! k = None →
  open_cty_env (<[k := x]> η) τ ≡τv
  cty_open k x (open_cty_env η τ).
Proof.
  intros Hfresh.
  unfold open_cty_env.
  apply (open_map_fold_insert_fresh_rel cty_vars_equiv cty_open).
  exact Hfresh.
Qed.

Lemma open_cty_env_insert_fresh η k x τ :
  η !! k = None →
  open_cty_env (<[k := x]> η) τ =
  cty_open k x (open_cty_env η τ).
Proof.
  intros Hfresh.
  unfold open_cty_env.
  apply (open_map_fold_insert_fresh_eq cty_open).
  exact Hfresh.
Qed.

Lemma open_cty_env_open_one_vars_equiv η k x τ :
  open_cty_env η (cty_open k x τ) ≡τv
  open_cty_env (<[k := x]> η) τ.
Proof.
  destruct (η !! k) as [y|] eqn:Hηk.
  - rewrite <-(insert_delete_id η k y Hηk) at 1.
    transitivity (cty_open k y
      (open_cty_env (delete k η) (cty_open k x τ))).
    { apply open_cty_env_insert_fresh_vars_equiv. apply lookup_delete_eq. }
    transitivity (cty_open k y
      (cty_open k x (open_cty_env (delete k η) τ))).
    { apply cty_vars_equiv_open.
      apply open_cty_env_open_fresh_vars_equiv. apply lookup_delete_eq. }
    rewrite cty_open_same_index_absorb.
    replace (<[k:=x]> η) with (<[k:=x]> (delete k η)).
    2:{ apply insert_delete_eq. }
    symmetry. apply open_cty_env_insert_fresh_vars_equiv.
    apply lookup_delete_eq.
  - transitivity (cty_open k x (open_cty_env η τ)).
    + apply open_cty_env_open_fresh_vars_equiv. exact Hηk.
    + symmetry. apply open_cty_env_insert_fresh_vars_equiv. exact Hηk.
Qed.

Lemma open_cty_env_open_one η k x τ :
  open_cty_env η (cty_open k x τ) =
  open_cty_env (<[k := x]> η) τ.
Proof.
  destruct (η !! k) as [y|] eqn:Hηk.
  - rewrite <-(insert_delete_id η k y Hηk) at 1.
    rewrite open_cty_env_insert_fresh by apply lookup_delete_eq.
    rewrite open_cty_env_open_fresh by apply lookup_delete_eq.
    rewrite cty_open_same_index_absorb.
    replace (<[k:=x]> η) with (<[k:=x]> (delete k η)).
    2:{ apply insert_delete_eq. }
    symmetry. apply open_cty_env_insert_fresh.
    apply lookup_delete_eq.
  - rewrite open_cty_env_open_fresh by exact Hηk.
    symmetry. apply open_cty_env_insert_fresh. exact Hηk.
Qed.

Lemma open_cty_env_inter η τ1 τ2 :
  open_cty_env η (CTInter τ1 τ2) =
  CTInter (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => cty_open k x acc) (CTInter τ1 τ2) η =
      CTInter
        (map_fold (fun k x acc => cty_open k x acc) τ1 η)
        (map_fold (fun k x acc => cty_open k x acc) τ2 η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold, IH.
    cbn [cty_open].
    rewrite (Hfold choice_ty (fun k x acc => cty_open k x acc) τ1 x).
    rewrite (Hfold choice_ty (fun k x acc => cty_open k x acc) τ2 x).
    reflexivity.
Qed.

Lemma open_cty_env_union η τ1 τ2 :
  open_cty_env η (CTUnion τ1 τ2) =
  CTUnion (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => cty_open k x acc) (CTUnion τ1 τ2) η =
      CTUnion
        (map_fold (fun k x acc => cty_open k x acc) τ1 η)
        (map_fold (fun k x acc => cty_open k x acc) τ2 η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold, IH.
    cbn [cty_open].
    rewrite (Hfold choice_ty (fun k x acc => cty_open k x acc) τ1 x).
    rewrite (Hfold choice_ty (fun k x acc => cty_open k x acc) τ2 x).
    reflexivity.
Qed.

Lemma open_cty_env_sum η τ1 τ2 :
  open_cty_env η (CTSum τ1 τ2) =
  CTSum (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => cty_open k x acc) (CTSum τ1 τ2) η =
      CTSum
        (map_fold (fun k x acc => cty_open k x acc) τ1 η)
        (map_fold (fun k x acc => cty_open k x acc) τ2 η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold, IH.
    cbn [cty_open].
    rewrite (Hfold choice_ty (fun k x acc => cty_open k x acc) τ1 x).
    rewrite (Hfold choice_ty (fun k x acc => cty_open k x acc) τ2 x).
    reflexivity.
Qed.

Lemma open_cty_env_arrow η τx τ :
  open_cty_env η (CTArrow τx τ) =
  CTArrow (open_cty_env η τx) (open_cty_env (open_env_lift η) τ).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => cty_open k x acc) (CTArrow τx τ) η =
      CTArrow
        (map_fold (fun k x acc => cty_open k x acc) τx η)
        (map_fold (fun k x acc => cty_open k x acc) τ
          (open_env_lift η))) _ _ η).
  - rewrite open_env_lift_empty, !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold, IH.
    cbn [cty_open].
    rewrite open_env_lift_insert.
    rewrite (Hfold choice_ty (fun k x acc => cty_open k x acc) τx x).
    change (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τ
      (<[S k:=x]> (open_env_lift η'))) with
      (open_cty_env (<[S k:=x]> (open_env_lift η')) τ).
    rewrite open_cty_env_insert_fresh by
      (apply open_env_lift_lookup_none; exact Hfresh).
    reflexivity.
Qed.

Lemma open_cty_env_wand η τx τ :
  open_cty_env η (CTWand τx τ) =
  CTWand (open_cty_env η τx) (open_cty_env (open_env_lift η) τ).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => cty_open k x acc) (CTWand τx τ) η =
      CTWand
        (map_fold (fun k x acc => cty_open k x acc) τx η)
        (map_fold (fun k x acc => cty_open k x acc) τ
          (open_env_lift η))) _ _ η).
  - rewrite open_env_lift_empty, !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold, IH.
    cbn [cty_open].
    rewrite open_env_lift_insert.
    rewrite (Hfold choice_ty (fun k x acc => cty_open k x acc) τx x).
    change (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τ
      (<[S k:=x]> (open_env_lift η'))) with
      (open_cty_env (<[S k:=x]> (open_env_lift η')) τ).
    rewrite open_cty_env_insert_fresh by
      (apply open_env_lift_lookup_none; exact Hfresh).
    reflexivity.
Qed.

Lemma open_cty_env_over η b φ :
  open_cty_env η (CTOver b φ) =
  CTOver b (qual_open_env (open_env_lift η) φ).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => cty_open k x acc) (CTOver b φ) η =
      CTOver b (qual_open_env (open_env_lift η) φ)) _ _ η).
  - rewrite open_env_lift_empty, map_fold_empty, qual_open_env_empty.
    reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold, IH.
    cbn [cty_open].
    rewrite open_env_lift_insert.
    rewrite qual_open_env_insert_fresh by
      (apply open_env_lift_lookup_none; exact Hfresh).
    reflexivity.
Qed.

Lemma open_cty_env_under η b φ :
  open_cty_env η (CTUnder b φ) =
  CTUnder b (qual_open_env (open_env_lift η) φ).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => cty_open k x acc) (CTUnder b φ) η =
      CTUnder b (qual_open_env (open_env_lift η) φ)) _ _ η).
  - rewrite open_env_lift_empty, map_fold_empty, qual_open_env_empty.
    reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold, IH.
    cbn [cty_open].
    rewrite open_env_lift_insert.
    rewrite qual_open_env_insert_fresh by
      (apply open_env_lift_lookup_none; exact Hfresh).
    reflexivity.
Qed.

Lemma open_cty_env_preserves_erasure η τ :
  erase_ty (open_cty_env η τ) = erase_ty τ.
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      erase_ty
        (map_fold (fun k x acc => cty_open k x acc) τ η) =
      erase_ty τ) _ _ η).
  - rewrite map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold.
    rewrite cty_open_preserves_erasure. exact IH.
Qed.

Lemma open_cty_env_inter_vars_equiv η τ1 τ2 :
  open_cty_env η (CTInter τ1 τ2) ≡τv
  CTInter (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => cty_open k x acc) (CTInter τ1 τ2) η ≡τv
      CTInter
        (map_fold (fun k x acc => cty_open k x acc) τ1 η)
        (map_fold (fun k x acc => cty_open k x acc) τ2 η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold.
    transitivity (cty_open k x
      (CTInter
        (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τ1 η')
        (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τ2 η'))).
    { apply cty_vars_equiv_open. exact IH. }
    cbn [cty_open cty_vars_equiv].
    split; symmetry; apply open_cty_env_insert_fresh_vars_equiv; exact Hfresh.
Qed.

Lemma open_cty_env_union_vars_equiv η τ1 τ2 :
  open_cty_env η (CTUnion τ1 τ2) ≡τv
  CTUnion (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => cty_open k x acc) (CTUnion τ1 τ2) η ≡τv
      CTUnion
        (map_fold (fun k x acc => cty_open k x acc) τ1 η)
        (map_fold (fun k x acc => cty_open k x acc) τ2 η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold.
    transitivity (cty_open k x
      (CTUnion
        (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τ1 η')
        (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τ2 η'))).
    { apply cty_vars_equiv_open. exact IH. }
    cbn [cty_open cty_vars_equiv].
    split; symmetry; apply open_cty_env_insert_fresh_vars_equiv; exact Hfresh.
Qed.

Lemma open_cty_env_sum_vars_equiv η τ1 τ2 :
  open_cty_env η (CTSum τ1 τ2) ≡τv
  CTSum (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => cty_open k x acc) (CTSum τ1 τ2) η ≡τv
      CTSum
        (map_fold (fun k x acc => cty_open k x acc) τ1 η)
        (map_fold (fun k x acc => cty_open k x acc) τ2 η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold.
    transitivity (cty_open k x
      (CTSum
        (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τ1 η')
        (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τ2 η'))).
    { apply cty_vars_equiv_open. exact IH. }
    cbn [cty_open cty_vars_equiv].
    split; symmetry; apply open_cty_env_insert_fresh_vars_equiv; exact Hfresh.
Qed.

Lemma open_cty_env_arrow_vars_equiv η τx τ :
  open_cty_env η (CTArrow τx τ) ≡τv
  CTArrow (open_cty_env η τx) (open_cty_env (open_env_lift η) τ).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => cty_open k x acc) (CTArrow τx τ) η ≡τv
      CTArrow
        (map_fold (fun k x acc => cty_open k x acc) τx η)
        (map_fold (fun k x acc => cty_open k x acc) τ (open_env_lift η))) _ _ η).
  - rewrite open_env_lift_empty, !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold.
    transitivity (cty_open k x
      (CTArrow
        (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τx η')
        (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τ
          (open_env_lift η')))).
    { apply cty_vars_equiv_open. exact IH. }
    cbn [cty_open cty_vars_equiv].
    rewrite open_env_lift_insert.
    split.
    + symmetry. apply open_cty_env_insert_fresh_vars_equiv. exact Hfresh.
    + symmetry. apply open_cty_env_insert_fresh_vars_equiv.
      apply open_env_lift_lookup_none. exact Hfresh.
Qed.

Lemma open_cty_env_wand_vars_equiv η τx τ :
  open_cty_env η (CTWand τx τ) ≡τv
  CTWand (open_cty_env η τx) (open_cty_env (open_env_lift η) τ).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => cty_open k x acc) (CTWand τx τ) η ≡τv
      CTWand
        (map_fold (fun k x acc => cty_open k x acc) τx η)
        (map_fold (fun k x acc => cty_open k x acc) τ (open_env_lift η))) _ _ η).
  - rewrite open_env_lift_empty, !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold.
    transitivity (cty_open k x
      (CTWand
        (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τx η')
        (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τ
          (open_env_lift η')))).
    { apply cty_vars_equiv_open. exact IH. }
    cbn [cty_open cty_vars_equiv].
    rewrite open_env_lift_insert.
    split.
    + symmetry. apply open_cty_env_insert_fresh_vars_equiv. exact Hfresh.
    + symmetry. apply open_cty_env_insert_fresh_vars_equiv.
      apply open_env_lift_lookup_none. exact Hfresh.
Qed.

Definition qual_with_vars (D : lvset) : type_qualifier :=
  qual D (fun _ _ _ => True).

Lemma open_cty_env_over_vars_equiv η b φ :
  open_cty_env η (CTOver b φ) ≡τv
  CTOver b (qual_with_vars (lvars_open_env (open_env_lift η) (qual_vars φ))).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => cty_open k x acc) (CTOver b φ) η ≡τv
      CTOver b
        (qual_with_vars
          (lvars_open_env (open_env_lift η) (qual_vars φ)))) _ _ η).
  - rewrite open_env_lift_empty. unfold lvars_open_env. rewrite !map_fold_empty.
    destruct φ as [D p]. cbn [cty_vars_equiv qual_with_vars qual_vars].
    split; reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold.
    transitivity (cty_open k x
      (CTOver b
        (qual_with_vars
          (lvars_open_env (open_env_lift η') (qual_vars φ))))).
    { apply cty_vars_equiv_open. exact IH. }
    cbn [cty_open cty_vars_equiv].
    split; [reflexivity|].
    rewrite qual_vars_open_atom.
    rewrite open_env_lift_insert.
    symmetry. apply lvars_open_env_insert_fresh.
    apply open_env_lift_lookup_none. exact Hfresh.
Qed.

Lemma open_cty_env_under_vars_equiv η b φ :
  open_cty_env η (CTUnder b φ) ≡τv
  CTUnder b (qual_with_vars (lvars_open_env (open_env_lift η) (qual_vars φ))).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => cty_open k x acc) (CTUnder b φ) η ≡τv
      CTUnder b
        (qual_with_vars
          (lvars_open_env (open_env_lift η) (qual_vars φ)))) _ _ η).
  - rewrite open_env_lift_empty. unfold lvars_open_env. rewrite !map_fold_empty.
    destruct φ as [D p]. cbn [cty_vars_equiv qual_with_vars qual_vars].
    split; reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold.
    transitivity (cty_open k x
      (CTUnder b
        (qual_with_vars
          (lvars_open_env (open_env_lift η') (qual_vars φ))))).
    { apply cty_vars_equiv_open. exact IH. }
    cbn [cty_open cty_vars_equiv].
    split; [reflexivity|].
    rewrite qual_vars_open_atom.
    rewrite open_env_lift_insert.
    symmetry. apply lvars_open_env_insert_fresh.
    apply open_env_lift_lookup_none. exact Hfresh.
Qed.

Lemma logic_var_open_shift_from_under j k x v :
  j <= k →
  logic_var_open (S (S k)) x (logic_var_shift_from (S j) v) =
  logic_var_shift_from (S j) (logic_var_open (S k) x v).
Proof.
  intros Hjk.
  destruct v as [n|y]; cbn [logic_var_open logic_var_shift_from].
  - repeat (destruct (decide _) as [?|?]; subst;
      cbn [logic_var_open logic_var_shift_from] in *; try lia; try reflexivity).
  - reflexivity.
Qed.

Lemma lvars_open_shift_from_under j k x D :
  j <= k →
  lvars_open (S (S k)) x (lvars_shift_from (S j) D) =
  lvars_shift_from (S j) (lvars_open (S k) x D).
Proof.
  intros Hjk.
  induction D as [|v D Hfresh IH] using set_ind_L.
  - unfold lvars_open, lvars_shift_from.
    rewrite !set_map_empty. reflexivity.
  - unfold lvars_open, lvars_shift_from in *.
    rewrite !set_map_union_L, !set_map_singleton_L.
    rewrite IH.
    rewrite logic_var_open_shift_from_under by exact Hjk.
    reflexivity.
Qed.

Lemma logic_var_shift_from_inj k : Inj (=) (=) (logic_var_shift_from k).
Proof.
  intros v1 v2 Hv.
  destruct v1 as [n1|x1], v2 as [n2|x2];
    cbn [logic_var_shift_from] in Hv.
  - destruct (decide (k <= n1)) as [Hn1|Hn1];
      destruct (decide (k <= n2)) as [Hn2|Hn2].
    + inversion Hv. subst. reflexivity.
    + inversion Hv. subst. exfalso. lia.
    + inversion Hv. subst. exfalso. lia.
    + inversion Hv. subst. reflexivity.
  - destruct (decide (k <= n1)); inversion Hv.
  - destruct (decide (k <= n2)); inversion Hv.
  - inversion Hv. subst. reflexivity.
Qed.

Lemma lvars_fv_shift_from k D :
  lvars_fv (lvars_shift_from k D) = lvars_fv D.
Proof.
  induction D as [|v D Hfresh IH] using set_ind_L.
  - unfold lvars_shift_from. rewrite set_map_empty. reflexivity.
  - unfold lvars_shift_from in *.
    rewrite set_map_union_L, set_map_singleton_L.
    rewrite !lvars_fv_union, IH.
    destruct v as [n|x]; cbn [shift_at shift_logic_var_inst logic_var_shift_from].
    + destruct (decide (k <= n));
        rewrite !lvars_fv_singleton_bound; reflexivity.
    + rewrite !lvars_fv_singleton_free. reflexivity.
Qed.

Lemma lvars_bv_shift_from_under_iff j k D :
  j <= k →
  S (S k) ∈ lvars_bv (lvars_shift_from (S j) D) ↔
  S k ∈ lvars_bv D.
Proof.
  intros Hjk.
  rewrite !lvars_bv_elem.
  unfold lvars_shift_from.
  rewrite elem_of_map.
  split.
  - intros [v [Hv HvD]].
    destruct v as [n|y]; cbn [shift_at shift_logic_var_inst
      logic_var_shift_from] in Hv; try discriminate.
    destruct (decide (S j <= n)) as [Hjn|Hjn].
    + inversion Hv. subst n. exact HvD.
    + inversion Hv. subst n. lia.
  - intros HvD.
    exists (LVBound (S k)). split.
    + cbn [shift_at shift_logic_var_inst logic_var_shift_from].
      destruct (decide (S j <= S k)) as [_|Hbad]; [reflexivity|lia].
    + exact HvD.
Qed.

Lemma beta_drop_shift_from_insert_under j k β v :
  j <= k →
  beta_drop_shift_from (S j) (<[S (S k):=v]> β) =
  <[S k:=v]> (beta_drop_shift_from (S j) β).
Proof.
  intros Hjk.
  apply map_eq. intros n.
  rewrite beta_drop_shift_from_lookup.
  destruct (decide (n < S j)) as [Hn|Hn].
  - rewrite lookup_insert_ne by lia.
    rewrite lookup_insert_ne by lia.
    rewrite beta_drop_shift_from_lookup.
    destruct (decide (n < S j)) as [_|Hbad]; [reflexivity|lia].
  - destruct (decide (n = S k)) as [->|Hne].
    + rewrite lookup_insert_eq.
      rewrite lookup_insert_eq. reflexivity.
    + rewrite lookup_insert_ne by lia.
      rewrite lookup_insert_ne by (intros Heq; apply Hne; symmetry; exact Heq).
      rewrite beta_drop_shift_from_lookup.
      destruct (decide (n < S j)) as [Hbad|_]; [lia|reflexivity].
Qed.

Lemma qual_open_shift_under_equiv j k x φ :
  j <= k →
  qual_open_atom (S (S k)) x (qual_shift_from (S j) φ) =
  qual_shift_from (S j) (qual_open_atom (S k) x φ).
Proof.
  intros Hjk.
  destruct φ as [D p].
  cbn [qual_shift_from qual_open_atom qual_bvars qual_prop shift_at
    shift_lvars_inst].
  change (shift_at (S j) D) with (lvars_shift_from (S j) D).
  change (shift_at (S j) (lvars_open (S k) x D))
    with (lvars_shift_from (S j) (lvars_open (S k) x D)).
  destruct (decide (S (S k) ∈ lvars_bv (lvars_shift_from (S j) D)))
    as [Hshift|Hshift];
    destruct (decide (S k ∈ lvars_bv D)) as [Horig|Horig].
  - assert (HD :
      lvars_open (S (S k)) x (lvars_shift_from (S j) D) =
      lvars_shift_from (S j) (lvars_open (S k) x D)).
    { apply lvars_open_shift_from_under. exact Hjk. }
    rewrite HD. cbn [qual_shift_from shift_qual_inst]. f_equal.
    repeat (apply functional_extensionality; intro).
    apply propositional_extensionality. split.
    + intros (v & Hv & Hp). exists v. split; [exact Hv|].
      rewrite beta_drop_shift_from_insert_under in Hp.
      rewrite !lvars_fv_shift_from in Hp.
      exact Hp. exact Hjk.
    + intros (v & Hv & Hp). exists v. split; [exact Hv|].
      rewrite !lvars_fv_shift_from.
      rewrite beta_drop_shift_from_insert_under. exact Hp. exact Hjk.
  - exfalso. apply Horig.
    apply lvars_bv_shift_from_under_iff in Hshift; [exact Hshift|exact Hjk].
  - exfalso. apply Hshift.
    apply lvars_bv_shift_from_under_iff; [exact Hjk|exact Horig].
  - reflexivity.
Qed.

Lemma cty_open_shift_under_from j k x τ :
  j <= k →
  cty_open (S k) x (cty_shift j τ) =
  cty_shift j (cty_open k x τ).
Proof.
  induction τ in j, k |- *; intros Hjk;
    cbn [cty_open cty_shift].
  - rewrite qual_open_shift_under_equiv by lia. reflexivity.
  - rewrite qual_open_shift_under_equiv by lia. reflexivity.
  - rewrite IHτ1, IHτ2 by lia. reflexivity.
  - rewrite IHτ1, IHτ2 by lia. reflexivity.
  - rewrite IHτ1, IHτ2 by lia. reflexivity.
  - rewrite IHτ1, IHτ2 by lia. reflexivity.
  - rewrite IHτ1, IHτ2 by lia. reflexivity.
Qed.

Lemma cty_open_shift_under_equiv k x τ :
  cty_open (S k) x (cty_shift 0 τ) =
  cty_shift 0 (cty_open k x τ).
Proof. apply cty_open_shift_under_from. lia. Qed.

Lemma cty_open_shift_under_vars_equiv k x τ :
  cty_open (S k) x (cty_shift 0 τ) ≡τv
  cty_shift 0 (cty_open k x τ).
Proof.
  rewrite cty_open_shift_under_equiv. reflexivity.
Qed.

Lemma open_cty_env_lift_shift0_vars_equiv η τ :
  open_cty_env (open_env_lift η) (cty_shift 0 τ) ≡τv
  cty_shift 0 (open_cty_env η τ).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => cty_open k x acc)
        (cty_shift 0 τ) (open_env_lift η) ≡τv
      cty_shift 0
        (map_fold (fun k x acc => cty_open k x acc) τ η)) _ _ η).
  - rewrite open_env_lift_empty, !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite open_env_lift_insert.
    change (map_fold (fun k0 x0 acc => cty_open k0 x0 acc)
      (cty_shift 0 τ) (<[S k:=x]> (open_env_lift η')))
      with (open_cty_env (<[S k := x]> (open_env_lift η'))
        (cty_shift 0 τ)).
    transitivity
      (cty_open (S k) x
        (open_cty_env (open_env_lift η') (cty_shift 0 τ))).
    { apply open_cty_env_insert_fresh_vars_equiv.
      apply open_env_lift_lookup_none. exact Hfresh. }
    change (open_cty_env (open_env_lift η') (cty_shift 0 τ))
      with (map_fold (fun k0 x0 acc => cty_open k0 x0 acc)
        (cty_shift 0 τ) (open_env_lift η')).
    transitivity
      (cty_open (S k) x
        (cty_shift 0
          (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τ η'))).
    { apply cty_vars_equiv_open. exact IH. }
    transitivity
      (cty_shift 0
        (cty_open k x
          (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τ η'))).
    { apply cty_open_shift_under_vars_equiv. }
    apply cty_vars_equiv_shift_from.
    symmetry. apply open_cty_env_insert_fresh_vars_equiv. exact Hfresh.
Qed.

Lemma lvars_at_depth_elem d D u :
  u ∈ lvars_at_depth d D ↔
  ∃ v, v ∈ D ∧ logic_var_at_depth d v = Some u.
Proof.
  unfold lvars_at_depth.
  refine (set_fold_ind_L
    (fun acc D => ∀ u, u ∈ acc ↔
      ∃ v, v ∈ D ∧ logic_var_at_depth d v = Some u)
    (fun v acc =>
      match logic_var_at_depth d v with
      | Some u => {[u]} ∪ acc
      | None => acc
      end) ∅ _ _ D u).
  - intros y. set_solver.
  - intros v D' acc Hfresh IH z.
    destruct (logic_var_at_depth d v) as [a|] eqn:Hv.
    + pose proof (IH z) as Hz. split.
      * intros Hx.
        apply elem_of_union in Hx as [Hx|Hx].
        -- apply elem_of_singleton in Hx. subst z.
           exists v. split; [set_solver | exact Hv].
        -- apply Hz in Hx as [w [Hw Hwx]].
           exists w. split; [set_solver | exact Hwx].
      * intros [w [Hw Hwx]].
        apply elem_of_union.
        apply elem_of_union in Hw as [Hw|Hw].
        -- apply elem_of_singleton in Hw. subst w.
           rewrite Hv in Hwx. inversion Hwx. subst z.
           left. set_solver.
        -- right. apply Hz. exists w. split; [exact Hw | exact Hwx].
    + pose proof (IH z) as Hz. split.
      * intros Hx.
        apply Hz in Hx as [w [Hw Hwx]].
        exists w. split; [set_solver | exact Hwx].
      * intros [w [Hw Hwx]].
        apply elem_of_union in Hw as [Hw|Hw].
        -- apply elem_of_singleton in Hw. subst w.
           rewrite Hv in Hwx. discriminate.
        -- apply Hz. exists w. split; [exact Hw | exact Hwx].
Qed.

Lemma logic_var_at_depth_open d k x v :
  logic_var_at_depth d (logic_var_open (d + k) x v) =
  option_map (logic_var_open k x) (logic_var_at_depth d v).
Proof.
  destruct v as [n|y]; cbn [logic_var_open logic_var_at_depth].
  - destruct (decide (n = d + k)) as [->|Hne].
    + destruct (decide (d <= d + k)) as [_|Hbad]; [|lia].
      replace (d + k - d) with k by lia.
      cbn [option_map logic_var_open].
      destruct (decide (k = k)) as [_|Hbad]; [reflexivity | congruence].
    + destruct (decide (d <= n)) as [Hdn|Hdn].
      * cbn [logic_var_at_depth].
        destruct (decide (d <= n)) as [_|Hbad]; [|lia].
        cbn [option_map logic_var_open].
        destruct (decide (n - d = k)) as [Hnk|_]; [lia | reflexivity].
      * cbn [logic_var_at_depth].
        destruct (decide (d <= n)) as [Hbad|_]; [lia | reflexivity].
  - cbn [option_map logic_var_open]. reflexivity.
Qed.

Lemma lvars_at_depth_open d k x D :
  lvars_at_depth d (lvars_open (d + k) x D) =
  lvars_open k x (lvars_at_depth d D).
Proof.
  apply set_eq. intros u.
  split.
  - intros Hu.
    apply lvars_at_depth_elem in Hu as [v [Hv Hvu]].
    unfold lvars_open in Hv.
    apply elem_of_map in Hv as [w [-> Hw]].
    rewrite logic_var_at_depth_open in Hvu.
    destruct (logic_var_at_depth d w) as [w'|] eqn:Hw'; [|discriminate].
    inversion Hvu. subst u.
    unfold lvars_open.
    apply elem_of_map.
    exists w'. split; [reflexivity |].
    rewrite lvars_at_depth_elem. exists w. split; [exact Hw | exact Hw'].
  - intros Hu.
    unfold lvars_open in Hu.
    apply elem_of_map in Hu as [v [-> Hv]].
    apply lvars_at_depth_elem in Hv as [w [Hw Hwv]].
    rewrite lvars_at_depth_elem.
    exists (logic_var_open (d + k) x w). split.
    + unfold lvars_open. apply elem_of_map. eauto.
    + rewrite logic_var_at_depth_open, Hwv. reflexivity.
Qed.


Lemma value_tm_lvars_at_open :
  (∀ v d k x,
    value_lvars_at d ({d + k ~> x} v) =
    lvars_open k x (value_lvars_at d v)) *
  (∀ e d k x,
    tm_lvars_at d ({d + k ~> x} e) =
    lvars_open k x (tm_lvars_at d e)).
Proof.
  apply value_tm_mutind; cbn [open_one open_value_atom_inst open_tm_atom_inst].
  - intros c d k x. reflexivity.
  - intros y d k x.
    cbn [open_value value_lvars_at].
    unfold lvars_open. rewrite set_map_singleton_L. reflexivity.
  - intros n d k x. cbn [open_value value_lvars_at].
    destruct (decide (d + k = n)) as [Heq|Hne].
    subst n.
    + cbn [open_one open_value_atom_inst open_value value_lvars_at logic_var_at_depth].
      destruct (decide (d + k = d + k)) as [_|Hbad]; [|congruence].
      cbn [value_lvars_at logic_var_at_depth].
      destruct (decide (d <= d + k)) as [_|Hbad]; [|lia].
      unfold lvars_open. rewrite set_map_singleton_L.
      replace (d + k - d) with k by lia.
      cbn [logic_var_open].
      destruct (decide (k = k)) as [_|Hbad]; [reflexivity | congruence].
    + cbn [open_one open_value_atom_inst open_value value_lvars_at logic_var_at_depth].
      destruct (decide (d + k = n)) as [Heq|_]; [congruence |].
      cbn [value_lvars_at logic_var_at_depth].
      destruct (decide (d <= n)) as [Hdn|Hdn].
      * unfold lvars_open. rewrite set_map_singleton_L.
        cbn [logic_var_open].
        destruct (decide (n - d = k)) as [Hnk|_]; [lia | reflexivity].
      * unfold lvars_open. rewrite set_map_empty. reflexivity.
  - intros s e IHe d k x.
    cbn [open_one open_value_atom_inst open_value value_lvars_at].
    replace (S (d + k)) with (S d + k) by lia.
    apply IHe.
  - intros Tf vf IHvf d k x.
    cbn [open_one open_value_atom_inst open_value value_lvars_at].
    replace (S (d + k)) with (S d + k) by lia.
    apply IHvf.
  - intros v IHv d k x.
    cbn [open_one open_tm_atom_inst open_tm tm_lvars_at].
    apply IHv.
  - intros e1 IHe1 e2 IHe2 d k x.
    cbn [open_one open_tm_atom_inst open_tm tm_lvars_at].
    rewrite IHe1.
    replace (S (d + k)) with (S d + k) by lia.
    replace (tm_lvars_at (S d) (open_tm (S d + k) (vfvar x) e2))
      with (lvars_open k x (tm_lvars_at (S d) e2))
      by (change (open_tm (S d + k) (vfvar x) e2) with ({S d + k ~> x} e2);
          symmetry; apply IHe2).
    unfold lvars_open. rewrite set_map_union_L. reflexivity.
  - intros op arg IHarg d k x.
    cbn [open_one open_tm_atom_inst open_tm tm_lvars_at].
    apply IHarg.
  - intros v1 IHv1 v2 IHv2 d k x.
    cbn [open_one open_tm_atom_inst open_tm tm_lvars_at].
    replace (value_lvars_at d (open_value (d + k) (vfvar x) v1))
      with (lvars_open k x (value_lvars_at d v1))
      by (change (open_value (d + k) (vfvar x) v1) with ({d + k ~> x} v1);
          symmetry; apply IHv1).
    replace (value_lvars_at d (open_value (d + k) (vfvar x) v2))
      with (lvars_open k x (value_lvars_at d v2))
      by (change (open_value (d + k) (vfvar x) v2) with ({d + k ~> x} v2);
          symmetry; apply IHv2).
    unfold lvars_open. rewrite set_map_union_L. reflexivity.
  - intros v IHv et IHet ef IHef d k x.
    cbn [open_one open_tm_atom_inst open_tm tm_lvars_at].
    replace (value_lvars_at d (open_value (d + k) (vfvar x) v))
      with (lvars_open k x (value_lvars_at d v))
      by (change (open_value (d + k) (vfvar x) v) with ({d + k ~> x} v);
          symmetry; apply IHv).
    replace (tm_lvars_at d ({d + k ~> x} et))
      with (lvars_open k x (tm_lvars_at d et))
      by (symmetry; apply IHet).
    replace (tm_lvars_at d ({d + k ~> x} ef))
      with (lvars_open k x (tm_lvars_at d ef))
      by (symmetry; apply IHef).
    unfold lvars_open. rewrite !set_map_union_L. reflexivity.
Qed.

Lemma value_lvars_at_open d k x v :
  value_lvars_at d ({d + k ~> x} v) =
  lvars_open k x (value_lvars_at d v).
Proof. exact (fst value_tm_lvars_at_open v d k x). Qed.

Lemma tm_lvars_at_open d k x e :
  tm_lvars_at d ({d + k ~> x} e) =
  lvars_open k x (tm_lvars_at d e).
Proof. exact (snd value_tm_lvars_at_open e d k x). Qed.

Lemma tm_lvars_open k x e :
  tm_lvars ({k ~> x} e) = lvars_open k x (tm_lvars e).
Proof.
  unfold tm_lvars.
  replace k with (0 + k) at 1 by lia.
  apply tm_lvars_at_open.
Qed.

Lemma tm_lvars_open_env η e :
  tm_lvars (open_tm_env η e) = lvars_open_env η (tm_lvars e).
Proof.
  unfold open_tm_env, lvars_open_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      tm_lvars
        (map_fold (fun k x acc => open_tm k (vfvar x) acc) e η) =
      map_fold (fun k x acc => lvars_open k x acc) (tm_lvars e) η)
    _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold.
    change (open_tm k (vfvar x)
      (map_fold (fun k0 x0 acc => open_tm k0 (vfvar x0) acc) e η'))
      with ({k ~> x}
        (map_fold (fun k0 x0 acc => open_tm k0 (vfvar x0) acc) e η')).
    rewrite tm_lvars_open.
    rewrite IH. reflexivity.
Qed.

Lemma choice_ty_lvars_at_open d k x τ :
  choice_ty_lvars_at d ({d + k ~> x} τ) =
  lvars_open k x (choice_ty_lvars_at d τ).
Proof.
  induction τ in d, k |- *; cbn [choice_ty_lvars_at cty_open open_one open_cty_atom_inst].
  - rewrite qual_vars_open_atom.
    replace (S (d + k)) with (S d + k) by lia.
    apply lvars_at_depth_open.
  - rewrite qual_vars_open_atom.
    replace (S (d + k)) with (S d + k) by lia.
    apply lvars_at_depth_open.
  - rewrite IHτ1, IHτ2.
    unfold lvars_open. rewrite set_map_union_L. reflexivity.
  - rewrite IHτ1, IHτ2.
    unfold lvars_open. rewrite set_map_union_L. reflexivity.
  - rewrite IHτ1, IHτ2.
    unfold lvars_open. rewrite set_map_union_L. reflexivity.
  - rewrite IHτ1.
    replace (S (d + k)) with (S d + k) by lia.
    replace (choice_ty_lvars_at (S d) ({S d + k ~> x} τ2))
      with (lvars_open k x (choice_ty_lvars_at (S d) τ2))
      by (symmetry; apply IHτ2).
    unfold lvars_open. rewrite set_map_union_L. reflexivity.
  - rewrite IHτ1.
    replace (S (d + k)) with (S d + k) by lia.
    replace (choice_ty_lvars_at (S d) ({S d + k ~> x} τ2))
      with (lvars_open k x (choice_ty_lvars_at (S d) τ2))
      by (symmetry; apply IHτ2).
    unfold lvars_open. rewrite set_map_union_L. reflexivity.
Qed.

Lemma choice_ty_lvars_open k x τ :
  choice_ty_lvars ({k ~> x} τ) = lvars_open k x (choice_ty_lvars τ).
Proof.
  unfold choice_ty_lvars.
  replace k with (0 + k) at 1 by lia.
  apply choice_ty_lvars_at_open.
Qed.

Lemma cty_open_lc k x τ :
  lc_choice_ty τ ->
  {k ~> x} τ = τ.
Proof.
  intros Hlc. apply cty_open_lc_core. exact Hlc.
Qed.

Lemma lvars_fv_lvars_at_depth d D :
  lvars_fv (lvars_at_depth d D) = lvars_fv D.
Proof.
  apply set_eq. intros x.
  rewrite !lvars_fv_elem, lvars_at_depth_elem.
  split.
  - intros [v [Hv Hdepth]].
    destruct v as [k|y]; cbn [logic_var_at_depth] in Hdepth.
    + destruct (decide (d <= k)); discriminate.
    + inversion Hdepth. subst. exact Hv.
  - intros Hx.
    exists (LVFree x). split; [exact Hx | reflexivity].
Qed.

Lemma value_tm_lvars_fv_at :
  (∀ v d, lvars_fv (value_lvars_at d v) = fv_value v) *
  (∀ e d, lvars_fv (tm_lvars_at d e) = fv_tm e).
Proof.
  apply value_tm_mutind; intros; cbn [value_lvars_at tm_lvars_at
    fv_value fv_tm].
  - reflexivity.
  - rewrite lvars_fv_singleton_free. reflexivity.
  - cbn [logic_var_at_depth].
    destruct (decide (d <= n)) as [_|_];
      rewrite ?lvars_fv_singleton_bound; reflexivity.
  - apply H.
  - apply H.
  - apply H.
  - rewrite lvars_fv_union, H, H0. reflexivity.
  - apply H.
  - rewrite lvars_fv_union, H, H0. reflexivity.
  - rewrite !lvars_fv_union, H, H0, H1. reflexivity.
Qed.

Lemma tm_lvars_fv e :
  lvars_fv (tm_lvars e) = fv_tm e.
Proof.
  exact (snd value_tm_lvars_fv_at e 0).
Qed.

Lemma choice_ty_lvars_fv_at d τ :
  lvars_fv (choice_ty_lvars_at d τ) = fv_cty τ.
Proof.
  induction τ in d |- *; cbn [choice_ty_lvars_at fv_cty];
    rewrite ?lvars_fv_lvars_at_depth, ?lvars_fv_union, ?IHτ1, ?IHτ2;
    try reflexivity;
    destruct φ; reflexivity.
Qed.

Lemma choice_ty_lvars_fv τ :
  lvars_fv (choice_ty_lvars τ) = fv_cty τ.
Proof.
  exact (choice_ty_lvars_fv_at 0 τ).
Qed.

Lemma lvars_shift_mono D E :
  D ⊆ E →
  lvars_shift D ⊆ lvars_shift E.
Proof.
  intros HDE u Hu.
  unfold lvars_shift in *.
  apply elem_of_map in Hu as [v [-> Hv]].
  apply elem_of_map. exists v. split; [reflexivity |].
  apply HDE. exact Hv.
Qed.

Lemma lvars_of_atoms_mono D E :
  D ⊆ E →
  lvars_of_atoms D ⊆ lvars_of_atoms E.
Proof.
  intros HDE u Hu.
  unfold lvars_of_atoms in *.
  apply elem_of_map in Hu as [x [-> Hx]].
  apply elem_of_map. exists x. split; [reflexivity |].
  apply HDE. exact Hx.
Qed.

Lemma lvars_shift_succ_body_union D1 D1' D2 D2' :
  D1 ⊆ lvars_shift D1' ∪ {[LVBound 0]} →
  D2 ⊆ lvars_shift D2' ∪ {[LVBound 0]} →
  D1 ∪ D2 ⊆ lvars_shift (D1' ∪ D2') ∪ {[LVBound 0]}.
Proof.
  intros H1 H2 u Hu.
  apply elem_of_union in Hu as [Hu | Hu].
  - specialize (H1 u Hu).
    apply elem_of_union in H1 as [Hshift | Hzero].
    + apply elem_of_union_l.
      unfold lvars_shift in *.
      apply elem_of_map in Hshift as [v [-> Hv]].
      apply elem_of_map. exists v. split; [reflexivity |].
      apply elem_of_union_l. exact Hv.
    + apply elem_of_union_r. exact Hzero.
  - specialize (H2 u Hu).
    apply elem_of_union in H2 as [Hshift | Hzero].
    + apply elem_of_union_l.
      unfold lvars_shift in *.
      apply elem_of_map in Hshift as [v [-> Hv]].
      apply elem_of_map. exists v. split; [reflexivity |].
      apply elem_of_union_r. exact Hv.
    + apply elem_of_union_r. exact Hzero.
Qed.

Lemma lvars_at_depth_succ_body d D :
  lvars_at_depth d D ⊆
    lvars_shift (lvars_at_depth (S d) D) ∪ {[LVBound 0]}.
Proof.
  intros u Hu.
  apply lvars_at_depth_elem in Hu as [v [Hv Hdepth]].
  destruct v as [n|x]; cbn [logic_var_at_depth] in Hdepth.
  - destruct (decide (d <= n)) as [Hdn|Hdn]; [|discriminate].
    inversion Hdepth; subst u.
    destruct (decide (S d <= n)) as [Hsdn|Hsdn].
    + apply elem_of_union_l.
      unfold lvars_shift. apply elem_of_map.
      exists (LVBound (n - S d)). split.
      * cbn [logic_var_shift]. f_equal. lia.
      * apply lvars_at_depth_elem.
        exists (LVBound n). split; [exact Hv |].
        cbn [logic_var_at_depth].
        destruct (decide (S d <= n)) as [_|Hbad]; [reflexivity | lia].
    + apply elem_of_union_r.
      assert (n = d) by lia. subst n.
      replace (d - d) with 0 by lia.
      apply elem_of_singleton. reflexivity.
  - inversion Hdepth; subst u.
    apply elem_of_union_l.
    unfold lvars_shift. apply elem_of_map.
    exists (LVFree x). split; [reflexivity |].
    apply lvars_at_depth_elem.
    exists (LVFree x). split; [exact Hv | reflexivity].
Qed.

Lemma choice_ty_lvars_at_succ_body d τ :
  choice_ty_lvars_at d τ ⊆
    lvars_shift (choice_ty_lvars_at (S d) τ) ∪ {[LVBound 0]}.
Proof.
  induction τ in d |- *; cbn [choice_ty_lvars_at].
  - apply lvars_at_depth_succ_body.
  - apply lvars_at_depth_succ_body.
  - apply lvars_shift_succ_body_union; [apply IHτ1 | apply IHτ2].
  - apply lvars_shift_succ_body_union; [apply IHτ1 | apply IHτ2].
  - apply lvars_shift_succ_body_union; [apply IHτ1 | apply IHτ2].
  - apply lvars_shift_succ_body_union; [apply IHτ1 | apply IHτ2].
  - apply lvars_shift_succ_body_union; [apply IHτ1 | apply IHτ2].
Qed.

Lemma choice_ty_lvars_body_subset D τ :
  choice_ty_lvars_at 1 τ ⊆ D →
  choice_ty_lvars τ ⊆ lvars_shift D ∪ {[LVBound 0]}.
Proof.
  intros HD u Hu.
  unfold choice_ty_lvars in Hu.
  pose proof (choice_ty_lvars_at_succ_body 0 τ u Hu) as Hbody.
  apply elem_of_union in Hbody as [Hshift | Hzero].
  - apply elem_of_union_l.
    pose proof (lvars_shift_mono _ _ HD u Hshift) as HuD.
    exact HuD.
  - apply elem_of_union_r. exact Hzero.
Qed.

Lemma lc_choice_ty_lvars_bv_empty τ :
  lc_choice_ty τ →
  lvars_bv (choice_ty_lvars τ) = ∅.
Proof.
  intros Hlc.
  apply set_eq. intros k. split; [|set_solver].
  intros Hk.
  pose (x := fresh_for (lvars_fv (choice_ty_lvars τ))).
  assert (Hx : x ∉ lvars_fv (choice_ty_lvars τ))
    by (subst x; apply fresh_for_not_in).
  pose proof (cty_open_lc_core τ Hlc k x) as Hopen.
  pose proof (f_equal choice_ty_lvars Hopen) as Hlvars.
  rewrite choice_ty_lvars_open in Hlvars.
  assert (Hxopen : x ∈ lvars_fv (lvars_open k x (choice_ty_lvars τ))).
  {
    rewrite lvars_fv_open.
    destruct (decide (k ∈ lvars_bv (choice_ty_lvars τ))) as [_|Hbad].
    - set_solver.
    - contradiction.
  }
  rewrite Hlvars in Hxopen.
  contradiction.
Qed.

Lemma lc_choice_ty_lvars_subset_atoms τ :
  lc_choice_ty τ →
  choice_ty_lvars τ ⊆ lvars_of_atoms (fv_cty τ).
Proof.
  intros Hlc u Hu.
  destruct u as [k|x].
  - exfalso.
    pose proof (lc_choice_ty_lvars_bv_empty _ Hlc) as Hbv.
    assert (k ∈ lvars_bv (choice_ty_lvars τ)).
    { apply lvars_bv_elem. exact Hu. }
    set_solver.
  - apply elem_of_map.
    exists x. split; [reflexivity |].
    rewrite <- choice_ty_lvars_fv.
    apply lvars_fv_elem. exact Hu.
Qed.

Lemma lvars_shift_union_free_singleton D x :
  lvars_shift (D ∪ {[LVFree x]}) =
  lvars_shift D ∪ {[LVFree x]}.
Proof.
  unfold lvars_shift, shift_at, shift_logic_var_inst,
    lvars_shift_from, logic_var_shift_from.
  rewrite set_map_union_L, set_map_singleton_L.
  reflexivity.
Qed.

Lemma tm_lvars_shift_free_fresh x e :
  x ∉ fv_tm e →
  LVFree x ∉ tm_lvars (↑[0] e).
Proof.
  intros Hfresh Hbad.
  apply Hfresh.
  rewrite <- (fv_tm_shift 0 e).
  rewrite <- tm_lvars_fv.
  apply lvars_fv_elem. exact Hbad.
Qed.

Lemma open_tret_bvar0_under k x :
  {S k ~> x} (tret (vbvar 0)) = tret (vbvar 0).
Proof.
  cbn [open_one open_tm_atom_inst open_tm open_value].
  destruct (decide (0 = S k)) as [Hbad|_]; [lia | reflexivity].
Qed.

Lemma open_tret_bvar0 x :
  {0 ~> x} (tret (vbvar 0)) = tret (vfvar x).
Proof.
  cbn [open_one open_tm_atom_inst open_tm open_value].
  destruct (decide (0 = 0)) as [_|Hbad]; [reflexivity | congruence].
Qed.

Lemma open_tapp_tm_shift_bvar0_under_lvar e k x :
  {S k ~> x} (tapp_tm (↑[0] e) (vbvar 0)) =
  tapp_tm (↑[0] ({k ~> x} e)) (vbvar 0).
Proof.
  change ({S k ~> x} (tapp_tm (↑[0] e) (vbvar 0)))
    with (open_tm (S k) (vfvar x) (tapp_tm (tm_shift 0 e) (vbvar 0))).
  change (tapp_tm (↑[0] ({k ~> x} e)) (vbvar 0))
    with (tapp_tm (tm_shift 0 (open_tm k (vfvar x) e)) (vbvar 0)).
  apply open_tapp_tm_shift_bvar0_under.
Qed.

Lemma open_tapp_shift_bvar0 e x :
  lc_tm e →
  {0 ~> x} (tapp_tm (↑[0] e) (vbvar 0)) =
    tapp_tm e (vfvar x).
Proof.
  intros Hlc.
  change ({0 ~> x} (tapp_tm (↑[0] e) (vbvar 0)))
    with (open_tm 0 (vfvar x) (tapp_tm (tm_shift 0 e) (vbvar 0))).
  rewrite open_tapp_tm_arg.
  rewrite (tm_shift_lc_id 0 e Hlc).
  rewrite (open_rec_lc_tm e Hlc 0 (vfvar x)).
  cbn [open_value].
  destruct (decide (0 = 0)) as [_|Hbad]; [reflexivity | congruence].
Qed.

Lemma open_tm_env_lift_tapp_shift_bvar0 η e :
  open_tm_env (open_env_lift η) (tapp_tm (↑[0] e) (vbvar 0)) =
  tapp_tm (↑[0] (open_tm_env η e)) (vbvar 0).
Proof.
  unfold open_tm_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      map_fold (fun k x acc => open_tm k (vfvar x) acc)
        (tapp_tm (↑[0] e) (vbvar 0)) (open_env_lift η) =
      tapp_tm
        (↑[0] (map_fold (fun k x acc => open_tm k (vfvar x) acc) e η))
        (vbvar 0)) _ _ η).
  - rewrite open_env_lift_empty, !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite open_env_lift_insert.
    change (map_fold (fun k0 x0 acc => open_tm k0 (vfvar x0) acc)
      (tapp_tm (↑[0] e) (vbvar 0))
      (<[S k:=x]> (open_env_lift η'))) with
      (open_tm_env (<[S k := x]> (open_env_lift η'))
        (tapp_tm (↑[0] e) (vbvar 0))).
    rewrite open_tm_env_insert_fresh.
    2:{ apply open_env_lift_lookup_none. exact Hfresh. }
    change (open_tm_env (open_env_lift η')
        (tapp_tm (↑[0] e) (vbvar 0))) with
      (map_fold (fun k0 x0 acc => open_tm k0 (vfvar x0) acc)
        (tapp_tm (↑[0] e) (vbvar 0)) (open_env_lift η')).
    rewrite IH.
    change (map_fold (fun k0 x0 acc => open_tm k0 (vfvar x0) acc) e
      (<[k:=x]> η')) with (open_tm_env (<[k := x]> η') e).
    rewrite open_tm_env_insert_fresh by exact Hfresh.
    apply open_tapp_tm_shift_bvar0_under_lvar.
Qed.

Lemma open_tm_env_precompose η ξ e :
  open_tm_env ξ (open_tm_env η e) =
  open_tm_env (open_env_precompose η ξ) e.
Proof.
  revert ξ e.
  unfold open_tm_env at 1.
  refine (fin_maps.map_fold_ind
    (fun η => ∀ ξ e,
      open_tm_env ξ
        (map_fold (fun k x acc => open_tm k (vfvar x) acc) e η) =
      open_tm_env (open_env_precompose η ξ) e) _ _ η).
  - intros ξ e. rewrite map_fold_empty.
    rewrite open_env_precompose_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH ξ e.
    rewrite Hfold.
    rewrite open_tm_env_open_tm.
    rewrite IH.
    rewrite <- open_env_precompose_insert_fresh by exact Hfresh.
    reflexivity.
Qed.
