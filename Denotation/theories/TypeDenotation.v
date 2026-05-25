(** * Denotation.Definition

    The recursive choice-type denotation on the new route.

    This file intentionally keeps the old [TypeDenotation] syntax sugar
    inlined.  In particular there are no exported wrappers for typed forall
    binders, expression continuations, closed-resource atoms, or denotation
    obligations.  The regularity side conditions are the component formulas
    supplied by [ChoiceBasicDenotation]. *)

From CoreLang Require Import Syntax Sugar BasicTypingProps.
From ChoiceAlgebra Require Import Resource.
From ChoiceLogic Require Import Formula FormulaDerived FormulaWorldExtension.
From ChoiceTypeLanguage Require Import Interface.
From ChoiceBasicDenotation Require Import Interface.
From LocallyNameless Require Import Tactics.

Section TypeDenotation.

Local Notation FormulaT := (Formula (V := value)) (only parsing).
Local Notation WorldT := (World (V := value)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := value)) (only parsing).
Local Notation FiberExtensionT := (fiber_extension (V := value)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Lemma bvar_lvars_at_shift_under d k n :
  k <= d ->
  value_lvars_at (S d) (value_shift k (vbvar n)) =
  value_lvars_at d (vbvar n).
Proof.
  intros Hkd.
  cbn [value_shift value_lvars_at]. unfold bvar_lvars_at.
  destruct (bool_decide (k <= n)) eqn:Hknb.
  - apply bool_decide_eq_true_1 in Hknb.
    cbn [value_lvars_at]. unfold bvar_lvars_at.
    destruct (decide (S d <= S n)) as [Hsdn|Hsdn].
    + destruct (decide (d <= n)) as [_|Hbad]; [|lia].
      replace (S n - S d) with (n - d) by lia.
      reflexivity.
    + destruct (decide (d <= n)) as [Hbad|_]; [lia|reflexivity].
  - apply bool_decide_eq_false_1 in Hknb.
    cbn [value_lvars_at]. unfold bvar_lvars_at.
    destruct (decide (S d <= n)) as [Hsdn|Hsdn].
    + lia.
    + destruct (decide (d <= n)) as [Hdn|Hdn].
      * assert (n = d) by lia. subst n. lia.
      * reflexivity.
Qed.

Lemma value_tm_lvars_at_shift_under_mutual :
  (forall v d k,
      k <= d ->
      value_lvars_at (S d) (value_shift k v) = value_lvars_at d v) *
  (forall e d k,
      k <= d ->
      tm_lvars_at (S d) (tm_shift k e) = tm_lvars_at d e).
Proof.
  apply value_tm_mutind; cbn [value_shift tm_shift value_lvars_at tm_lvars_at];
    intros; try reflexivity.
  - apply bvar_lvars_at_shift_under. exact H.
  - rewrite H by lia. reflexivity.
  - rewrite H by lia. reflexivity.
  - rewrite H by exact H0. reflexivity.
  - rewrite H by exact H1.
    rewrite H0 by lia. reflexivity.
  - rewrite H by exact H0. reflexivity.
  - rewrite H by exact H1.
    rewrite H0 by exact H1. reflexivity.
  - rewrite H by exact H2.
    rewrite H0 by exact H2.
    rewrite H1 by exact H2. reflexivity.
Qed.

Lemma value_lvars_at_shift_under v d k :
  k <= d ->
  value_lvars_at (S d) (value_shift k v) = value_lvars_at d v.
Proof. exact (fst value_tm_lvars_at_shift_under_mutual v d k). Qed.

Lemma tm_lvars_at_shift_under e d k :
  k <= d ->
  tm_lvars_at (S d) (tm_shift k e) = tm_lvars_at d e.
Proof. exact (snd value_tm_lvars_at_shift_under_mutual e d k). Qed.

Lemma value_lvars_at_bound0_under d :
  value_lvars_at (S d) (vbvar 0) = ∅.
Proof.
  cbn [value_lvars_at]. unfold bvar_lvars_at.
  destruct (decide (S d <= 0)); [lia|reflexivity].
Qed.

Lemma tm_lvars_at_tret_bound0_under d :
  tm_lvars_at (S d) (tret (vbvar 0)) = ∅.
Proof. cbn [tm_lvars_at]. apply value_lvars_at_bound0_under. Qed.

Lemma tm_lvars_at_tapp_shift_bound0 e d k :
  k <= d ->
  tm_lvars_at (S d) (tapp_tm (tm_shift k e) (vbvar 0)) ⊆
  tm_lvars_at d e.
Proof.
  induction e in d, k |- *; cbn [tm_shift tapp_tm tm_lvars_at]; intros Hkd.
  - rewrite value_lvars_at_shift_under by lia.
    rewrite value_lvars_at_bound0_under. set_solver.
  - pose proof (IHe2 (S d) (S k) ltac:(lia)) as Hbody.
    rewrite tm_lvars_at_shift_under by lia. set_solver.
  - rewrite value_lvars_at_shift_under by lia.
    cbn [tm_lvars_at].
    rewrite !value_lvars_at_bound0_under. set_solver.
  - rewrite value_lvars_at_shift_under by lia.
    rewrite value_lvars_at_shift_under by lia.
    cbn [tm_lvars_at].
    rewrite !value_lvars_at_bound0_under. set_solver.
  - rewrite value_lvars_at_shift_under by lia.
    rewrite tm_lvars_at_shift_under by lia.
    rewrite tm_lvars_at_shift_under by lia.
    cbn [tm_lvars_at].
    rewrite !value_lvars_at_bound0_under. set_solver.
Qed.

Lemma tm_lvars_at_tapp_shift0_bound0 e d :
  tm_lvars_at (S d) (tapp_tm (tm_shift 0 e) (vbvar 0)) ⊆
  tm_lvars_at d e.
Proof. apply tm_lvars_at_tapp_shift_bound0. lia. Qed.

Lemma open_tm_shift0_lc y e :
  lc_tm e ->
  open_tm 0 (vfvar y) (tm_shift 0 e) = e.
Proof.
  intros Hlc.
  rewrite tm_shift_lc_id by exact Hlc.
  apply open_rec_lc_tm. exact Hlc.
Qed.

Definition lty_env_restrict_lvars (Σ : lty_env) (D : lvset) : lty_env :=
  storeA_restrict Σ D.

Definition denot_relevant_lvars (τ : choice_ty) (e : tm) : lvset :=
  choice_ty_lvars τ ∪ tm_lvars e.

Definition denot_relevant_env (Σ : lty_env) (τ : choice_ty) (e : tm) : lty_env :=
  lty_env_restrict_lvars Σ (denot_relevant_lvars τ e).

Lemma lty_env_to_atom_env_restrict_lvars_lookup Σ D x :
  LVFree x ∈ D ->
  lty_env_to_atom_env (lty_env_restrict_lvars Σ D) !! x =
  lty_env_to_atom_env Σ !! x.
Proof.
  intros HxD.
  rewrite !lty_env_to_atom_env_lookup.
  unfold lty_env_restrict_lvars.
  destruct ((Σ : gmap logic_var ty) !! LVFree x) as [T|] eqn:HΣ.
  - apply storeA_restrict_lookup_some_2; assumption.
  - apply storeA_restrict_lookup_none_l. exact HΣ.
Qed.

Lemma basic_typing_lty_env_to_atom_env_restrict_lvars Σ D e T :
  tm_lvars e ⊆ D ->
  lty_env_to_atom_env Σ ⊢ₑ e ⋮ T ->
  lty_env_to_atom_env (lty_env_restrict_lvars Σ D) ⊢ₑ e ⋮ T.
Proof.
  intros Hsub Hty.
  eapply basic_typing_env_agree_tm; [exact Hty |].
  intros x Hx.
  apply lty_env_to_atom_env_restrict_lvars_lookup.
  apply Hsub.
  apply lvars_fv_elem.
  rewrite tm_lvars_fv. exact Hx.
Qed.

Lemma basic_typing_lty_env_to_atom_env_denot_relevant_env Σ τ e T :
  lty_env_to_atom_env Σ ⊢ₑ e ⋮ T ->
  lty_env_to_atom_env (denot_relevant_env Σ τ e) ⊢ₑ e ⋮ T.
Proof.
  intros Hty.
  unfold denot_relevant_env, denot_relevant_lvars.
  eapply basic_typing_lty_env_to_atom_env_restrict_lvars; [|exact Hty].
  set_solver.
Qed.

Lemma lty_env_restrict_lvars_fv_subset Σ D :
  lvars_fv (dom (lty_env_restrict_lvars Σ D)) ⊆ lvars_fv D.
Proof.
  unfold lty_env_restrict_lvars.
  change (lvars_fv (dom (storeA_restrict (Σ : gmap logic_var ty) D)) ⊆
    lvars_fv D).
  rewrite storeA_restrict_dom.
  apply lvars_fv_mono. set_solver.
Qed.

Lemma lty_env_restrict_lvars_fv_dom_subset Σ D :
  lvars_fv (dom (lty_env_restrict_lvars Σ D)) ⊆ lvars_fv (dom Σ).
Proof.
  unfold lty_env_restrict_lvars.
  change (lvars_fv (dom (storeA_restrict (Σ : gmap logic_var ty) D)) ⊆
    lvars_fv (dom Σ)).
  rewrite storeA_restrict_dom.
  apply lvars_fv_mono. set_solver.
Qed.

Lemma lty_env_restrict_lvars_insert_fresh Σ D x T :
  LVFree x ∉ D ->
  lty_env_restrict_lvars (<[LVFree x := T]> Σ) D =
  lty_env_restrict_lvars Σ D.
Proof.
  intros HxD.
  unfold lty_env_restrict_lvars.
  change (storeA_restrict (<[LVFree x := T]> (Σ : gmap logic_var ty)) D =
    storeA_restrict (Σ : gmap logic_var ty) D).
  unfold storeA_restrict.
  apply map_restrict_insert_notin. exact HxD.
Qed.

Lemma denot_relevant_env_fv_subset Σ τ e :
  lvars_fv (dom (denot_relevant_env Σ τ e)) ⊆
  fv_cty τ ∪ fv_tm e.
Proof.
  unfold denot_relevant_env, denot_relevant_lvars.
  transitivity (lvars_fv (choice_ty_lvars τ ∪ tm_lvars e)).
  - apply lty_env_restrict_lvars_fv_subset.
  - rewrite lvars_fv_union, choice_ty_lvars_fv, tm_lvars_fv.
    set_solver.
Qed.

Lemma tm_lvars_free_notin_of_fv x e :
  x ∉ fv_tm e ->
  LVFree x ∉ tm_lvars e.
Proof.
  intros Hx Hbad.
  apply Hx.
  rewrite <- tm_lvars_fv.
  apply lvars_fv_elem. exact Hbad.
Qed.

Lemma denot_relevant_lvars_insert_fresh x τ e :
  LVFree x ∉ choice_ty_lvars τ ->
  x ∉ fv_tm e ->
  LVFree x ∉ denot_relevant_lvars τ e.
Proof.
  intros Hxτ Hxe.
  unfold denot_relevant_lvars.
  pose proof (tm_lvars_free_notin_of_fv x e Hxe).
  set_solver.
Qed.

Lemma denot_relevant_env_insert_fresh Σ τ e x T :
  LVFree x ∉ choice_ty_lvars τ ->
  x ∉ fv_tm e ->
  denot_relevant_env (<[LVFree x := T]> Σ) τ e =
  denot_relevant_env Σ τ e.
Proof.
  intros Hxτ Hxe.
  unfold denot_relevant_env, lty_env_restrict_lvars.
  change (storeA_restrict
    (<[LVFree x := T]> (Σ : gmap logic_var ty))
    (denot_relevant_lvars τ e) =
    storeA_restrict (Σ : gmap logic_var ty)
      (denot_relevant_lvars τ e)).
  unfold storeA_restrict.
  apply map_restrict_insert_notin.
  apply denot_relevant_lvars_insert_fresh; assumption.
Qed.

Lemma lvars_at_depth_free_elem d D x :
  LVFree x ∈ lvars_at_depth d D <-> LVFree x ∈ D.
Proof.
  rewrite lvars_at_depth_elem.
  split.
  - intros [v [Hv Hdepth]].
    destruct v as [n|y]; cbn [logic_var_at_depth] in Hdepth.
    + destruct (decide (d <= n)); discriminate.
    + inversion Hdepth. subst. exact Hv.
  - intros Hx.
    exists (LVFree x). split; [exact Hx | reflexivity].
Qed.

Lemma lvars_at_depth_depth d c D :
  lvars_at_depth d (lvars_at_depth c D) = lvars_at_depth (c + d) D.
Proof.
  apply set_eq. intros u.
  rewrite (lvars_at_depth_elem d (lvars_at_depth c D) u).
  rewrite (lvars_at_depth_elem (c + d) D u).
  split.
  - intros [v [Hv Hvu]].
    apply lvars_at_depth_elem in Hv as [w [Hw Hwv]].
    exists w. split; [exact Hw|].
    destruct w as [n|x].
    + cbn [logic_var_at_depth] in Hwv.
      destruct (decide (c <= n)) as [Hcn|Hcn]; [|discriminate].
      inversion Hwv. subst v.
      cbn [logic_var_at_depth] in Hvu.
      destruct (decide (d <= n - c)) as [Hdn|Hdn]; [|discriminate].
      inversion Hvu. subst u.
      cbn [logic_var_at_depth].
      destruct (decide (c + d <= n)) as [_|Hbad]; [|lia].
      replace (n - (c + d)) with (n - c - d) by lia.
      reflexivity.
    + cbn [logic_var_at_depth] in Hwv. inversion Hwv. subst v.
      cbn [logic_var_at_depth] in Hvu.
      inversion Hvu. subst u. reflexivity.
  - intros [v [Hv Hvu]].
    destruct v as [n|x].
    + cbn [logic_var_at_depth] in Hvu.
      destruct (decide (c + d <= n)) as [Hcdn|Hcdn]; [|discriminate].
      inversion Hvu. subst u.
      exists (#ₗ (n - c))%choice. split.
      * apply lvars_at_depth_elem. exists (LVBound n). split; [exact Hv|].
        cbn [logic_var_at_depth].
        destruct (decide (c <= n)) as [_|Hbad]; [reflexivity|lia].
      * cbn [logic_var_at_depth].
        destruct (decide (d <= n - c)) as [_|Hbad]; [|lia].
        replace (n - c - d) with (n - (c + d)) by lia.
        reflexivity.
    + cbn [logic_var_at_depth] in Hvu. inversion Hvu. subst u.
      exists (LVFree x). split.
      * apply lvars_at_depth_elem. exists (LVFree x). split; [exact Hv|reflexivity].
      * reflexivity.
Qed.

Lemma choice_ty_lvars_at_depth τ c d :
  lvars_at_depth d (choice_ty_lvars_at c τ) =
  choice_ty_lvars_at (c + d) τ.
Proof.
  induction τ in c, d |- *; cbn [choice_ty_lvars_at];
    rewrite ?lvars_at_depth_union, ?IHτ1, ?IHτ2.
  - rewrite lvars_at_depth_depth. reflexivity.
  - rewrite lvars_at_depth_depth. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - replace (S c + d) with (S (c + d)) by lia. reflexivity.
  - replace (S c + d) with (S (c + d)) by lia. reflexivity.
Qed.

Lemma choice_ty_lvars_depth τ d :
  lvars_at_depth d (choice_ty_lvars τ) = choice_ty_lvars_at d τ.
Proof.
  unfold choice_ty_lvars.
  rewrite choice_ty_lvars_at_depth. reflexivity.
Qed.

Lemma lvars_at_depth_denot_relevant_env_subset d Σ τ e :
  lvars_at_depth d (dom (denot_relevant_env Σ τ e)) ⊆
  lvars_at_depth d (dom Σ) ∪ choice_ty_lvars_at d τ ∪ tm_lvars_at d e.
Proof.
  unfold denot_relevant_env, lty_env_restrict_lvars, denot_relevant_lvars.
  change (lvars_at_depth d
    (dom (storeA_restrict (Σ : gmap logic_var ty)
      (choice_ty_lvars τ ∪ tm_lvars e))) ⊆
    lvars_at_depth d (dom Σ) ∪ choice_ty_lvars_at d τ ∪ tm_lvars_at d e).
  rewrite storeA_restrict_dom.
  transitivity (lvars_at_depth d (dom Σ ∩ (choice_ty_lvars τ ∪ tm_lvars e))).
  { reflexivity. }
  transitivity (lvars_at_depth d (dom Σ) ∩
    lvars_at_depth d (choice_ty_lvars τ ∪ tm_lvars e)).
  - intros v Hv.
    apply lvars_at_depth_elem in Hv as [u [Hu Huv]].
    apply elem_of_intersection in Hu as [HuΣ HuD].
    apply elem_of_intersection. split; apply lvars_at_depth_elem;
      exists u; split; assumption.
  - rewrite lvars_at_depth_union, choice_ty_lvars_depth, tm_lvars_depth.
    set_solver.
Qed.

Lemma lvars_at_depth_denot_relevant_typed_bind_subset d Σ T τ e :
  lvars_at_depth (S d)
    (dom (denot_relevant_env (typed_lty_env_bind Σ T) τ e)) ⊆
  lvars_at_depth d (dom Σ).
Proof.
  unfold denot_relevant_env, lty_env_restrict_lvars.
  change (lvars_at_depth (S d)
    (dom (storeA_restrict
      (typed_lty_env_bind Σ T : gmap logic_var ty)
      (denot_relevant_lvars τ e))) ⊆
    lvars_at_depth d (dom Σ)).
  rewrite storeA_restrict_dom.
  transitivity (lvars_at_depth (S d) (dom (typed_lty_env_bind Σ T))).
  - apply lvars_at_depth_mono. set_solver.
  - rewrite lvars_at_depth_typed_lty_env_bind. reflexivity.
Qed.

Lemma lvars_at_depth_restrict_typed_bind_subset d Σ T D :
  lvars_at_depth (S d)
    (dom (lty_env_restrict_lvars (typed_lty_env_bind Σ T) D)) ⊆
  lvars_at_depth d (dom Σ).
Proof.
  unfold lty_env_restrict_lvars.
  change (lvars_at_depth (S d)
    (dom (storeA_restrict
      (typed_lty_env_bind Σ T : gmap logic_var ty) D)) ⊆
    lvars_at_depth d (dom Σ)).
  rewrite storeA_restrict_dom.
  transitivity (lvars_at_depth (S d) (dom (typed_lty_env_bind Σ T))).
  - apply lvars_at_depth_mono. set_solver.
  - rewrite lvars_at_depth_typed_lty_env_bind. reflexivity.
Qed.

Lemma lvars_at_depth_dom_singleton_bound0_succ d T :
  lvars_at_depth (S d) (dom (<[LVBound 0 := T]> (∅ : lty_env))) = ∅.
Admitted.

Lemma choice_ty_lvars_shift_free_notin k x τ :
  LVFree x ∉ choice_ty_lvars τ ->
  LVFree x ∉ choice_ty_lvars (cty_shift k τ).
Proof.
  intros Hfresh Hin.
  apply Hfresh. apply lvars_fv_elem.
  apply lvars_fv_elem in Hin.
  change (x ∈ fv_cty (cty_shift k τ)) in Hin.
  rewrite cty_shift_fv in Hin. exact Hin.
Qed.

Fixpoint denot_ty_lvar_gas
    (gas : nat) (Σ : lty_env) (τ : choice_ty) (e : tm)
    {struct gas} : FormulaT :=
  let Σg := denot_relevant_env Σ τ e in
  FAnd
    (FAnd (choice_ty_wf_formula Σg τ)
      (FAnd (basic_world_formula Σg)
        (FAnd (expr_basic_typing_formula Σg e (erase_ty τ))
              (expr_total_formula e))))
    (match gas with
    | 0 => FTrue
    | S gas' =>
      match τ with
      | CTOver b φ =>
          FForall
            (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
              (FImpl
                (expr_result_formula (tm_shift 0 e) (LVBound 0))
                (FFibVars (qual_vars φ ∖ {[LVBound 0]})
                  (FOver (type_qualifier_formula φ)))))
      | CTUnder b φ =>
          FForall
            (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
              (FImpl
                (expr_result_formula (tm_shift 0 e) (LVBound 0))
                (FFibVars (qual_vars φ ∖ {[LVBound 0]})
                  (FUnder (type_qualifier_formula φ)))))
      | CTInter τ1 τ2 =>
          FAnd
            (denot_ty_lvar_gas gas' Σ τ1 e)
            (denot_ty_lvar_gas gas' Σ τ2 e)
      | CTUnion τ1 τ2 =>
          FOr
            (denot_ty_lvar_gas gas' Σ τ1 e)
            (denot_ty_lvar_gas gas' Σ τ2 e)
      | CTSum τ1 τ2 =>
          FPlus
            (denot_ty_lvar_gas gas' Σ τ1 e)
            (denot_ty_lvar_gas gas' Σ τ2 e)
      | CTArrow τx τr =>
          let Σx := typed_lty_env_bind Σg (erase_ty τx) in
          FForall
            (FImpl (basic_world_formula (<[LVBound 0 := (erase_ty τx)]> ∅))
              (FImpl
                (denot_ty_lvar_gas gas' Σx
                  (cty_shift 0 τx) (tret (vbvar 0)))
                (denot_ty_lvar_gas gas' Σx τr
                  (tapp_tm (tm_shift 0 e) (vbvar 0)))))
      | CTWand τx τr =>
          let Σx := typed_lty_env_bind Σg (erase_ty τx) in
          FForall
            (FImpl (basic_world_formula (<[LVBound 0 := (erase_ty τx)]> ∅))
              (FWand
                (denot_ty_lvar_gas gas' Σx
                  (cty_shift 0 τx) (tret (vbvar 0)))
                (denot_ty_lvar_gas gas' Σx τr
                  (tapp_tm (tm_shift 0 e) (vbvar 0)))))
      end
    end).

Fixpoint formula_lvars_at (d : nat) (φ : FormulaT) : lvset :=
  match φ with
  | FTrue | FFalse => ∅
  | FAtom q => lvars_at_depth d (lqual_lvars q)
  | FAnd p q | FOr p q | FImpl p q
  | FStar p q | FWand p q | FPlus p q =>
      formula_lvars_at d p ∪ formula_lvars_at d q
  | FForall p => formula_lvars_at (S d) p
  | FOver p | FUnder p => formula_lvars_at d p
  | FFibVars D p => lvars_at_depth d D ∪ formula_lvars_at d p
  end.

Lemma formula_lvars_at_fv d (φ : FormulaT) :
  lvars_fv (formula_lvars_at d φ) = formula_fv φ.
Proof.
  induction φ in d |- *; cbn [formula_lvars_at];
    rewrite ?lvars_fv_lvars_at_depth, ?lvars_fv_union,
      ?IHφ1, ?IHφ2, ?IHφ;
    rewrite ?formula_fv_true, ?formula_fv_false, ?formula_fv_atom,
      ?formula_fv_and, ?formula_fv_or, ?formula_fv_impl,
      ?formula_fv_star, ?formula_fv_wand, ?formula_fv_plus,
      ?formula_fv_forall, ?formula_fv_over, ?formula_fv_under,
      ?formula_fv_fibvars;
    rewrite ?lvars_fv_lvars_at_depth;
    reflexivity.
Qed.

Ltac rewrite_tm_support :=
  repeat match goal with
  | |- context [lvars_at_depth ?d (tm_lvars ?e)] =>
      rewrite (tm_lvars_depth e d)
  | H : context [lvars_at_depth ?d (tm_lvars ?e)] |- _ =>
      rewrite (tm_lvars_depth e d) in H
  end.

Ltac unfold_formula_lvars_atoms :=
  cbn [formula_lvars_at choice_ty_wf_formula basic_world_formula
    expr_basic_typing_formula expr_total_formula expr_result_formula
    type_qualifier_formula];
  unfold lqual_lvars, choice_ty_wf_lqual, basic_world_lqual,
    expr_basic_typing_lqual, expr_total_lqual, expr_result_lqual,
    type_qualifier_lqual;
  cbn [lqual_dom].

Lemma formula_lvars_at_denot_ty_lvar_gas_subset gas d Σ τ e :
  formula_lvars_at d (denot_ty_lvar_gas gas Σ τ e) ⊆
  lvars_at_depth d (dom Σ) ∪ tm_lvars_at d e ∪ choice_ty_lvars_at d τ.
Admitted.

Definition denot_ty
    (Δ : gmap atom ty) (τ : choice_ty) (e : tm) : FormulaT :=
  denot_ty_lvar_gas (cty_depth τ) (atom_env_to_lty_env Δ) τ e.

Lemma formula_open_expr_result_formula_shift0 y e :
  lc_tm e ->
  y ∉ fv_tm e ->
  formula_open 0 y (expr_result_formula (tm_shift 0 e) (LVBound 0)) =
  expr_result_formula e (LVFree y).
Proof.
  intros Hlc Hy.
  rewrite formula_open_expr_result_formula.
  - rewrite open_tm_shift0_lc by exact Hlc.
    replace (logic_var_open 0 y (LVBound 0)) with (LVFree y).
    reflexivity.
    unfold logic_var_open, swap, swap_action_self, eq_swap.
    repeat destruct decide; try lia; try congruence.
  - rewrite tm_shift_fv. exact Hy.
Qed.

Lemma formula_open_denot_ty_lvar_gas_typed_bind_current
    y gas Σ T τ e :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  y ∉ fv_tm e ->
  formula_open 0 y
    (denot_ty_lvar_gas gas (typed_lty_env_bind Σ T) τ e) =
  denot_ty_lvar_gas gas
    (<[LVFree y := T]> Σ)
    (cty_open 0 y τ)
    (open_tm 0 (vfvar y) e).
Admitted.

Lemma formula_open_denot_ty_lvar_gas_arrow_arg_current
    y gas Σ T τ :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  formula_open 0 y
    (denot_ty_lvar_gas gas (typed_lty_env_bind Σ T)
      (cty_shift 0 τ) (tret (vbvar 0))) =
  denot_ty_lvar_gas gas
    (<[LVFree y := T]> Σ)
    (cty_open 0 y (cty_shift 0 τ))
    (tret (vfvar y)).
Proof.
  intros Hfresh Hclosed.
  rewrite formula_open_denot_ty_lvar_gas_typed_bind_current by (try assumption; set_solver).
  reflexivity.
Qed.

Lemma formula_open_denot_ty_lvar_gas_arrow_conseq_current
    y gas Σ T τ e :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  lc_tm e ->
  y ∉ fv_tm e ->
  formula_open 0 y
    (denot_ty_lvar_gas gas (typed_lty_env_bind Σ T) τ
      (tapp_tm (tm_shift 0 e) (vbvar 0))) =
  denot_ty_lvar_gas gas
    (<[LVFree y := T]> Σ)
    (cty_open 0 y τ)
    (tapp_tm e (vfvar y)).
Proof.
  intros Hfresh Hclosed Hlc Hy.
  rewrite formula_open_denot_ty_lvar_gas_typed_bind_current.
  - unfold tapp_tm.
    cbn [open_tm open_value value_shift].
    rewrite open_tm_shift0_lc by exact Hlc.
    destruct (decide (1 = 0)) as [Hbad|_]; [lia|].
    destruct (decide (1 = 1)) as [_|Hbad]; [reflexivity|lia].
  - exact Hfresh.
  - exact Hclosed.
  - rewrite fv_tapp_tm, tm_shift_fv. cbn [fv_value]. set_solver.
Qed.

(** Gas normalization.  The old route had separate body/obligation saturation
    lemmas; the new denotation keeps the component guard inline, so the useful
    surface statement is just that any gas above [cty_depth τ] is equivalent to
    the canonical depth gas. *)
Lemma denot_ty_lvar_gas_saturate gas Σ τ e :
  cty_depth τ <= gas ->
  denot_ty_lvar_gas gas Σ τ e =
  denot_ty_lvar_gas (cty_depth τ) Σ τ e.
Proof.
  assert (Hsat :
    forall gas τ Σ e,
      cty_depth τ <= gas ->
      denot_ty_lvar_gas gas Σ τ e =
      denot_ty_lvar_gas (cty_depth τ) Σ τ e).
  {
    intros fuel.
    induction fuel as [fuel IH] using lt_wf_ind.
    intros τ0 Σ0 e0 Hgas.
    destruct fuel as [|gas']; destruct τ0; cbn [cty_depth] in Hgas; try lia;
      cbn [cty_depth denot_ty_lvar_gas].
    - reflexivity.
    - reflexivity.
    - rewrite (IH gas' ltac:(lia) τ0_1 Σ0 e0 ltac:(lia)).
      rewrite (IH gas' ltac:(lia) τ0_2 Σ0 e0 ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_1 Σ0 e0 ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_2 Σ0 e0 ltac:(lia)).
      reflexivity.
    - rewrite (IH gas' ltac:(lia) τ0_1 Σ0 e0 ltac:(lia)).
      rewrite (IH gas' ltac:(lia) τ0_2 Σ0 e0 ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_1 Σ0 e0 ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_2 Σ0 e0 ltac:(lia)).
      reflexivity.
    - rewrite (IH gas' ltac:(lia) τ0_1 Σ0 e0 ltac:(lia)).
      rewrite (IH gas' ltac:(lia) τ0_2 Σ0 e0 ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_1 Σ0 e0 ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_2 Σ0 e0 ltac:(lia)).
      reflexivity.
	    - rewrite (IH gas' ltac:(lia) (cty_shift 0 τ0_1)
	        (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
	          (erase_ty τ0_1)) (tret (vbvar 0))
	        ltac:(rewrite cty_shift_preserves_depth; lia)).
	      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
	        (cty_shift 0 τ0_1)
	        (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
	          (erase_ty τ0_1)) (tret (vbvar 0))
	        ltac:(rewrite cty_shift_preserves_depth; lia)).
	      rewrite (IH gas' ltac:(lia) τ0_2
	        (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
	          (erase_ty τ0_1))
	        (tapp_tm (tm_shift 0 e0) (vbvar 0)) ltac:(lia)).
	      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
	        τ0_2 (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
	          (erase_ty τ0_1))
	        (tapp_tm (tm_shift 0 e0) (vbvar 0)) ltac:(lia)).
	      reflexivity.
	    - rewrite (IH gas' ltac:(lia) (cty_shift 0 τ0_1)
	        (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
	          (erase_ty τ0_1)) (tret (vbvar 0))
	        ltac:(rewrite cty_shift_preserves_depth; lia)).
	      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
	        (cty_shift 0 τ0_1)
	        (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
	          (erase_ty τ0_1)) (tret (vbvar 0))
	        ltac:(rewrite cty_shift_preserves_depth; lia)).
	      rewrite (IH gas' ltac:(lia) τ0_2
	        (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
	          (erase_ty τ0_1))
	        (tapp_tm (tm_shift 0 e0) (vbvar 0)) ltac:(lia)).
	      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
	        τ0_2 (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
	          (erase_ty τ0_1))
	        (tapp_tm (tm_shift 0 e0) (vbvar 0)) ltac:(lia)).
      reflexivity.
  }
  intros Hgas. apply Hsat. exact Hgas.
Qed.

Lemma denot_ty_lvar_gas_saturate_ge gas1 gas2 Σ τ e :
  cty_depth τ <= gas1 ->
  cty_depth τ <= gas2 ->
  denot_ty_lvar_gas gas1 Σ τ e =
  denot_ty_lvar_gas gas2 Σ τ e.
Proof.
  intros Hgas1 Hgas2.
  rewrite (denot_ty_lvar_gas_saturate gas1 Σ τ e Hgas1).
  rewrite (denot_ty_lvar_gas_saturate gas2 Σ τ e Hgas2).
  reflexivity.
Qed.

Lemma choice_ty_wf_formula_insert_fresh_same_world
    (Σ : lty_env) τ (m : WfWorldT) x T :
  LVFree x ∉ dom Σ ->
  m ⊨ basic_world_formula (<[LVFree x := T]> Σ) ->
  m ⊨ choice_ty_wf_formula Σ τ ->
  m ⊨ choice_ty_wf_formula (<[LVFree x := T]> Σ) τ.
Proof.
  intros HxΣ Hworld Hwf.
  apply choice_ty_wf_formula_models_iff in Hwf as [_ [_ Hbasic]].
  apply basic_world_formula_models_iff in Hworld as [Hlc [Hsub _]].
  apply choice_ty_wf_formula_models_iff.
  split; [exact Hlc|].
  split; [exact Hsub|].
  apply basic_choice_ty_lvars_insert_fresh. exact Hbasic.
Qed.

Lemma expr_basic_typing_formula_insert_fresh_same_world
    (Σ : lty_env) e U (m : WfWorldT) x T :
  LVFree x ∉ dom Σ ->
  m ⊨ basic_world_formula (<[LVFree x := T]> Σ) ->
  m ⊨ expr_basic_typing_formula Σ e U ->
  m ⊨ expr_basic_typing_formula (<[LVFree x := T]> Σ) e U.
Proof.
  intros HxΣ Hworld Hbasic.
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
  apply basic_world_formula_models_iff in Hworld as [Hlc [Hsub _]].
  apply expr_basic_typing_formula_models_iff.
  split; [exact Hlc|].
  split; [exact Hsub|].
  apply basic_tm_has_ltype_insert_fresh_lvar; assumption.
Qed.

Lemma denot_ty_lvar_guard_insert_fresh_lty_env
    (Σ : lty_env) τ e x T (m : WfWorldT) :
  LVFree x ∉ dom Σ ->
  m ⊨ basic_world_formula (<[LVFree x := T]> Σ) ->
  m ⊨ FAnd (choice_ty_wf_formula Σ τ)
    (FAnd (basic_world_formula Σ)
      (FAnd (expr_basic_typing_formula Σ e (erase_ty τ))
            (expr_total_formula e))) ->
  m ⊨ FAnd (choice_ty_wf_formula (<[LVFree x := T]> Σ) τ)
    (FAnd (basic_world_formula (<[LVFree x := T]> Σ))
      (FAnd
        (expr_basic_typing_formula (<[LVFree x := T]> Σ) e (erase_ty τ))
        (expr_total_formula e))).
Proof.
  intros HxΣ Hworldx Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [_ [Hbasic Htotal]]].
  eapply res_models_and_intro_from_models.
  - eapply choice_ty_wf_formula_insert_fresh_same_world; eauto.
  - eapply res_models_and_intro_from_models; [exact Hworldx|].
    eapply res_models_and_intro_from_models; [|exact Htotal].
    eapply expr_basic_typing_formula_insert_fresh_same_world; eauto.
Qed.

Lemma denot_ty_lvar_gas_insert_fresh_lty_env_eq
    gas (Σ : lty_env) τ e x T :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ choice_ty_lvars τ ->
  x ∉ fv_tm e ->
  denot_ty_lvar_gas gas (<[LVFree x := T]> Σ) τ e =
  denot_ty_lvar_gas gas Σ τ e.
Admitted.

Lemma denot_ty_lvar_gas_insert_fresh_lty_env
    gas (Σ : lty_env) τ e x T (m : WfWorldT) :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ choice_ty_lvars τ ->
  x ∉ fv_tm e ->
  m ⊨ denot_ty_lvar_gas gas Σ τ e ->
  m ⊨ denot_ty_lvar_gas gas (<[LVFree x := T]> Σ) τ e.
Proof.
  intros HxΣ Hxτ Hxe Hm.
  rewrite (denot_ty_lvar_gas_insert_fresh_lty_env_eq gas Σ τ e x T);
    assumption.
Qed.

Lemma denot_ty_lvar_gas_extend_typed_extension
    gas (Σ : lty_env) τ e x T
    (m mx : WfWorldT) (Fx : FiberExtensionT) :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ choice_ty_lvars τ ->
  x ∉ fv_tm e ->
  extension_has_ltype (<[LVFree x := T]> ∅)
    (res_restrict m (ext_in Fx)) Fx ->
  res_extend_by m Fx mx ->
  m ⊨ denot_ty_lvar_gas gas Σ τ e ->
  mx ⊨ denot_ty_lvar_gas gas (<[LVFree x := T]> Σ) τ e.
Proof.
  intros HxΣ Hxτ Hxe HFx Hext Hm.
  assert (Hmx_old : mx ⊨ denot_ty_lvar_gas gas Σ τ e).
  {
    eapply res_models_extend_mono; [exact Hext | exact Hm].
  }
  eapply denot_ty_lvar_gas_insert_fresh_lty_env; eauto.
Qed.

Lemma denot_ty_lvar_gas_extend_typed_extension_zero
    (Σ : lty_env) τ e x T
    (m mx : WfWorldT) (Fx : FiberExtensionT) :
  LVFree x ∉ dom Σ ->
  extension_has_ltype (<[LVFree x := T]> ∅)
    (res_restrict m (ext_in Fx)) Fx ->
  res_extend_by m Fx mx ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ e ->
  mx ⊨ denot_ty_lvar_gas 0 (<[LVFree x := T]> Σ) τ e.
Admitted.

Lemma denot_ty_lvar_guard_extend_typed_extension
    (Σ : lty_env) τ e x T
    (m mx : WfWorldT) (Fx : FiberExtensionT) :
  LVFree x ∉ dom Σ ->
  extension_has_ltype (<[LVFree x := T]> ∅)
    (res_restrict m (ext_in Fx)) Fx ->
  res_extend_by m Fx mx ->
  m ⊨ FAnd (choice_ty_wf_formula Σ τ)
    (FAnd (basic_world_formula Σ)
      (FAnd (expr_basic_typing_formula Σ e (erase_ty τ))
            (expr_total_formula e))) ->
  mx ⊨ FAnd (choice_ty_wf_formula (<[LVFree x := T]> Σ) τ)
    (FAnd (basic_world_formula (<[LVFree x := T]> Σ))
      (FAnd
        (expr_basic_typing_formula (<[LVFree x := T]> Σ) e (erase_ty τ))
        (expr_total_formula e))).
Proof.
  intros HxΣ HFx Hext Hguard.
  pose proof HFx as HFx_full.
  destruct HFx as [_ [_ [Hout _]]].
  assert (Houtx : ext_out Fx = {[x]}).
  {
    change (lvars_fv (dom (<[LVFree x := T]> (∅ : gmap logic_var ty))) =
      ext_out Fx) in Hout.
    rewrite dom_insert_L, dom_empty_L, lvars_fv_union,
      lvars_fv_singleton_free in Hout.
    change (lvars_fv (∅ : lvset)) with (∅ : aset) in Hout.
    set_solver.
  }
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  repeat rewrite res_models_and_iff.
  split.
  - eapply choice_ty_wf_formula_insert_fresh_lvar; eauto.
  - split.
    + eapply basic_world_formula_insert_typed_extension; eauto.
    + split.
      * eapply expr_basic_typing_formula_insert_fresh_lvar; eauto.
      * eapply res_models_extend_mono; eauto.
Qed.

Ltac denot_ty_fv_norm :=
  cbn [denot_ty_lvar_gas denot_relevant_env lty_env_restrict_lvars
    denot_relevant_lvars formula_lvars formula_fv];
  repeat first
    [ rewrite formula_fv_true | rewrite formula_fv_false
    | rewrite formula_fv_and | rewrite formula_fv_or
    | rewrite formula_fv_impl | rewrite formula_fv_star
    | rewrite formula_fv_wand | rewrite formula_fv_plus
    | rewrite formula_fv_forall | rewrite formula_fv_over
    | rewrite formula_fv_under | rewrite formula_fv_fibvars ];
  rewrite ?formula_fv_choice_ty_wf_formula;
  rewrite ?formula_fv_basic_world_formula;
  rewrite ?formula_fv_expr_basic_typing_formula;
  rewrite ?formula_fv_expr_total_formula;
  rewrite ?formula_fv_expr_result_formula;
  rewrite ?formula_fv_type_qualifier_formula;
  rewrite ?storeA_restrict_dom;
  rewrite ?typed_lty_env_bind_lvars_fv_dom;
  rewrite ?tm_shift_fv, ?cty_shift_fv, ?fv_tapp_tm;
  rewrite ?tm_shift_fv, ?cty_shift_fv;
  cbn [fv_tm fv_value];
  rewrite ?lvars_fv_union, ?lvars_fv_of_atoms,
    ?lvars_fv_singleton_bound, ?lvars_fv_singleton_free;
  rewrite ?formula_fv_true, ?formula_fv_false, ?tm_lvars_fv.

Ltac denot_ty_fv_norm_in H :=
  cbn [denot_ty_lvar_gas denot_relevant_env lty_env_restrict_lvars
    denot_relevant_lvars formula_lvars formula_fv] in H;
  repeat first
    [ rewrite formula_fv_true in H | rewrite formula_fv_false in H
    | rewrite formula_fv_and in H | rewrite formula_fv_or in H
    | rewrite formula_fv_impl in H | rewrite formula_fv_star in H
    | rewrite formula_fv_wand in H | rewrite formula_fv_plus in H
    | rewrite formula_fv_forall in H | rewrite formula_fv_over in H
    | rewrite formula_fv_under in H | rewrite formula_fv_fibvars in H ];
  rewrite ?formula_fv_choice_ty_wf_formula in H;
  rewrite ?formula_fv_basic_world_formula in H;
  rewrite ?formula_fv_expr_basic_typing_formula in H;
  rewrite ?formula_fv_expr_total_formula in H;
  rewrite ?formula_fv_expr_result_formula in H;
  rewrite ?formula_fv_type_qualifier_formula in H;
  rewrite ?storeA_restrict_dom in H;
  rewrite ?typed_lty_env_bind_lvars_fv_dom in H;
  rewrite ?tm_shift_fv, ?cty_shift_fv, ?fv_tapp_tm in H;
  rewrite ?tm_shift_fv, ?cty_shift_fv in H;
  cbn [fv_tm fv_value] in H;
  rewrite ?lvars_fv_union, ?lvars_fv_of_atoms,
    ?lvars_fv_singleton_bound, ?lvars_fv_singleton_free in H;
  rewrite ?formula_fv_true, ?formula_fv_false, ?tm_lvars_fv in H.

Ltac denot_ty_fv_set :=
  denot_ty_fv_norm;
  fast_set_solver!!.

Lemma formula_fv_denot_ty_lvar_gas_subset_relevant gas Σ τ e :
  formula_fv (denot_ty_lvar_gas gas Σ τ e) ⊆
  fv_tm e ∪ fv_cty τ.
Admitted.

Lemma formula_fv_denot_ty_lvar_gas_subset_env_term gas Σ τ e :
  formula_fv (denot_ty_lvar_gas gas Σ τ e) ⊆
  lvars_fv (dom Σ) ∪ fv_tm e ∪ fv_cty τ.
Proof.
  pose proof (formula_fv_denot_ty_lvar_gas_subset_relevant gas Σ τ e).
  set_solver.
Qed.

Lemma formula_fv_denot_ty_lvar_gas_guard_subset gas Σ τ e :
  lvars_fv (dom (denot_relevant_env Σ τ e)) ∪ fv_tm e ⊆
  formula_fv (denot_ty_lvar_gas gas Σ τ e).
Proof.
  destruct gas; cbn [denot_ty_lvar_gas denot_relevant_env
    lty_env_restrict_lvars denot_relevant_lvars];
    repeat rewrite ?formula_fv_and, ?formula_fv_true,
      ?formula_fv_choice_ty_wf_formula, ?formula_fv_basic_world_formula,
      ?formula_fv_expr_basic_typing_formula, ?formula_fv_expr_total_formula;
    rewrite ?storeA_restrict_dom, ?tm_lvars_fv;
    set_solver.
Qed.

Lemma fv_tapp_shift0_bvar0_subset_env_or X e1 e2 :
  fv_tm e1 ⊆ X ∪ fv_tm e2 ->
  fv_tm (tapp_tm (tm_shift 0 e1) (vbvar 0)) ⊆
  X ∪ fv_tm (tapp_tm (tm_shift 0 e2) (vbvar 0)).
Proof.
  intros He.
  rewrite !fv_tapp_tm, !tm_shift_fv.
  cbn [fv_value].
  set_solver.
Qed.

Lemma formula_fv_denot_ty_lvar_gas_mono_env_term gas Σ1 Σ2 τ e1 e2 :
  lvars_fv (dom Σ1) ⊆ lvars_fv (dom Σ2) ->
  fv_tm e1 ⊆ fv_tm e2 ->
  formula_fv (denot_ty_lvar_gas gas Σ1 τ e1) ⊆
  formula_fv (denot_ty_lvar_gas gas Σ2 τ e2).
Admitted.

Lemma formula_fv_denot_ty_lvar_gas_mono_env_or_term gas Σ1 Σ2 τ e1 e2 :
  lvars_fv (dom Σ1) ⊆ lvars_fv (dom Σ2) ->
  fv_tm e1 ⊆ lvars_fv (dom Σ2) ∪ fv_tm e2 ->
  formula_fv (denot_ty_lvar_gas gas Σ1 τ e1) ⊆
  lvars_fv (dom Σ2) ∪
    formula_fv (denot_ty_lvar_gas gas Σ2 τ e2).
Admitted.

Lemma formula_fv_denot_ty_lvar_gas_insert_fresh_upper
    gas Σ x T τ e :
  formula_fv (denot_ty_lvar_gas gas (<[LVFree x := T]> Σ) τ e) ⊆
  lvars_fv (dom Σ) ∪ fv_tm e ∪ fv_cty τ ∪ {[x]}.
Proof.
  transitivity
    (lvars_fv (dom (<[LVFree x := T]> Σ)) ∪ fv_tm e ∪ fv_cty τ).
  - apply formula_fv_denot_ty_lvar_gas_subset_env_term.
  - change (lvars_fv (dom (<[LVFree x := T]> (Σ : gmap logic_var ty))) ∪
      fv_tm e ∪ fv_cty τ ⊆ lvars_fv (dom Σ) ∪ fv_tm e ∪ fv_cty τ ∪ {[x]}).
    rewrite dom_insert_L, lvars_fv_union, lvars_fv_singleton_free.
    set_solver.
Qed.

Lemma denot_ty_lvar_gas_scope_from_guard
    gas Σ τ e (m : WfWorldT) :
  m ⊨ FAnd (choice_ty_wf_formula Σ τ)
    (FAnd (basic_world_formula Σ)
      (FAnd (expr_basic_typing_formula Σ e (erase_ty τ))
            (expr_total_formula e))) ->
  formula_fv (denot_ty_lvar_gas gas Σ τ e) ⊆ world_dom (m : WorldT).
Proof.
  intros Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [_ Htotal]]].
  transitivity (lvars_fv (dom Σ) ∪ fv_tm e ∪ fv_cty τ).
  - apply formula_fv_denot_ty_lvar_gas_subset_env_term.
  - pose proof (proj1 (basic_world_formula_models_iff Σ m) Hworld)
      as [_ [HΣ _]].
    pose proof (res_models_fuel_scoped _ _ _ Htotal) as He.
    pose proof (choice_ty_wf_formula_fv_cty_subset Σ τ m Hwf) as Hτ.
    unfold formula_scoped_in_world in He.
    rewrite formula_fv_expr_total_formula in He.
    rewrite tm_lvars_fv in He.
    intros a Ha.
    apply elem_of_union in Ha as [Ha | Ha].
    + apply elem_of_union in Ha as [Ha | Ha].
      * exact (HΣ a Ha).
      * exact (He a Ha).
    + apply HΣ. exact (Hτ a Ha).
Qed.

Lemma denot_ty_lvar_gas_insert_scope_from_parts
    gas Σ τ e x T (mx : WfWorldT) :
  lvars_fv (dom Σ) ∪ {[x]} ⊆ world_dom (mx : WorldT) ->
  fv_tm e ⊆ world_dom (mx : WorldT) ->
  fv_cty τ ⊆ lvars_fv (dom Σ) ->
  formula_fv (denot_ty_lvar_gas gas (<[LVFree x := T]> Σ) τ e) ⊆
  world_dom (mx : WorldT).
Proof.
  intros HΣx He Hτ.
  transitivity (lvars_fv (dom Σ) ∪ fv_tm e ∪ fv_cty τ ∪ {[x]}).
  - apply formula_fv_denot_ty_lvar_gas_insert_fresh_upper.
  - intros a Ha.
    apply elem_of_union in Ha as [Ha | Ha].
    + apply elem_of_union in Ha as [Ha | Ha].
      * apply elem_of_union in Ha as [Ha | Ha].
        -- apply HΣx. apply elem_of_union_l. exact Ha.
        -- exact (He a Ha).
      * apply HΣx. apply elem_of_union_l. exact (Hτ a Ha).
    + apply HΣx. apply elem_of_union_r. exact Ha.
Qed.

End TypeDenotation.
