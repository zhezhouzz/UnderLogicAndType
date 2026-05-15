(** * ChoiceTyping.Soundness

    Soundness skeleton for the single declarative typing judgment. *)

From ChoiceTyping Require Export SoundnessHelpers.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  StrongNormalization.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma fundamental_sub_case
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ1 τ2 : choice_ty) :
  choice_typing_wf Σ Γ e τ2 →
  sub_type_under Σ Γ τ1 τ2 →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e) →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ2 e.
Proof.
  intros Hwf Hsub IH m HΓ.
  destruct Hsub as [_ [_ [_ Hent]]].
  pose proof (choice_typing_wf_fv_tm_subset Σ Γ e τ2 Hwf) as Hfv.
  pose proof (Hent e Hfv m HΓ) as Himpl.
  eapply res_models_impl_elim; [exact Himpl |].
  apply IH. exact HΓ.
Qed.

Lemma fundamental_sub_total_case
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ1 τ2 : choice_ty) :
  choice_typing_wf Σ Γ e τ2 →
  sub_type_under Σ Γ τ1 τ2 →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_in_ctx_under Σ Γ τ1 e) →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_in_ctx_under Σ Γ τ2 e).
Proof.
  intros Hwf Hsub IH m HΓ.
  destruct (IH m HΓ) as [Hτ1 Htotal].
  split.
  - eapply fundamental_sub_case; eauto.
    intros n Hn. exact (proj1 (IH n Hn)).
  - exact Htotal.
Qed.

(** The context-subtyping case of the fundamental theorem. *)
Lemma fundamental_ctx_sub_case
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ1 Γ2 : ctx) (e : tm) (τ : choice_ty) :
  ctx_sub_under Σ (fv_tm e ∪ fv_cty τ) Γ1 Γ2 →
  (denot_ctx_in_env Σ Γ2 ⊫ denot_ty_in_ctx_under Σ Γ2 τ e) →
  denot_ctx_in_env Σ Γ1 ⊫ denot_ty_in_ctx_under Σ Γ1 τ e.
Proof.
Admitted.

(** The variable case is exactly the singleton context denotation. *)
Lemma fundamental_var_case Σ (x : atom) (τ : choice_ty) :
  choice_typing_wf Σ (CtxBind x τ) (tret (vfvar x)) τ →
  denot_ctx_in_env Σ (CtxBind x τ) ⊫
    denot_ty_in_ctx_under Σ (CtxBind x τ) τ (tret (vfvar x)).
Proof.
  intros Hwf m Hctx.
  pose proof (denot_ctx_in_env_ctx Σ (CtxBind x τ) m Hctx) as Hbind.
  destruct Hwf as [Hwfτ _].
  pose proof (wf_choice_ty_under_ctx Σ (CtxBind x τ) τ Hwfτ) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ (CtxBind x τ) Hwfctx) as Hbasicctx.
  inversion Hbasicctx; subst; clear Hbasicctx.
  simpl in Hbind.
  unfold denot_ty_in_ctx_under, erase_ctx_under. simpl.
  replace (Σ ∪ {[x := erase_ty τ]}) with (<[x := erase_ty τ]> Σ).
  - exact Hbind.
  - apply (map_eq (M := gmap atom)). intros z.
    rewrite lookup_insert.
    destruct (decide (z = x)) as [->|Hzx].
    + rewrite decide_True by reflexivity.
      rewrite lookup_union_r.
      * rewrite lookup_singleton. rewrite decide_True by reflexivity. reflexivity.
      * apply not_elem_of_dom.
        match goal with
        | H : x ∉ dom Σ |- _ => exact H
        end.
    + rewrite decide_False by congruence.
      rewrite lookup_union.
      rewrite lookup_singleton. rewrite decide_False by congruence.
      destruct (Σ !! z); reflexivity.
Qed.

Lemma expr_total_on_ret_lc X v (m : WfWorld) :
  stale v ⊆ X →
  is_lc v →
  (∀ σ, (m : World) σ → lc_env (store_restrict σ X)) →
  expr_total_on X (tret v) m.
Proof.
  intros Hfv Hlc Henv.
  split; [simpl; exact Hfv |].
  intros σ Hσ.
  exists (m{store_restrict σ X} v).
  change (m{store_restrict σ X} (tret v) →* tret (m{store_restrict σ X} v)).
  rewrite msubst_ret.
  apply Steps_refl.
  constructor.
  apply msubst_lc; [apply Henv; exact Hσ | exact Hlc].
Qed.

Lemma fundamental_var_total_case Σ (x : atom) (τ : choice_ty) :
  choice_typing_wf Σ (CtxBind x τ) (tret (vfvar x)) τ →
  entails_total (denot_ctx_in_env Σ (CtxBind x τ))
    (denot_ty_total_in_ctx_under Σ (CtxBind x τ) τ (tret (vfvar x))).
Proof.
  intros Hwf m Hctx.
  assert (Hbasicctx : basic_ctx (dom Σ) (CtxBind x τ)).
  {
    destruct Hwf as [Hwfτ _].
    eapply wf_ctx_under_basic.
    eapply wf_choice_ty_under_ctx. exact Hwfτ.
  }
  split.
  - eapply fundamental_var_case; eauto.
  - eapply (expr_total_on_ret_lc
      (dom (erase_ctx_under Σ (CtxBind x τ))) (vfvar x) m).
    + change ({[x]} ⊆ dom (erase_ctx_under Σ (CtxBind x τ))).
      unfold erase_ctx_under. simpl.
      rewrite dom_union_L, dom_singleton_L. set_solver.
    + constructor.
    + intros σ Hσ.
      replace (dom (erase_ctx_under Σ (CtxBind x τ))) with (dom Σ ∪ {[x]}).
      * pose proof (denot_ctx_in_env_store_erased_lc
          Σ (CtxBind x τ) m σ Hbasicctx Hctx Hσ) as Hlc.
        simpl in Hlc. exact Hlc.
      * unfold erase_ctx_under. simpl.
        rewrite dom_union_L, dom_singleton_L. set_solver.
Qed.

Lemma fundamental_const_over_case Σ c :
  denot_ctx_in_env Σ CtxEmpty ⊫
    denot_ty_in_ctx_under Σ CtxEmpty
      (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
      (tret (vconst c)).
Proof.
Admitted.

Lemma fundamental_const_under_case Σ c :
  denot_ctx_in_env Σ CtxEmpty ⊫
    denot_ty_in_ctx_under Σ CtxEmpty
      (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
      (tret (vconst c)).
Proof.
Admitted.

(** Constants need the first value-adequacy lemma for the new
    basic-world-aware refinement denotation: evaluating [tret c] at a fresh
    result coordinate produces a singleton world satisfying the opened
    equality qualifier. *)
Lemma fundamental_const_case Σ c :
  denot_ctx_in_env Σ CtxEmpty ⊫
    denot_ty_in_ctx_under Σ CtxEmpty (const_precise_ty c) (tret (vconst c)).
Proof.
Admitted.

Lemma expr_total_on_ret_const X c m :
  expr_total_on X (tret (vconst c)) m.
Proof.
  split.
  - simpl. set_solver.
  - intros σ _.
    exists (vconst c).
    change (m{store_restrict σ X} (tret (vconst c)) →* tret (vconst c)).
    rewrite msubst_ret. simpl.
    rewrite (msubst_fresh (store_restrict σ X) (vconst c)) by set_solver.
    apply Steps_refl. constructor. constructor.
Qed.

Lemma fundamental_const_total_case Σ c :
  entails_total (denot_ctx_in_env Σ CtxEmpty)
    (denot_ty_total_in_ctx_under Σ CtxEmpty (const_precise_ty c) (tret (vconst c))).
Proof.
  intros m Hctx.
  split.
  - apply fundamental_const_case. exact Hctx.
  - apply expr_total_on_ret_const.
Qed.

Lemma choice_typing_wf_let_body Σ Γ e1 e2 τ :
  choice_typing_wf Σ Γ (tlete e1 e2) τ →
  body_tm e2.
Proof.
  intros [_ Herase].
  apply typing_tm_lc in Herase.
  apply lc_lete_iff_body in Herase as [_ Hbody].
  exact Hbody.
Qed.

Lemma choice_typing_wf_inter_l Σ Γ e τ1 τ2 :
  choice_typing_wf Σ Γ e (CTInter τ1 τ2) →
  choice_typing_wf Σ Γ e τ1.
Proof.
  intros [Hwf Herase].
  destruct Hwf as [Hctx Hbasic].
  inversion Hbasic; subst.
  split; [split; assumption | exact Herase].
Qed.

Lemma choice_typing_wf_inter_r Σ Γ e τ1 τ2 :
  choice_typing_wf Σ Γ e (CTInter τ1 τ2) →
  choice_typing_wf Σ Γ e τ2.
Proof.
  intros [Hwf Herase].
  destruct Hwf as [Hctx Hbasic].
  inversion Hbasic; subst.
  split.
  - split; assumption.
  - simpl in Herase.
    match goal with
    | H : erase_ty τ1 = erase_ty τ2 |- _ => rewrite H in Herase
    end.
    exact Herase.
Qed.

Lemma choice_typing_wf_union_l Σ Γ e τ1 τ2 :
  choice_typing_wf Σ Γ e (CTUnion τ1 τ2) →
  choice_typing_wf Σ Γ e τ1.
Proof.
  intros [Hwf Herase].
  destruct Hwf as [Hctx Hbasic].
  inversion Hbasic; subst.
  split; [split; assumption | exact Herase].
Qed.

Lemma choice_typing_wf_union_r Σ Γ e τ1 τ2 :
  choice_typing_wf Σ Γ e (CTUnion τ1 τ2) →
  choice_typing_wf Σ Γ e τ2.
Proof.
  intros [Hwf Herase].
  destruct Hwf as [Hctx Hbasic].
  inversion Hbasic; subst.
  split.
  - split; assumption.
  - simpl in Herase.
    match goal with
    | H : erase_ty τ1 = erase_ty τ2 |- _ => rewrite H in Herase
    end.
    exact Herase.
Qed.

Lemma choice_typing_wf_sum_l Σ Γ e τ1 τ2 :
  choice_typing_wf Σ Γ e (CTSum τ1 τ2) →
  choice_typing_wf Σ Γ e τ1.
Proof.
  intros [Hwf Herase].
  destruct Hwf as [Hctx Hbasic].
  inversion Hbasic; subst.
  split; [split; assumption | exact Herase].
Qed.

Lemma choice_typing_wf_sum_r Σ Γ e τ1 τ2 :
  choice_typing_wf Σ Γ e (CTSum τ1 τ2) →
  choice_typing_wf Σ Γ e τ2.
Proof.
  intros [Hwf Herase].
  destruct Hwf as [Hctx Hbasic].
  inversion Hbasic; subst.
  split.
  - split; assumption.
  - simpl in Herase.
    match goal with
    | H : erase_ty τ1 = erase_ty τ2 |- _ => rewrite H in Herase
    end.
    exact Herase.
Qed.

(** The semantic content of [T-Let].

    This is intentionally separated from [fundamental_let_case].  The typing
    case should only assemble the induction hypotheses; the hard work is the
    expression-result composition:

    - results of [e1] provide the let-bound coordinate;
    - the body theorem is used under the comma-extended context;
    - all resulting body outcomes are reassembled into the result set of
      [tlete e1 e2].

    This lemma is the right place to use [expr_result_in_world_let_intro] and
    the denotation compatibility lemmas.  It must not recurse on [τ2] locally;
    any structural recursion belongs in the general denotation-compatibility
    theorem. *)
Lemma semantic_let_rule (Φ : primop_ctx) Σ Γ τ1 τ2 e1 e2 (L : aset) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
  intros Hwf1 Hwf IH1 IH2.
  eapply denot_tlet_semantic; eauto.
Qed.

Lemma fundamental_let_case (Φ : primop_ctx) Σ Γ τ1 τ2 e1 e2 (L : aset) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
  intros Hwf1 Hwf IH1 IH2.
  eapply semantic_let_rule; eauto.
Qed.

Lemma semantic_total_let_rule (Φ : primop_ctx) Σ Γ τ1 τ2 e1 e2 (L : aset) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  (∀ x, x ∉ L →
    choice_typing_wf Σ (CtxComma Γ (CtxBind x τ1)) (e2 ^^ x) τ2) →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    entails_total (denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)))
      (denot_ty_total_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x))) →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_in_ctx_under Σ Γ τ2 (tlete e1 e2)).
Proof.
  intros Hwf1 Hwf Hbody_wf IH1 IH2 m Hm.
  apply total_model_to_total_denot.
  eapply (denot_tlet_total_semantic Σ Γ τ1 τ2 e1 e2 L).
  - exact (proj2 Hwf1).
  - exact (proj2 Hwf).
  - intros n Hn. eapply entails_total_to_total_model; eauto.
  - intros x HxL n Hn. eapply entails_total_to_total_model; eauto.
  - exact Hm.
Qed.

Lemma fundamental_total_let_case (Φ : primop_ctx) Σ Γ τ1 τ2 e1 e2 (L : aset) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  (∀ x, x ∉ L →
    choice_typing_wf Σ (CtxComma Γ (CtxBind x τ1)) (e2 ^^ x) τ2) →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    entails_total (denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)))
      (denot_ty_total_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x))) →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_in_ctx_under Σ Γ τ2 (tlete e1 e2)).
Proof.
  intros Hwf1 Hwf Hbody_wf IH1 IH2.
  eapply semantic_total_let_rule; eauto.
Qed.

Lemma fundamental_letd_case (Φ : primop_ctx) Σ Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
  choice_typing_wf Σ (CtxStar Γ1 Γ2) (tlete e1 e2) τ2 →
  (denot_ctx_in_env Σ Γ1 ⊫ denot_ty_in_ctx_under Σ Γ1 τ1 e1) →
  (∀ x, x ∉ L →
    denot_ctx_in_env Σ (CtxStar Γ2 (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ2 (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  denot_ctx_in_env Σ (CtxStar Γ1 Γ2) ⊫
    denot_ty_in_ctx_under Σ (CtxStar Γ1 Γ2) τ2 (tlete e1 e2).
Proof. Admitted.

Lemma fundamental_lam_case (Φ : primop_ctx) Σ Γ τx τ e (L : aset) :
  (∀ y, y ∉ L →
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind y τx)) ({0 ~> y} τ) (e ^^ y)) →
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTArrow τx τ) (tret (vlam (erase_ty τx) e)).
Proof. Admitted.

Lemma fundamental_lamd_case (Φ : primop_ctx) Σ Γ τx τ e (L : aset) :
  (∀ y, y ∉ L →
    denot_ctx_in_env Σ (CtxStar Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ (CtxBind y τx)) ({0 ~> y} τ) (e ^^ y)) →
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTWand τx τ) (tret (vlam (erase_ty τx) e)).
Proof. Admitted.

Lemma fundamental_app_case (Φ : primop_ctx) Σ Γ τx τ v1 x :
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ (CTArrow τx τ) (tret v1)) →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τx (tret (vfvar x))) →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof. Admitted.

Lemma fundamental_appd_case (Φ : primop_ctx) Σ Γ1 Γ2 τx τ v1 x :
  (denot_ctx_in_env Σ Γ1 ⊫ denot_ty_in_ctx_under Σ Γ1 (CTWand τx τ) (tret v1)) →
  (denot_ctx_in_env Σ Γ2 ⊫ denot_ty_in_ctx_under Σ Γ2 τx (tret (vfvar x))) →
  denot_ctx_in_env Σ (CtxStar Γ1 Γ2) ⊫
    denot_ty_in_ctx_under Σ (CtxStar Γ1 Γ2) ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof. Admitted.

Lemma fundamental_fix_case (Φ : primop_ctx) Σ Γ τx τ vf (L : aset) :
  (∀ y, y ∉ L →
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind y τx))
        (CTArrow (CTArrow τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) →
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTArrow τx τ)
      (tret (vfix (erase_ty (CTArrow τx τ)) vf)).
Proof. Admitted.

Lemma fundamental_fixd_case (Φ : primop_ctx) Σ Γ τx τ vf (L : aset) :
  (∀ y, y ∉ L →
    denot_ctx_in_env Σ (CtxStar Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ (CtxBind y τx))
        (CTWand (CTWand τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) →
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTWand τx τ)
      (tret (vfix (erase_ty (CTWand τx τ)) vf)).
Proof. Admitted.

Lemma fundamental_appop_case (Φ : primop_ctx) Σ Γ op x :
  wf_primop_sig op (Φ op) →
  choice_typing_wf Σ Γ
    (tprim op (vfvar x))
    ({0 ~> x} (primop_result_ty (Φ op))) →
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (primop_arg_ty (Φ op)) (tret (vfvar x))) →
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ ({0 ~> x} (primop_result_ty (Φ op))) (tprim op (vfvar x)).
Proof.
Admitted.

Lemma fundamental_match_both_case (Φ : primop_ctx) Σ Γt Γf v τt τf et ef :
  (denot_ctx_in_env Σ Γt ⊫ denot_ty_in_ctx_under Σ Γt (bool_precise_ty true) (tret v)) →
  (denot_ctx_in_env Σ Γf ⊫ denot_ty_in_ctx_under Σ Γf (bool_precise_ty false) (tret v)) →
  (denot_ctx_in_env Σ Γt ⊫ denot_ty_in_ctx_under Σ Γt τt et) →
  (denot_ctx_in_env Σ Γf ⊫ denot_ty_in_ctx_under Σ Γf τf ef) →
  denot_ctx_in_env Σ (CtxSum Γt Γf) ⊫
    denot_ty_in_ctx_under Σ (CtxSum Γt Γf) (CTSum τt τf) (tmatch v et ef).
Proof. Admitted.

Lemma fundamental_match_true_case (Φ : primop_ctx) Σ Γ v τ et ef :
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ (bool_precise_ty true) (tret v)) →
  branch_unreachable Σ Γ v false →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ et) →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ (tmatch v et ef).
Proof. Admitted.

Lemma fundamental_match_false_case (Φ : primop_ctx) Σ Γ v τ et ef :
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ (bool_precise_ty false) (tret v)) →
  branch_unreachable Σ Γ v true →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ ef) →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ (tmatch v et ef).
Proof. Admitted.

(** ** Fundamental theorem *)

Theorem Fundamental (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ : choice_ty) :
  wf_primop_ctx Φ →
  has_choice_type Φ Σ Γ e τ →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ e.
Proof.
  intros HΦ Hty.
  induction Hty.
  - eapply fundamental_var_case; eauto 6.
  - eapply fundamental_const_case; eauto 6.
  - eapply fundamental_sub_case; eauto 6.
  - eapply fundamental_ctx_sub_case; eauto 6.
  - eapply fundamental_let_case; eauto 6 using typing_wf_under.
  - eapply fundamental_letd_case; eauto 6.
  - eapply fundamental_lam_case; eauto 6.
  - eapply fundamental_lamd_case; eauto 6.
  - eapply fundamental_app_case; eauto 6.
  - eapply fundamental_appd_case; eauto 6.
  - eapply fundamental_fix_case; eauto 6.
  - eapply fundamental_fixd_case; eauto 6.
  - eapply fundamental_appop_case; eauto 6.
  - eapply fundamental_match_both_case; eauto 6.
  - eapply fundamental_match_true_case; eauto 6.
  - eapply fundamental_match_false_case; eauto 6.
Qed.

(** ** Corollaries

    The theorem statements follow the single typing judgment.  The proof
    bodies remain as admitted skeletons while the definition layer is being
    aligned with the paper. *)

Corollary safety (Φ : primop_ctx) (e : tm) (b : base_ty) :
  wf_primop_ctx Φ →
  has_choice_type Φ ∅ CtxEmpty e (CTOver b qual_top) →
  ∀ e', steps e e' → is_val e' ∨ ∃ e'', step e' e''.
Proof. Admitted.

Corollary coverage (Φ : primop_ctx) (e : tm) (b : base_ty) :
  wf_primop_ctx Φ →
  has_choice_type Φ ∅ CtxEmpty e (CTUnder b qual_top) →
  ∃ v, steps e (tret v).
Proof. Admitted.

Corollary refinement (Φ : primop_ctx) (e : tm) (b : base_ty) (φ : type_qualifier) :
  wf_primop_ctx Φ →
  has_choice_type Φ ∅ CtxEmpty e (CTOver b φ) →
  ∀ v, steps e (tret v) →
       ∃ x, qual_interp {[x := v]} (φ ^q^ x).
Proof. Admitted.

Corollary incorrectness (Φ : primop_ctx) (e : tm) (b : base_ty) (φ : type_qualifier) :
  wf_primop_ctx Φ →
  has_choice_type Φ ∅ CtxEmpty e (CTUnder b φ) →
  ∃ v x, steps e (tret v) ∧ qual_interp {[x := v]} (φ ^q^ x).
Proof. Admitted.

Corollary exact_result (Φ : primop_ctx) (e : tm) (b : base_ty) (c : constant) :
  wf_primop_ctx Φ →
  has_choice_type Φ ∅ CtxEmpty e (CTUnder b (b0:c= c)) →
  steps e (tret (vconst c)).
Proof. Admitted.
