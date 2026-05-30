(** * ContextTyping.TLet

    Fresh-name helpers, regularity facts, and the direct TLet bridge to the
    denotational TLet theorem. *)

From CoreLang Require Import BasicTyping Instantiation InstantiationProps.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermTLet Qualifier BasicTypingFormula.
From Denotation Require Import Context ContextTypeDenotationSaturate TLet.
From ContextTyping Require Export Typing.

(** * ContextTyping.Naming

    Small proof-layer helpers for binder representatives.  These definitions
    keep the tlet proofs from repeatedly rebuilding the same freshness,
    context-domain, and open/substitution side conditions. *)


(** ** Fresh representatives for tlet body binders *)

Definition tlet_fresh_avoid
    (L X : aset) (τ : context_ty) (e : tm) (m : WfWorldT) : aset :=
  L ∪ world_dom (m : WorldT) ∪ X ∪ fv_cty τ ∪ fv_tm e.

Record tlet_fresh_name
    (L X : aset) (τ : context_ty) (e : tm) (m : WfWorldT) (x : atom) : Prop := {
  tlet_fresh_notin_L : x ∉ L;
  tlet_fresh_notin_world : x ∉ world_dom (m : WorldT);
  tlet_fresh_notin_body : x ∉ X ∪ fv_cty τ ∪ fv_tm e;
}.

Lemma tlet_fresh_name_for
    L X τ e (m : WfWorldT) :
  tlet_fresh_name L X τ e m
    (fresh_for (tlet_fresh_avoid L X τ e m)).
Proof.
  pose proof (fresh_for_not_in (tlet_fresh_avoid L X τ e m)) as Hfresh.
  constructor; unfold tlet_fresh_avoid in Hfresh; set_solver.
Qed.

(** A lighter variant for totality lemmas that only mention a body term, not a
    result refinement type. *)

Definition body_fresh_avoid
    (L X : aset) (e : tm) (m : WfWorldT) : aset :=
  L ∪ world_dom (m : WorldT) ∪ X ∪ fv_tm e.

Record body_fresh_name
    (L X : aset) (e : tm) (m : WfWorldT) (x : atom) : Prop := {
  body_fresh_notin_L : x ∉ L;
  body_fresh_notin_world : x ∉ world_dom (m : WorldT);
  body_fresh_notin_X : x ∉ X;
  body_fresh_notin_fv_tm : x ∉ fv_tm e;
}.

Lemma body_fresh_name_for
    L X e (m : WfWorldT) :
  body_fresh_name L X e m
    (fresh_for (body_fresh_avoid L X e m)).
Proof.
  pose proof (fresh_for_not_in (body_fresh_avoid L X e m)) as Hfresh.
  constructor; unfold body_fresh_avoid in Hfresh; set_solver.
Qed.

Ltac pick_tlet_fresh x L X τ e m :=
  let Hfresh := fresh "Hfresh" in
  set (x := fresh_for (tlet_fresh_avoid L X τ e m));
  pose proof (tlet_fresh_name_for L X τ e m) as Hfresh;
  change (tlet_fresh_name L X τ e m x) in Hfresh.

Ltac pick_body_fresh x L X e m :=
  let Hfresh := fresh "Hfresh" in
  set (x := fresh_for (body_fresh_avoid L X e m));
  pose proof (body_fresh_name_for L X e m) as Hfresh;
  change (body_fresh_name L X e m x) in Hfresh.

(** ** Context binder normal forms *)

Lemma erase_ctx_under_comma_bind_dom_nf Σ Γ x τ :
  dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ))) =
  dom (erase_ctx_under Σ Γ) ∪ {[x]}.
Proof.
  unfold erase_ctx_under.
  cbn [erase_ctx].
  apply set_eq. intros z. split.
  - intros Hz.
    apply elem_of_dom in Hz as [T Hz].
    apply map_lookup_union_Some_raw in Hz as [HzΣ|[HΣ Hzrest]].
    + apply elem_of_union_l. apply elem_of_dom. exists T.
      apply map_lookup_union_Some_raw. left. exact HzΣ.
    + apply map_lookup_union_Some_raw in Hzrest as [HzΓ|[_ Hzx]].
      * apply elem_of_union_l. apply elem_of_dom. exists T.
        apply map_lookup_union_Some_raw. right. eauto.
      * cbv [map_singleton singleton singletonM insert map_insert] in Hzx.
        destruct (decide (z = x)) as [->|Hzx_ne]; [set_solver|].
        change ((partial_alter (λ _ : option ty, Some (erase_ty τ))
          x (∅ : gmap atom ty)) !! z = Some T) in Hzx.
        rewrite (lookup_partial_alter_ne (K := atom) (M := gmap atom)) in Hzx
          by congruence.
        rewrite lookup_empty in Hzx. discriminate.
  - intros Hz.
    apply elem_of_union in Hz as [Hz|Hz].
    + apply elem_of_dom in Hz as [T Hz].
      apply elem_of_dom.
      apply map_lookup_union_Some_raw in Hz as [HzΣ|[HΣ HzΓ]].
      * exists T. apply map_lookup_union_Some_raw. left. exact HzΣ.
      * exists T. apply map_lookup_union_Some_raw. right.
        split; [exact HΣ|]. apply map_lookup_union_Some_raw. left. exact HzΓ.
    + apply elem_of_singleton in Hz. subst z.
      destruct (Σ !! x) as [TΣ|] eqn:HΣ.
      * apply elem_of_dom. exists TΣ.
        apply map_lookup_union_Some_raw. left. exact HΣ.
      * destruct (erase_ctx Γ !! x) as [TΓ|] eqn:HΓ.
        -- apply elem_of_dom. exists TΓ.
           apply map_lookup_union_Some_raw. right. split; [exact HΣ|].
           apply map_lookup_union_Some_raw. left. exact HΓ.
        -- apply elem_of_dom. exists (erase_ty τ).
           apply map_lookup_union_Some_raw. right. split; [exact HΣ|].
           apply map_lookup_union_Some_raw. right.
           split.
           ++ exact HΓ.
           ++ cbv [map_singleton singleton singletonM insert map_insert].
              change ((partial_alter (λ _ : option ty, Some (erase_ty τ))
                x (∅ : gmap atom ty)) !! x = Some (erase_ty τ)).
              rewrite (lookup_partial_alter_eq (K := atom) (M := gmap atom)).
              reflexivity.
Qed.

Lemma erase_ctx_under_comma_bind_env_fresh Σ Γ x τ :
  x ∉ dom (erase_ctx_under Σ Γ) →
  erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)) =
  <[x := erase_ty τ]> (erase_ctx_under Σ Γ).
Proof.
  intros Hfresh.
  unfold erase_ctx_under in *.
  cbn [erase_ctx] in *.
  assert (HxΣ : x ∉ dom Σ).
  { better_set_solver. }
  assert (HxΓ : x ∉ dom (erase_ctx Γ)).
  { better_set_solver. }
  change (Σ ∪ ((erase_ctx Γ : gmap atom ty) ∪
      ({[x := erase_ty τ]} : gmap atom ty)) =
    <[x := erase_ty τ]> (Σ ∪ erase_ctx Γ)).
  replace ((erase_ctx Γ : gmap atom ty) ∪
      ({[x := erase_ty τ]} : gmap atom ty))
    with (<[x := erase_ty τ]> (erase_ctx Γ : gmap atom ty)).
  2:{
    symmetry.
    apply (storeA_union_singleton_insert_fresh
      (V := ty) (K := atom) (erase_ctx Γ : gmap atom ty)
      x (erase_ty τ)).
    exact HxΓ.
  }
  change (Σ ∪ (<[x := erase_ty τ]> (erase_ctx Γ : gmap atom ty) :
      gmap atom ty) =
    <[x := erase_ty τ]> (Σ ∪ erase_ctx Γ)).
  apply (storeA_insert_union_r_fresh (V := ty) (K := atom)
    (Σ : gmap atom ty) (erase_ctx Γ : gmap atom ty)
    x (erase_ty τ)).
  exact HxΣ.
Qed.

Lemma erase_ctx_under_dom_basic Σ Γ :
  basic_ctx (dom Σ) Γ →
  dom (erase_ctx_under Σ Γ) = dom Σ ∪ ctx_dom Γ.
Proof.
  intros Hbasic.
  unfold erase_ctx_under.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ Hbasic) as HdomΓ.
  better_set_solver.
Qed.

Ltac ctx_name_norm :=
  repeat match goal with
  | H : context[dom (erase_ctx_under ?Σ (CtxComma ?Γ (CtxBind ?x ?τ)))] |- _ =>
      rewrite (erase_ctx_under_comma_bind_dom_nf Σ Γ x τ) in H
  | |- context[dom (erase_ctx_under ?Σ (CtxComma ?Γ (CtxBind ?x ?τ)))] =>
      rewrite (erase_ctx_under_comma_bind_dom_nf Σ Γ x τ)
  | Hfresh : ?x ∉ dom (erase_ctx_under ?Σ ?Γ),
    H : context[erase_ctx_under ?Σ (CtxComma ?Γ (CtxBind ?x ?τ))] |- _ =>
      rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ x τ Hfresh) in H
  | Hfresh : ?x ∉ dom (erase_ctx_under ?Σ ?Γ)
      |- context[erase_ctx_under ?Σ (CtxComma ?Γ (CtxBind ?x ?τ))] =>
      rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ x τ Hfresh)
  end.

(** * ContextTyping.RegularDenotation

    Prop-level regularity and totality around context-type denotation.

    The context-type denotation formulas intentionally stay semantic.  The
    typing proof, however, often needs the regularity facts that the paper keeps
    implicit: the context is basic, and the type is basic in the erased context.
    This file packages those facts outside the logic, so we do not encode
    naming or well-formedness as logic atoms. *)


Definition denot_ty_regular_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) : Prop :=
  basic_ctx (dom Σ) Γ ∧ basic_context_ty (dom (erase_ctx_under Σ Γ)) τ.

Definition denot_ty_total_model_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) (e : tm)
    (m : WfWorldT) : Prop :=
  denot_ty_regular_in_ctx_under Σ Γ τ ∧
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ∧
  m ⊨ expr_total_formula e.

Definition total_model_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) (e : tm) : Prop :=
  ∀ m,
    m ⊨ denot_ctx_under Σ Γ →
    denot_ty_total_model_in_ctx_under Σ Γ τ e m.

Lemma denot_ty_total_model_regular Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  denot_ty_regular_in_ctx_under Σ Γ τ.
Proof. intros [H _]. exact H. Qed.

Lemma denot_ty_total_model_basic_ctx Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  basic_ctx (dom Σ) Γ.
Proof. intros [[H _] _]. exact H. Qed.

Lemma denot_ty_total_model_formula Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e.
Proof. intros [_ [H _]]. exact H. Qed.

Lemma denot_ty_total_model_total Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  m ⊨ expr_total_formula e.
Proof. intros [_ [_ H]]. exact H. Qed.

Lemma total_model_to_total_denot Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  denot_ty_total_in_ctx_under Σ Γ τ e m.
Proof.
  intros.
  split.
  - eauto 6 using denot_ty_total_model_formula.
  - eauto 6 using denot_ty_total_model_total.
Qed.

Lemma total_model_of_total_denot Σ Γ τ e m :
  basic_ctx (dom Σ) Γ →
  basic_context_ty (dom (erase_ctx_under Σ Γ)) τ →
  denot_ty_total_in_ctx_under Σ Γ τ e m →
  denot_ty_total_model_in_ctx_under Σ Γ τ e m.
Proof.
  intros Hctx Hτ [Hden Htotal].
  split.
  - split; assumption.
  - split; assumption.
Qed.

Lemma context_typing_wf_from_erased_basic Σ Γ e τ m :
  basic_ctx (dom Σ) Γ →
  context_ty_wf_for_ctx Σ Γ τ →
  m ⊨ denot_ctx_under Σ Γ →
  erase_ctx_under Σ Γ ⊢ₑ e ⋮ erase_ty τ →
  context_typing_wf Σ Γ e τ.
Proof.
  intros Hctx Hτ Hm Herase.
  constructor.
  - split; [exact Hctx|]. exists m. exact Hm.
  - exact Hτ.
  - exact Herase.
Qed.

Lemma denot_ty_total_model_context_typing_wf Σ Γ e τ m :
  context_ty_wf_for_ctx Σ Γ τ →
  erase_ctx_under Σ Γ ⊢ₑ e ⋮ erase_ty τ →
  m ⊨ denot_ctx_under Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  context_typing_wf Σ Γ e τ.
Proof.
  intros Hτ Herase Hctx Hmodel.
  eapply context_typing_wf_from_erased_basic; eauto.
  exact (denot_ty_total_model_basic_ctx Σ Γ τ e m Hmodel).
Qed.

Lemma context_typing_wf_regular_denotation Σ Γ e τ :
  context_typing_wf Σ Γ e τ →
  denot_ty_regular_in_ctx_under Σ Γ τ.
Proof.
  intros Hwf.
  split.
  - exact (wf_ctx_under_basic Σ Γ
      (wf_context_ty_under_ctx Σ Γ τ
        (context_typing_wf_wf_context_ty_under Σ Γ e τ Hwf))).
  - exact (context_typing_wf_basic_context_ty_erased Σ Γ e τ Hwf).
Qed.

Lemma context_typing_wf_to_total_model Σ Γ e τ m :
  context_typing_wf Σ Γ e τ →
  denot_ty_total_in_ctx_under Σ Γ τ e m →
  denot_ty_total_model_in_ctx_under Σ Γ τ e m.
Proof.
  intros Hwf Htotal.
  eapply total_model_of_total_denot; eauto.
  - exact (proj1 (context_typing_wf_regular_denotation Σ Γ e τ Hwf)).
  - exact (proj2 (context_typing_wf_regular_denotation Σ Γ e τ Hwf)).
Qed.

Lemma entails_total_to_total_model Σ Γ e τ :
  context_typing_wf Σ Γ e τ →
  entails_total (denot_ctx_under Σ Γ)
    (denot_ty_total_in_ctx_under Σ Γ τ e) →
  total_model_in_ctx_under Σ Γ τ e.
Proof.
  intros Hwf Hent m Hm.
  apply context_typing_wf_to_total_model; eauto 6.
Qed.

(** * ContextTyping.TLetDirect

    The new TLet bridge is intentionally a one-hop wrapper around
    [Denotation.TLet.tlet_intro_denotation].  It does not depend on the old
    continuation/reduction helper stack. *)


Lemma denot_tlet_direct_in_ctx
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : context_ty) e1 e2
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom) :
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 ->
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 ->
  expr_result_extension_witness e1 x Fx ->
  m ⊨ expr_total_formula e1 ->
  m ⊨ basic_world_formula
        (denot_relevant_env (atom_env_to_lty_env (erase_ctx_under Σ Γ))
          τ2 (tlete e1 e2)) ->
  x ∉ dom (erase_ctx_under Σ Γ) ->
  LVFree x ∉ dom (atom_env_to_lty_env (erase_ctx_under Σ Γ)) ∪
    context_ty_lvars τ2 ->
  res_extend_by m Fx mx ->
  mx ⊨ denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1))
          τ2 (e2 ^^ x) ->
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
  intros He1 Hlet HFx Htotal Hworld Hxfresh Hxlvar Hext Hbody.
  unfold denot_ty_in_ctx_under, denot_ty in Hbody |- *.
  rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ x τ1 Hxfresh) in Hbody.
  replace (atom_env_to_lty_env (<[x := erase_ty τ1]> (erase_ctx_under Σ Γ)))
    with (<[LVFree x := erase_ty τ1]>
      (atom_env_to_lty_env (erase_ctx_under Σ Γ))) in Hbody.
  2:{ symmetry. apply atom_store_to_lvar_store_insert. }
  eapply tlet_intro_denotation; eauto.
  - apply atom_store_to_lvar_store_closed.
  - rewrite lvar_store_to_atom_store_atom_store. exact He1.
  - rewrite lvar_store_to_atom_store_atom_store. exact Hlet.
Qed.

Lemma denot_tlet_direct_total_model_in_ctx
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : context_ty) e1 e2
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom) :
  denot_ty_total_model_in_ctx_under Σ Γ τ1 e1 m ->
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 ->
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 ->
  expr_result_extension_witness e1 x Fx ->
  m ⊨ basic_world_formula
        (denot_relevant_env (atom_env_to_lty_env (erase_ctx_under Σ Γ))
          τ2 (tlete e1 e2)) ->
  x ∉ dom (erase_ctx_under Σ Γ) ->
  LVFree x ∉ dom (atom_env_to_lty_env (erase_ctx_under Σ Γ)) ∪
    context_ty_lvars τ2 ->
  res_extend_by m Fx mx ->
  mx ⊨ denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1))
          τ2 (e2 ^^ x) ->
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
  intros Hmodel He1 Hlet HFx Hworld Hxfresh Hxlvar Hext Hbody.
  eapply denot_tlet_direct_in_ctx; eauto.
  exact (denot_ty_total_model_total Σ Γ τ1 e1 m Hmodel).
Qed.

(** * ContextTyping.TLetDenotation

    Compatibility names for the ContextTyping TLet case.

    The old version of this file routed through totality, expression
    continuations, and reduction helpers.  The new route is deliberately thin:
    the proof-facing bridge is [denot_tlet_direct_in_ctx], which directly calls
    [Denotation.TLet.tlet_intro_denotation]. *)


Lemma denot_tlet_semantic_direct
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : context_ty) e1 e2
    (m mx : WfWorld (V := value)) (Fx : fiber_extension (V := value))
    (x : atom) :
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 ->
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 ->
  expr_result_extension_witness e1 x Fx ->
  m ⊨ expr_total_formula e1 ->
  m ⊨ basic_world_formula
        (denot_relevant_env (atom_env_to_lty_env (erase_ctx_under Σ Γ))
          τ2 (tlete e1 e2)) ->
  x ∉ dom (erase_ctx_under Σ Γ) ->
  LVFree x ∉ dom (atom_env_to_lty_env (erase_ctx_under Σ Γ)) ∪
    context_ty_lvars τ2 ->
  res_extend_by m Fx mx ->
  mx ⊨ denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1))
          τ2 (e2 ^^ x) ->
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
  eapply denot_tlet_direct_in_ctx.
Qed.

(** The old [denot_tlet_semantic] shape quantified over context entailments and
    internally constructed the result extension.  Reintroducing that exact
    surface should be a small wrapper over [denot_tlet_direct_in_ctx], but it is
    intentionally not rebuilt through the old helper stack. *)
