(** * ContextTyping.SoundnessFixApply

    Applying the opened Fix body arrow to the recursive self value. *)

From Stdlib Require Import Lia.
From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  TypeEquivCore
  TypeEquivTerm
  TypeEquivFiberBase
  TypeEquivFiberTransport
  TypeEquivBody
  TypeEquivArrow
  TypeEquivWand
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing SoundnessLam SoundnessFixBase
  SoundnessFixOpen.

Local Ltac fix_apply_build_union :=
  first
    [ assumption
    | apply elem_of_union_l; fix_apply_build_union
    | apply elem_of_union_r; fix_apply_build_union
    | apply elem_of_singleton_2; reflexivity ].

Local Ltac fix_apply_notin_union :=
  let Hbad := fresh "Hbad" in
  intros Hbad;
  match goal with
  | H : ?x ∉ _ |- False =>
      apply H; fix_apply_build_union
  end.

Local Lemma fix_apply_fresh_erase_ctx_from_fix_union
    (Σ : tyctx) Γ y A B C :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ A ∪ B ∪ C ->
  y ∉ dom (erase_ctx Γ).
Proof.
  intros Hy.
  eapply ctx_erasure_under_notin_erase_ctx.
  intros Hyctx.
  apply Hy.
  apply elem_of_union_l.
  apply elem_of_union_l.
  apply elem_of_union_l.
  apply elem_of_union_r.
  exact Hyctx.
Qed.

Lemma fix_body_arrow_outer_value_open
    (Σ : tyctx) Γ τx τ vf b (t : ty)
    (my : WfWorldT) y :
  context_typing_wf Σ
    (CtxComma Γ (CtxBind y τx))
    (tret ({0 ~> vfvar y} vf))
    (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ)) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas
    (cty_depth (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ)))
    (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ)))
    (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
    (tret ({0 ~> vfvar y} vf)) ->
  exists (z : atom) (mz : WfWorldT) (Fz : FiberExtensionT),
    z ∉ world_dom (my : WorldT) ∪ lvars_fv (dom
      ((relevant_env
        (<[LVFree y := erase_ty τx]>
          (atom_env_to_lty_env (erase_ctx Γ)))
        (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) : lty_env)) ∪
      fv_value vf ∪ fv_cty τx ∪ fv_cty τ ∪ {[y]} /\
    world_dom (mz : WorldT) = world_dom (my : WorldT) ∪ {[z]} /\
    res_restrict mz (world_dom (my : WorldT)) = my /\
    res_extend_by my Fz mz /\
    mz ⊨ expr_result_formula (tret ({0 ~> vfvar y} vf)) (LVFree z) /\
    mz ⊨ formula_open 0 z
      (arrow_value_denote_gas
        (Nat.max (cty_depth (fix_rec_call_ty b y τx τ))
          (cty_depth ({0 ~> y} τ)))
        (typed_lty_env_bind
          (relevant_env
            (<[LVFree y := erase_ty τx]>
              (atom_env_to_lty_env (erase_ctx Γ)))
            (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
            (tret ({0 ~> vfvar y} vf)))
          (erase_ty (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))))
        (cty_shift 0 (fix_rec_call_ty b y τx τ))
        (cty_shift 1 ({0 ~> y} τ))
        (tret (vbvar 0))).
Proof.
  intros Hbody_wf Hy Hbody_den.
  set (Δy := <[LVFree y := erase_ty τx]>
    (atom_env_to_lty_env (erase_ctx Γ))).
  set (τself := fix_rec_call_ty b y τx τ).
  set (τres := cty_open 0 y τ).
  set (body := open_value 0 (vfvar y) vf).
  set (Σrel := relevant_env Δy (CTArrow τself τres) (tret body)).
  assert (Hlc_body : lc_value body).
  {
    subst body τself τres.
    eapply context_typing_wf_ret_lc_value. exact Hbody_wf.
  }
  assert (Hbody_fv_my : fv_tm (tret body) ⊆ world_dom (my : WorldT)).
  { eapply ty_denote_gas_fv_tm_subset. exact Hbody_den. }
  cbn [cty_depth ty_denote_gas] in Hbody_den.
  rewrite res_models_and_iff in Hbody_den.
  destruct Hbody_den as [Hguard_body Hbody_outer].
  set (z := fresh_for
    (world_dom (my : WorldT) ∪ lvars_fv (dom Σrel) ∪
      fv_value vf ∪ fv_cty τx ∪ fv_cty τ ∪ {[y]})).
  assert (Hzfresh :
      z ∉ world_dom (my : WorldT) ∪ lvars_fv (dom Σrel) ∪
        fv_value vf ∪ fv_cty τx ∪ fv_cty τ ∪ {[y]}).
  { subst z. apply fresh_for_not_in. }
  assert (Hzmy : z ∉ world_dom (my : WorldT)).
  { clear -Hzfresh. better_set_solver. }
  assert (HzΣrel : z ∉ lvars_fv (dom Σrel)).
  { clear -Hzfresh. better_set_solver. }
  assert (Hzbody : z ∉ fv_value body).
  {
    subst body.
    pose proof (open_fv_value vf (vfvar y) 0) as Hopen.
    cbn [fv_value] in Hopen.
    intros Hzbody.
    apply Hopen in Hzbody.
    cbn [fv_value] in Hzbody.
    clear -Hzfresh Hzbody. better_set_solver.
  }
  destruct (expr_result_extension_witness_on_exists
    (world_dom (my : WorldT)) (tret body) z Hbody_fv_my
    ltac:(clear -Hzfresh; better_set_solver)) as [Fz HFz].
  destruct (expr_result_extension_witness_on_shape _ _ _ _ HFz)
    as [HFz_in HFz_out].
  unfold ext_in, ext_out in HFz_in, HFz_out.
  assert (Happz : extension_applicable Fz my).
  {
    constructor.
    - rewrite HFz_in. set_solver.
    - rewrite HFz_out. clear -Hzmy. set_solver.
  }
  destruct (res_extend_by_exists my Fz Happz) as [mz Hextz].
  assert (Hmz_dom :
      world_dom (mz : WorldT) = world_dom (my : WorldT) ∪ {[z]}).
  {
    pose proof (res_extend_by_dom my Fz mz Hextz) as Hdom.
    rewrite Hdom, HFz_out. reflexivity.
  }
  assert (Hmz_restrict :
      res_restrict mz (world_dom (my : WorldT)) = my).
  { exact (res_extend_by_restrict_base my Fz mz Hextz). }
  pose proof (res_models_forall_open_named_fresh
    my mz z
    (FImpl
      (expr_result_formula_at (lvars_shift_from 0 (dom Σrel))
        (tm_shift 0 (tret body)) (LVBound 0))
      (arrow_value_denote_gas
        (Nat.max (cty_depth τself) (cty_depth τres))
        (typed_lty_env_bind Σrel (erase_ty (CTArrow τself τres)))
        (cty_shift 0 τself) (cty_shift 1 τres) (tret (vbvar 0))))
    Hbody_outer Hzmy Hmz_dom Hmz_restrict) as Houter_open.
  cbn [formula_open] in Houter_open.
  assert (Hzero_body :
      my ⊨ ty_denote_gas 0 Δy (CTArrow τself τres) (tret body)).
  {
    apply ty_denote_gas_zero_of_guard_formula.
    subst Σrel. exact Hguard_body.
  }
  assert (Htotal_body : expr_total_on_atom_world (tret body) my).
  { eapply ty_denote_gas_zero_total_atom_world. exact Hzero_body. }
  assert (Hres_at :
      mz ⊨ expr_result_formula_at (dom Σrel) (tret body) (LVFree z)).
  {
    eapply expr_result_formula_at_of_result_extends_on_coarsen
      with (X := world_dom (my : WorldT)) (F := Fz) (m := my).
    - subst Σrel. apply relevant_env_closed.
      subst Δy. apply lty_env_closed_insert_free.
      apply atom_store_to_lvar_store_closed.
    - pose proof Hguard_body as Hguard_parts.
      unfold ty_guard_formula in Hguard_parts.
      repeat rewrite res_models_and_iff in Hguard_parts.
      destruct Hguard_parts as [_ [_ [Hbasic _]]].
      apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
      rewrite (tm_lvars_lc_eq_atoms (tret body)).
      + eapply basic_tm_has_ltype_lvars. exact Hty.
      + constructor. exact Hlc_body.
    - pose proof Hguard_body as Hguard_parts.
      unfold ty_guard_formula in Hguard_parts.
      repeat rewrite res_models_and_iff in Hguard_parts.
      destruct Hguard_parts as [_ [Hworld [_ _]]].
      apply basic_world_formula_models_iff in Hworld as [HlcD [HdomD _]].
      intros v Hv.
      destruct v as [k|a].
      + exfalso. exact (HlcD (LVBound k) Hv).
      + unfold lvars_of_atoms. apply elem_of_map.
        exists a. split; [reflexivity|].
        apply HdomD. apply lvars_fv_elem. exact Hv.
    - unfold lvars_of_atoms. intros HzD.
      apply elem_of_map in HzD as [a [Ha HaD]].
      inversion Ha. subst a.
      exact (Hzmy HaD).
    - set_solver.
    - exact HFz.
    - exact Hextz.
    - exact Htotal_body.
  }
  assert (Hres_open :
      mz ⊨ formula_open 0 z
        (expr_result_formula_at (lvars_shift_from 0 (dom Σrel))
          (tm_shift 0 (tret body)) (LVBound 0))).
  {
    subst Σrel.
    eapply result_first_outer_result_ret_value_at_open.
    - subst Δy. apply lty_env_closed_insert_free.
      apply atom_store_to_lvar_store_closed.
    - exact Hlc_body.
    - exact Hzbody.
    - exact HzΣrel.
    - exact Hres_at.
  }
  pose proof (res_models_impl_elim _ _ _ Houter_open Hres_open)
    as Hvalue.
  assert (Hres_plain :
      mz ⊨ expr_result_formula (tret body) (LVFree z)).
  {
    unfold expr_result_formula.
    eapply expr_result_formula_at_of_result_extends_on_coarsen
      with (X := world_dom (my : WorldT)) (F := Fz) (m := my).
    - rewrite (tm_lvars_lc_eq_atoms (tret body)).
      + unfold lvars_of_atoms. intros v Hv.
        apply elem_of_map in Hv as [a [Ha _]]. inversion Ha. exact I.
      + constructor. exact Hlc_body.
    - reflexivity.
    - rewrite (tm_lvars_lc_eq_atoms (tret body)).
      + unfold lvars_of_atoms. intros v Hv.
        apply elem_of_map in Hv as [a [Ha HaIn]].
        inversion Ha. subst v.
        apply elem_of_map. exists a. split; [reflexivity|].
        apply Hbody_fv_my. exact HaIn.
      + constructor. exact Hlc_body.
    - unfold lvars_of_atoms. intros HzD.
      apply elem_of_map in HzD as [a [Ha HaD]].
      inversion Ha. subst a.
      exact (Hzmy HaD).
    - set_solver.
    - exact HFz.
    - exact Hextz.
    - exact Htotal_body.
  }
  exists z, mz, Fz.
  split; [exact Hzfresh|].
  split; [exact Hmz_dom|].
  split; [exact Hmz_restrict|].
  split; [exact Hextz|].
  split; [exact Hres_plain|].
  exact Hvalue.
Qed.

Lemma fix_body_arrow_apply_self
    (Σ : tyctx) Γ τx τ vf b t
    (my : WfWorldT) y :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  (context_typing_wf Σ
      (CtxComma Γ (CtxBind y τx))
      (tret ({0 ~> vfvar y} vf))
      (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ->
  my ⊨ ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
    (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
    (tret ({0 ~> vfvar y} vf)) ->
  my ⊨ ty_denote_gas (cty_depth (fix_rec_call_ty b y τx τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (fix_rec_call_ty b y τx τ)
      (tret (vfix (TBase b →ₜ t) vf)) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
      (tapp_tm (tret (open_value 0 (vfvar y) vf))
        (vfix (TBase b →ₜ t) vf)).
Proof.
  (* Result-first Arrow denotation adds an outer function-result binder
     before the old argument binder. The old proof below opened the body
     arrow directly at the recursive self argument. The replacement proof
     should first bind the opened body value itself, then reuse the old
     recursive-self application argument inside [arrow_value_denote_gas]. *)
Admitted.
