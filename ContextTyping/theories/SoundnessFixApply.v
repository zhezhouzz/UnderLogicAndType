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
  DenotationSetMapFacts
  ResultFirstOpen
  TypeEquivCore
  TypeEquivTerm
  TypeEquivFiberBase
  TypeEquivFiberTransport
  TypeEquivBody
  TypeEquivArrow
  TypeEquivWand
  TypeEquiv
  TypePersistArrow
  ConstDenote.
From ContextTyping Require Import Typing SoundnessLamBase SoundnessLamArrow
  SoundnessLamWand SoundnessFixBase
  SoundnessFixOpen.

Local Lemma fix_apply_open_value_fresh vf y z :
  z ∉ fv_value vf ∪ {[y]} ->
  z ∉ fv_value (open_value 0 (vfvar y) vf).
Proof.
  intros Hfresh Hbad.
  pose proof (open_fv_value vf (vfvar y) 0) as Hopen.
  cbn [fv_value] in Hopen.
  apply Hopen in Hbad.
  cbn [fv_value] in Hbad.
  clear -Hfresh Hbad. set_solver.
Qed.

Local Lemma fix_apply_open_cty_fresh τ y z :
  z ∉ fv_cty τ ∪ {[y]} ->
  z ∉ fv_cty (cty_open 0 y τ).
Proof.
  intros Hfresh Hbad.
  pose proof (cty_open_fv_subset 0 y τ) as Hsub.
  apply Hsub in Hbad.
  clear -Hfresh Hbad. set_solver.
Qed.

Local Lemma fix_apply_fix_rec_call_ty_fresh b y τx τ z :
  z ∉ fv_cty τx ∪ fv_cty τ ∪ {[y]} ->
  z ∉ fv_cty (fix_rec_call_ty b y τx τ).
Proof.
  intros Hfresh Hbad.
  pose proof (fv_cty_fix_rec_call_ty_subset b y τx τ) as Hsub.
  apply Hsub in Hbad.
  clear -Hfresh Hbad. set_solver.
Qed.

Local Lemma fix_apply_vfix_fresh b t vf z :
  z ∉ fv_value vf ->
  z ∉ fv_value (vfix (TBase b →ₜ t) vf).
Proof.
  intros Hfresh. cbn [fv_value]. exact Hfresh.
Qed.

Local Lemma fix_apply_bind_lvar_env_dom_subset
    (Σ : tyctx) Γ y τx :
  y ∉ dom (erase_ctx Γ) ->
  dom (<[LVFree y := erase_ty τx]>
    (atom_env_to_lty_env (erase_ctx Γ))) ⊆
  dom (atom_env_to_lty_env
    (ctx_erasure_under Σ (CtxComma Γ (CtxBind y τx)))).
Proof.
  intros HyΓ v Hv.
  rewrite dom_insert_L in Hv.
  rewrite !atom_store_to_lvar_store_dom.
  apply elem_of_union in Hv as [Hyv|HΓv].
  - apply elem_of_singleton in Hyv. subst v.
    unfold lvars_of_atoms. apply elem_of_map. exists y.
    split; [reflexivity|].
    eapply ctx_erasure_under_erase_ctx_dom_subset.
    rewrite erase_ctx_comma_bind_dom. clear -HyΓ. set_solver.
  - rewrite atom_store_to_lvar_store_dom in HΓv.
    unfold lvars_of_atoms in HΓv.
    apply elem_of_map in HΓv as [a [Hv_eq HaΓ]]. subst v.
    unfold lvars_of_atoms. apply elem_of_map. exists a.
    split; [reflexivity|].
    eapply ctx_erasure_under_erase_ctx_dom_subset.
    rewrite erase_ctx_comma_bind_dom. clear -HaΓ. set_solver.
Qed.

Local Lemma fix_apply_relevant_lvars_tapp_values_fresh
    τ body self z :
  z ∉ fv_cty τ ->
  z ∉ fv_value body ->
  z ∉ fv_value self ->
  LVFree z ∉ relevant_lvars τ (tapp_tm (tret body) self).
Proof.
  intros Hzτ Hzbody Hzself Hbad.
  apply lvars_fv_elem in Hbad.
  rewrite relevant_lvars_fv in Hbad.
  rewrite fv_tapp_tm in Hbad.
  cbn [fv_tm fv_value] in Hbad.
  clear -Hzτ Hzbody Hzself Hbad. set_solver.
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
    mz ⊨ arrow_value_denote_gas
        (Nat.max (cty_depth (fix_rec_call_ty b y τx τ))
          (cty_depth ({0 ~> y} τ)))
        (<[LVFree z :=
            erase_ty (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))]>
          (relevant_env
            (<[LVFree y := erase_ty τx]>
              (atom_env_to_lty_env (erase_ctx Γ)))
            (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
            (tret ({0 ~> vfvar y} vf))))
        (fix_rec_call_ty b y τx τ)
        ({0 ~> y} τ)
        (tret (vfvar z)).
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
  assert (Hτself_lc : lc_context_ty τself).
  {
    subst τself τres.
    pose proof (context_typing_wf_context_ty
      Σ (CtxComma Γ (CtxBind y τx)) (tret ({0 ~> vfvar y} vf))
      (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ)) Hbody_wf)
      as Hwf_ty.
    cbn [wf_context_ty_at] in Hwf_ty.
    destruct Hwf_ty as [Hτself_wf _].
    eapply wf_context_ty_at_lc. exact Hτself_wf.
  }
  assert (Hτres_lc1 : cty_lc_at 1 τres).
  {
    subst τself τres.
    pose proof (context_typing_wf_context_ty
      Σ (CtxComma Γ (CtxBind y τx)) (tret ({0 ~> vfvar y} vf))
      (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ)) Hbody_wf)
      as Hwf_ty.
    cbn [wf_context_ty_at] in Hwf_ty.
    destruct Hwf_ty as [_ Hτres_wf].
    eapply wf_context_ty_at_lc. exact Hτres_wf.
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
  assert (HzΣrel_free : LVFree z ∉ dom Σrel).
  {
    intros Hin. apply HzΣrel.
    apply lvars_fv_elem. exact Hin.
  }
  assert (Hzτself : z ∉ fv_cty τself).
  { subst τself. apply fix_apply_fix_rec_call_ty_fresh. clear -Hzfresh. set_solver. }
  assert (Hzτres : z ∉ fv_cty τres).
  { subst τres. apply fix_apply_open_cty_fresh. clear -Hzfresh. set_solver. }
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
  pose proof (res_extend_by_singleton_output_open_world
    my mz Fz z Hextz HFz_out) as [Hmz_dom Hmz_restrict].
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
	    eapply expr_result_formula_at_env_of_result_extends_from_ty_guard_on.
	    - exact HFz.
	    - exact Hextz.
	    - subst Σrel. exact Hguard_body.
	  }
  pose proof (res_models_forall_open_named_fresh
    my mz z _ Hbody_outer Hzmy Hmz_dom Hmz_restrict) as Hbody_open.
  cbn [formula_open] in Hbody_open.
	  rewrite (formula_open_result_first_expr_result_formula_at_shift0
	    z (dom Σrel) (tret body)) in Hbody_open.
	  2:{ subst Σrel. apply relevant_env_closed.
	      subst Δy. apply lty_env_closed_insert_free.
	      apply atom_store_to_lvar_store_closed. }
	  2:{ exact HzΣrel. }
	  2:{ constructor. exact Hlc_body. }
	  2:{ cbn [fv_tm fv_value]. exact Hzbody. }
	  pose proof (res_models_impl_elim _ _ _ Hbody_open Hres_at) as Hvalue.
	  assert (Hres_plain :
	      mz ⊨ expr_result_formula (tret body) (LVFree z)).
	  {
	    eapply expr_result_formula_of_result_extends_on_from_ty_guard.
	    - exact HFz.
	    - exact Hextz.
	    - subst Σrel. exact Hguard_body.
	  }
  exists z, mz, Fz.
  split; [exact Hzfresh|].
  split; [exact Hmz_dom|].
  split; [exact Hmz_restrict|].
  split; [exact Hextz|].
  split; [exact Hres_plain|].
  change (mz ⊨ formula_open 0 z
    (arrow_value_denote_gas_with ty_denote_gas
      (Nat.max (cty_depth τself) (cty_depth τres))
      (typed_lty_env_bind Σrel (erase_ty (CTArrow τself τres)))
      (cty_shift 0 τself) (cty_shift 1 τres)
      (tret (vbvar 0)))) in Hvalue.
  rewrite (formula_open_result_first_arrow_value_ret_bvar0
      (Nat.max (cty_depth τself) (cty_depth τres)) Σrel
      τself τres (erase_ty (CTArrow τself τres)) z) in Hvalue.
  2:{
    subst Σrel. apply relevant_env_closed.
    subst Δy. apply lty_env_closed_insert_free.
    apply atom_store_to_lvar_store_closed.
  }
  2:{ exact HzΣrel_free. }
  2:{ exact Hτself_lc. }
  2:{ exact Hτres_lc1. }
  2:{ exact Hzτself. }
  2:{ exact Hzτres. }
  subst τself τres body Σrel Δy.
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
  intros Hτx Hτ Hwf Hbody_wf Hy Hctx_comma Hbody_arrow Hself.
  set (Δy := <[LVFree y := erase_ty τx]>
    (atom_env_to_lty_env (erase_ctx Γ))).
  set (τself := fix_rec_call_ty b y τx τ).
  set (τres := cty_open 0 y τ).
  set (body := open_value 0 (vfvar y) vf).
  set (self := vfix (TBase b →ₜ t) vf).
  set (gas := Nat.max (cty_depth τself) (cty_depth τres)).
  assert (HyΓ : y ∉ dom (erase_ctx Γ)).
  { eapply soundness_fresh_erase_ctx_from_context_union; eauto. }
  assert (Hbody_mid :
      my ⊨ ty_denote_gas (cty_depth (CTArrow τself τres))
        Δy (CTArrow τself τres) (tret body)).
  {
    subst Δy τself τres body.
    eapply ty_denote_under_comma_bind_to_lvar_insert.
    - exact HyΓ.
    - exact Hbody_arrow.
  }
  assert (Hτself_lc : lc_context_ty τself).
  {
    pose proof (context_typing_wf_context_ty
      Σ (CtxComma Γ (CtxBind y τx)) (tret body)
      (CTArrow τself τres) ltac:(subst body τself τres; exact Hbody_wf))
      as Hwf_ty.
    cbn [wf_context_ty_at] in Hwf_ty.
    destruct Hwf_ty as [Hτself_wf _].
    eapply wf_context_ty_at_lc. exact Hτself_wf.
  }
  assert (Hτres_lc1 : cty_lc_at 1 τres).
  {
    pose proof (context_typing_wf_context_ty
      Σ (CtxComma Γ (CtxBind y τx)) (tret body)
      (CTArrow τself τres) ltac:(subst body τself τres; exact Hbody_wf))
      as Hwf_ty.
    cbn [wf_context_ty_at] in Hwf_ty.
    destruct Hwf_ty as [_ Hτres_wf].
    eapply wf_context_ty_at_lc. exact Hτres_wf.
  }
  assert (Hτres_lc0 : lc_context_ty τres).
  {
    subst τres.
    pose proof (context_typing_wf_context_ty
      Σ Γ (tret self) (CTArrow τx τ) ltac:(subst self; exact Hwf))
      as Hwf_ty.
    cbn [wf_context_ty_at] in Hwf_ty.
    destruct Hwf_ty as [_ Hτ_wf].
    eapply wf_context_ty_at_lc.
    eapply wf_context_ty_at_open_at.
    - exact HyΓ.
    - exact Hτ_wf.
  }
  destruct (fix_body_arrow_outer_value_open
    Σ Γ τx τ vf b t my y Hbody_wf Hy Hbody_mid)
    as (z & mz & Fz & Hzfresh & Hmz_dom & Hmz_restrict &
        Hextz & Hres_body_z & Hvalue_z).
  set (Σrel := relevant_env Δy (CTArrow τself τres) (tret body)).
  assert (Hzτself : z ∉ fv_cty τself).
  {
    subst τself. apply fix_apply_fix_rec_call_ty_fresh.
    clear -Hzfresh. set_solver.
  }
  assert (Hzτres : z ∉ fv_cty τres).
  {
    subst τres. apply fix_apply_open_cty_fresh.
    clear -Hzfresh. set_solver.
  }
  assert (Hzbody : z ∉ fv_value body).
  {
    subst body. apply fix_apply_open_value_fresh.
    clear -Hzfresh. set_solver.
  }
  assert (Hzself : z ∉ fv_value self).
  {
    subst self. apply fix_apply_vfix_fresh.
    clear -Hzfresh. set_solver.
  }
  assert (Hle_my_mz : my ⊑ mz).
  { rewrite <- Hmz_restrict. apply res_restrict_le. }
  assert (Hself_mz :
      mz ⊨ ty_denote_gas (cty_depth τself) Δy τself (tret self)).
  { eapply res_models_kripke; [exact Hle_my_mz|exact Hself]. }
  assert (Hself_fv_mz : fv_tm (tret self) ⊆ world_dom (mz : WorldT)).
  { eapply ty_denote_gas_fv_tm_subset. exact Hself_mz. }
  set (w := fresh_for
    (world_dom (mz : WorldT) ∪ lvars_fv (dom Δy) ∪
      lvars_fv (dom Σrel) ∪ fv_value vf ∪ fv_cty τx ∪
      fv_cty τ ∪ {[y; z]})).
  assert (Hwfresh :
      w ∉ world_dom (mz : WorldT) ∪ lvars_fv (dom Δy) ∪
        lvars_fv (dom Σrel) ∪ fv_value vf ∪ fv_cty τx ∪
        fv_cty τ ∪ {[y; z]}).
  { subst w. apply fresh_for_not_in. }
  assert (Hwz : w <> z) by (clear -Hwfresh; set_solver).
  assert (Hw_mz : w ∉ world_dom (mz : WorldT)).
  { clear -Hwfresh. better_set_solver. }
  assert (HwΔ : LVFree w ∉ dom Δy).
  { intros Hbad. apply Hwfresh. apply lvars_fv_elem in Hbad.
    clear -Hbad. better_set_solver. }
  assert (HwΣrel : LVFree w ∉ dom Σrel).
  { intros Hbad. apply Hwfresh. apply lvars_fv_elem in Hbad.
    clear -Hbad. better_set_solver. }
  assert (Hwτself : w ∉ fv_cty τself).
  {
    subst τself. apply fix_apply_fix_rec_call_ty_fresh.
    clear -Hwfresh. set_solver.
  }
  assert (Hwτres : w ∉ fv_cty τres).
  {
    subst τres. apply fix_apply_open_cty_fresh.
    clear -Hwfresh. set_solver.
  }
  assert (Hwbody : w ∉ fv_value body).
  {
    subst body. apply fix_apply_open_value_fresh.
    clear -Hwfresh. set_solver.
  }
  assert (Hwself : w ∉ fv_value self).
  {
    subst self. apply fix_apply_vfix_fresh.
    clear -Hwfresh. set_solver.
  }
  assert (HΔ_ctx :
      dom Δy ⊆
      dom (atom_env_to_lty_env
        (ctx_erasure_under Σ (CtxComma Γ (CtxBind y τx))))).
  { subst Δy. apply fix_apply_bind_lvar_env_dom_subset. exact HyΓ. }
  assert (HzΔ : LVFree z ∉ dom Δy).
  {
    intros HzΔ.
    pose proof (ctx_denote_under_basic_world
      Σ (CtxComma Γ (CtxBind y τx)) my Hctx_comma) as Hworld_ctx.
    apply basic_world_formula_models_iff in Hworld_ctx
      as [_ [Hscope_ctx _]].
    assert (Hz_world : z ∈ world_dom (my : WorldT)).
    {
      apply Hscope_ctx.
      apply lvars_fv_elem.
      apply HΔ_ctx. exact HzΔ.
    }
    apply Hzfresh.
    clear -Hz_world. set_solver.
  }
  destruct (expr_result_extension_witness_exists
    (tret self) w Hwself) as [Fw HFw].
  assert (Happw : extension_applicable Fw mz).
  {
    destruct HFw as [_ [HFw_in HFw_out] _].
    constructor.
    - unfold ext_in in HFw_in. rewrite HFw_in. exact Hself_fv_mz.
    - unfold ext_out in HFw_out. rewrite HFw_out. clear -Hw_mz. set_solver.
  }
  destruct (res_extend_by_exists mz Fw Happw) as [mw Hextw].
  pose proof HFw as HFw_shape_src.
  destruct HFw_shape_src as [_ [_ HFw_out] _].
  unfold ext_out in HFw_out.
  pose proof (res_extend_by_singleton_output_open_world
    mz mw Fw w Hextw HFw_out) as [Hmw_dom Hmw_restrict].
  assert (Hres_self_w :
      mw ⊨ expr_result_formula (tret self) (LVFree w)).
  {
    pose proof (ty_denote_gas_guard _ _ _ _ _ Hself_mz) as Hguard.
    eapply expr_result_formula_of_result_extends_from_ty_guard; eauto.
  }
  assert (Hself_w :
      mw ⊨ ty_denote_gas gas
        (<[LVFree w := erase_ty τself]> Δy)
        τself (tret (vfvar w))).
  {
    subst gas.
    rewrite (ty_denote_gas_saturate
      (Nat.max (cty_depth τself) (cty_depth τres))
      (<[LVFree w := erase_ty τself]> Δy)
      τself (tret (vfvar w))) by lia.
    eapply (ty_denote_gas_result_ext (cty_depth τself)
      Δy τself (tret self) w mz mw Fw).
    - subst Δy. apply lty_env_closed_insert_free.
      apply atom_store_to_lvar_store_closed.
    - exact HwΔ.
    - exact HFw.
    - exact Hextw.
    - exact Hself_mz.
  }
  cbn [formula_open arrow_value_denote_gas arrow_value_denote_gas_with]
    in Hvalue_z.
  pose proof (res_models_forall_open_named_fresh
    mz mw w _ Hvalue_z Hw_mz Hmw_dom Hmw_restrict) as Hinner.
  cbn [formula_open] in Hinner.
  assert (Harg_open :
      mw ⊨ formula_open 0 w
        (ty_denote_gas gas
          (typed_lty_env_bind
            (<[LVFree z := erase_ty (CTArrow τself τres)]> Σrel)
            (erase_ty τself))
          (cty_shift 0 τself) (tret (vbvar 0)))).
  {
    rewrite (formula_open_ty_denote_gas_bind_ret_bvar0
      w gas (<[LVFree z := erase_ty (CTArrow τself τres)]> Σrel)
      τself).
    - eapply res_models_ty_denote_gas_env_agree_on
        with (Σ1 := <[LVFree w := erase_ty τself]> Δy)
          (X := relevant_lvars τself (tret (vfvar w))).
      + reflexivity.
      + rewrite lty_env_insert_free_commute by
          (clear -Hwfresh; set_solver).
        assert (Hz_rel_arg :
            LVFree z ∉ relevant_lvars τself (tret (vfvar w))).
        {
          intros Hbad. apply lvars_fv_elem in Hbad.
          rewrite relevant_lvars_fv in Hbad.
          cbn [fv_tm fv_value] in Hbad.
          clear -Hzτself Hwfresh Hbad. better_set_solver.
        }
        rewrite (lty_env_restrict_lvars_insert_fresh
          (<[LVFree w := erase_ty τself]> Σrel)
          (relevant_lvars τself (tret (vfvar w))) z
          (erase_ty (CTArrow τself τres)) Hz_rel_arg).
        symmetry.
        apply lam_lty_env_restrict_result_first_arg_eq.
        * exact Hτself_lc.
        * clear -Hwbody Hwτself Hwτres. better_set_solver.
      + exact Hself_w.
    - apply lty_env_closed_insert_free.
      subst Σrel. apply relevant_env_closed.
      subst Δy. apply lty_env_closed_insert_free.
      apply atom_store_to_lvar_store_closed.
    - rewrite dom_insert_L. intros Hin.
      apply elem_of_union in Hin as [Hin|Hin].
      + apply elem_of_singleton in Hin.
        injection Hin as Hzw.
        exact (Hwz Hzw).
      + clear -HwΣrel Hin. apply HwΣrel. exact Hin.
    - exact Hwτself.
    - exact Hτself_lc.
  }
  pose proof (res_models_impl_elim _ _ _ Hinner Harg_open) as Hres_raw.
  assert (Hres_src :
      mw ⊨ ty_denote_gas gas
        (<[LVFree w := erase_ty τself]>
          (<[LVFree z := erase_ty (CTArrow τself τres)]> Δy))
        τres (tapp_tm (tret (vfvar z)) (vfvar w))).
  {
    change (mw ⊨ formula_open 0 w
      (ty_denote_gas gas
        (typed_lty_env_bind
          (<[LVFree z := erase_ty (CTArrow τself τres)]> Σrel)
          (erase_ty τself))
        τres (tapp_tm (tm_shift 0 (tret (vfvar z))) (vbvar 0))))
      in Hres_raw.
    rewrite (formula_open_ty_denote_gas_bind_tapp_shift_bvar0
      w gas (<[LVFree z := erase_ty (CTArrow τself τres)]> Σrel)
      τres (erase_ty τself) (tret (vfvar z)))
      in Hres_raw.
    2:{ apply lty_env_closed_insert_free.
        subst Σrel. apply relevant_env_closed.
        subst Δy. apply lty_env_closed_insert_free.
        apply atom_store_to_lvar_store_closed. }
    2:{
      rewrite dom_insert_L. intros Hin.
      apply elem_of_union in Hin as [Hin|Hin].
      - apply elem_of_singleton in Hin.
        injection Hin as Hzw.
        exact (Hwz Hzw).
      - clear -HwΣrel Hin. apply HwΣrel. exact Hin.
    }
    2:{ cbn [fv_tm fv_value]. clear -Hwz. set_solver. }
    2:{ exact Hwτres. }
    2:{ repeat constructor. }
    rewrite (cty_open_above_lc_fresh 0 0 w τres) in Hres_raw
      by (lia || exact Hτres_lc0 || exact Hwτres).
    eapply res_models_ty_denote_gas_env_agree_on
      with (Σ1 := <[LVFree w := erase_ty τself]>
          (<[LVFree z := erase_ty (CTArrow τself τres)]> Σrel))
        (X := relevant_lvars τres
          (tapp_tm (tret (vfvar z)) (vfvar w))).
    - reflexivity.
    - rewrite (lty_env_insert_free_commute Δy w z
        (erase_ty τself) (erase_ty (CTArrow τself τres)))
        by (clear -Hwfresh; set_solver).
      symmetry.
      apply lam_lty_env_restrict_result_first_result_closed_eq.
      + subst Δy. apply lty_env_closed_insert_free.
        apply atom_store_to_lvar_store_closed.
      + exact Hτres_lc0.
      + clear -Hwfresh. set_solver.
      + exact Hwτres.
      + clear -Hzbody Hzτself Hzτres. set_solver.
    - exact Hres_raw.
  }
  assert (Hstatic_target :
      mw ⊨ ty_static_guard_formula
        (<[LVFree w := erase_ty τself]>
          (<[LVFree z := erase_ty (CTArrow τself τres)]> Δy))
        τres (tapp_tm (tret body) self)).
  {
    assert (Hstatic_my :
        my ⊨ ty_static_guard_formula Δy τres
          (tapp_tm (tret body) self)).
    {
      subst Δy τres body self.
      eapply fix_unfolded_app_static_guard_full; eauto.
    }
    assert (Hle_mz_mw : mz ⊑ mw).
    { rewrite <- Hmw_restrict. apply res_restrict_le. }
    assert (Hle_my_mw : my ⊑ mw).
    { etransitivity; [exact Hle_my_mz|exact Hle_mz_mw]. }
    assert (Hstatic_my_mw :
        mw ⊨ ty_static_guard_formula Δy τres
          (tapp_tm (tret body) self)).
    { eapply res_models_kripke; [exact Hle_my_mw|exact Hstatic_my]. }
    assert (Hstatic_body_mw :
        mw ⊨ ty_static_guard_formula Δy
          (CTArrow τself τres) (tret body)).
    {
      eapply res_models_kripke; [exact Hle_my_mw|].
      subst Δy τself τres body.
      eapply context_typing_wf_denot_static_guard_comma_bind_insert;
        eauto.
    }
    pose proof (ty_static_guard_basic_world Δy
      (CTArrow τself τres) (tret body) mw Hstatic_body_mw)
      as Hworld_Δ.
    assert (Hbasic_body :
        mw ⊨ expr_basic_typing_formula Δy (tret body)
          (erase_ty (CTArrow τself τres))).
    {
      unfold ty_static_guard_formula in Hstatic_body_mw.
      repeat rewrite res_models_and_iff in Hstatic_body_mw.
      tauto.
    }
    assert (Hres_body_z_mw :
        mw ⊨ expr_result_formula (tret body) (LVFree z)).
    { eapply res_models_kripke; [exact Hle_mz_mw|exact Hres_body_z]. }
    pose proof (basic_world_insert_result_alias
      Δy (erase_ty (CTArrow τself τres)) (tret body) z mw
      HzΔ Hres_body_z_mw Hworld_Δ Hbasic_body) as Hworld_z.
    assert (Hzrel :
        LVFree z ∉ relevant_lvars τres (tapp_tm (tret body) self)).
    { exact (fix_apply_relevant_lvars_tapp_values_fresh
        τres body self z Hzτres Hzbody Hzself). }
    pose proof (ty_static_guard_insert_irrelevant
      Δy τres (tapp_tm (tret body) self)
      z (erase_ty (CTArrow τself τres)) mw
      HzΔ Hzrel Hworld_z Hstatic_my_mw) as Hstatic_z.
    assert (Hbasic_self_z :
        mw ⊨ expr_basic_typing_formula
          (<[LVFree z := erase_ty (CTArrow τself τres)]> Δy)
          (tret self) (erase_ty τself)).
    {
      pose proof (ty_denote_gas_guard _ _ _ _ _ Hself_mz)
        as Hguard_self.
      assert (Hguard_self_mw :
          mw ⊨ ty_guard_formula (relevant_env Δy τself (tret self))
            τself (tret self)).
      { eapply res_models_kripke; [exact Hle_mz_mw|exact Hguard_self]. }
      unfold ty_guard_formula in Hguard_self_mw.
      repeat rewrite res_models_and_iff in Hguard_self_mw.
      destruct Hguard_self_mw as [_ [_ [Hbasic_self_rel _]]].
      apply expr_basic_typing_formula_models_iff in Hbasic_self_rel
        as [_ [_ Hty_self_rel]].
      apply expr_basic_typing_formula_models_iff.
      apply basic_world_formula_models_iff in Hworld_z
        as [Hlc_z [Hscope_z _]].
      split; [exact Hlc_z|]. split; [exact Hscope_z|].
      eapply basic_tm_has_ltype_weaken; [exact Hty_self_rel|].
      apply map_subseteq_spec. intros v T Hv.
      unfold relevant_env, lty_env_restrict_lvars in Hv.
      apply storeA_restrict_lookup_some in Hv as [_ Hv].
      destruct (decide (v = LVFree z)) as [->|Hne].
      - exfalso. apply HzΔ. apply elem_of_dom. eauto.
      - rewrite lookup_insert_ne by (symmetry; exact Hne). exact Hv.
    }
    assert (Hw_zΔ :
        LVFree w ∉ dom
          (<[LVFree z := erase_ty (CTArrow τself τres)]> Δy)).
    {
      rewrite dom_insert_L.
      clear -HwΔ Hwfresh. set_solver.
    }
    pose proof (basic_world_insert_result_alias
      (<[LVFree z := erase_ty (CTArrow τself τres)]> Δy)
      (erase_ty τself) (tret self) w mw
      Hw_zΔ Hres_self_w Hworld_z Hbasic_self_z) as Hworld_w.
    assert (Hwrel :
        LVFree w ∉ relevant_lvars τres (tapp_tm (tret body) self)).
    { exact (fix_apply_relevant_lvars_tapp_values_fresh
        τres body self w Hwτres Hwbody Hwself). }
    exact (ty_static_guard_insert_irrelevant
      (<[LVFree z := erase_ty (CTArrow τself τres)]> Δy)
      τres (tapp_tm (tret body) self)
      w (erase_ty τself) mw
      Hw_zΔ Hwrel Hworld_w Hstatic_z).
  }
  assert (Hlc_body : lc_value body).
  {
    subst body τself τres.
    eapply context_typing_wf_ret_lc_value. exact Hbody_wf.
  }
  assert (Hlc_self : lc_value self).
  {
    subst self.
    apply lc_ret_iff_value.
    eapply context_typing_wf_lc_tm. exact Hwf.
  }
  assert (Hz_alias_dom :
      LVFree z ∈ dom
        (<[LVFree w := erase_ty τself]>
          (<[LVFree z := erase_ty (CTArrow τself τres)]> Δy))).
  {
    rewrite !dom_insert_L.
    apply elem_of_union_r.
    apply elem_of_union_l.
    apply elem_of_singleton. reflexivity.
  }
  assert (Hw_alias_dom :
      LVFree w ∈ dom
        (<[LVFree w := erase_ty τself]>
          (<[LVFree z := erase_ty (CTArrow τself τres)]> Δy))).
  {
    rewrite dom_insert_L.
    apply elem_of_union_l.
    apply elem_of_singleton. reflexivity.
  }
  assert (Hres_body_z_mw_alias :
      mw ⊨ expr_result_formula (tret body) (LVFree z)).
  {
    eapply res_models_kripke; [|exact Hres_body_z].
    rewrite <- Hmw_restrict. apply res_restrict_le.
  }
  pose proof (ty_denote_gas_tapp_fun_arg_result_alias_from_static
    gas
    (<[LVFree w := erase_ty τself]>
      (<[LVFree z := erase_ty (CTArrow τself τres)]> Δy))
    τres body self z w mw
    Hz_alias_dom
    Hw_alias_dom
    Hlc_body Hlc_self
    Hres_body_z_mw_alias
    Hres_self_w Hstatic_target Hres_src) as Htarget_mw.
  assert (Htarget_mz :
      mz ⊨ ty_denote_gas gas
        (<[LVFree z := erase_ty (CTArrow τself τres)]> Δy)
        τres (tapp_tm (tret body) self)).
  {
    eapply ty_denote_gas_drop_fresh_ext
      with (mx := mw) (Fx := Fw); eauto.
    - pose proof (ty_static_guard_fv_subset _ _ _ _ Hstatic_target)
        as Hfv_mw.
      intros a Ha.
      specialize (Hfv_mw a Ha).
      rewrite Hmw_dom in Hfv_mw.
      apply elem_of_union in Hfv_mw as [Ha_mz|Ha_w]; [exact Ha_mz|].
      apply elem_of_singleton in Ha_w. subst a.
      apply elem_of_union in Ha as [Ha_tm|Ha_ty].
      + rewrite fv_tapp_tm in Ha_tm.
        cbn [fv_tm fv_value] in Ha_tm.
        clear -Hwbody Hwself Ha_tm. set_solver.
      + clear -Hwτres Ha_ty. set_solver.
    - rewrite dom_insert_L.
      intros Hin.
      apply elem_of_union in Hin as [Hin|Hin].
      + apply elem_of_singleton in Hin.
        injection Hin as Hzw.
        exact (Hwz Hzw).
      + exact (HwΔ Hin).
    - intros Hbad. apply Hwτres. apply lvars_fv_elem. exact Hbad.
    - rewrite fv_tapp_tm. cbn [fv_tm fv_value].
      clear -Hwbody Hwself. set_solver.
  }
  assert (Htarget_my :
      my ⊨ ty_denote_gas gas Δy τres (tapp_tm (tret body) self)).
  {
    eapply ty_denote_gas_drop_fresh_ext
      with (mx := mz) (Fx := Fz).
    - pose proof (ty_denote_gas_guard _ _ _ _ _ Htarget_mz)
        as Hguard_mz.
      pose proof (ty_denote_gas_zero_of_guard
        (<[LVFree z := erase_ty (CTArrow τself τres)]> Δy)
        τres (tapp_tm (tret body) self) mz Hguard_mz)
        as Hzero_mz.
      pose proof (ty_denote_gas_zero_relevant_lvars_world
        (<[LVFree z := erase_ty (CTArrow τself τres)]> Δy)
        τres (tapp_tm (tret body) self) mz Hzero_mz)
        as Hfv_mz.
      intros a Ha.
      assert (Ha_rel :
          a ∈ lvars_fv
            (context_ty_lvars τres ∪
             tm_lvars (tapp_tm (tret body) self))).
      {
        rewrite lvars_fv_union.
        apply elem_of_union in Ha as [Ha_tm|Ha_ty].
        - apply elem_of_union_r.
          rewrite tm_lvars_fv. exact Ha_tm.
        - apply elem_of_union_l.
          rewrite context_ty_lvars_fv. exact Ha_ty.
      }
      specialize (Hfv_mz a Ha_rel).
      rewrite Hmz_dom in Hfv_mz.
      apply elem_of_union in Hfv_mz as [Ha_my|Ha_z]; [exact Ha_my|].
      apply elem_of_singleton in Ha_z. subst a.
      apply elem_of_union in Ha as [Ha_tm|Ha_ty].
      + rewrite fv_tapp_tm in Ha_tm.
        cbn [fv_tm fv_value] in Ha_tm.
        clear -Hzbody Hzself Ha_tm. set_solver.
      + clear -Hzτres Ha_ty. set_solver.
    - exact HzΔ.
    - intros Hbad.
      apply lvars_fv_elem in Hbad.
      rewrite context_ty_lvars_fv in Hbad.
      clear -Hzτres Hbad. set_solver.
    - rewrite fv_tapp_tm. cbn [fv_tm fv_value].
      clear -Hzbody Hzself. set_solver.
    - exact Hextz.
    - exact Htarget_mz.
  }
  subst gas Δy τself τres body self.
  rewrite ty_denote_gas_saturate by cty_depth_solve.
  rewrite ty_denote_gas_saturate in Htarget_my by cty_depth_solve.
  exact Htarget_my.
Qed.
