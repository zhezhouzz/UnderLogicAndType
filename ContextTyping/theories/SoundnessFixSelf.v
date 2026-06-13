(** * ContextTyping.SoundnessFixSelf

    Recursive-self support for the Fix Fundamental case. *)

From Stdlib Require Import Lia Logic.Classical.
From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  TypeEquivCore
  TypeEquivBody
  TypeEquivArrow
  TypeEquivWand
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing SoundnessLam SoundnessFixBase
  SoundnessFixOpen SoundnessFixApply.

Local Ltac fix_self_in_union :=
  first
    [ assumption
    | apply elem_of_union_l; fix_self_in_union
    | apply elem_of_union_r; fix_self_in_union
    | apply elem_of_singleton_2; reflexivity ].

Local Ltac fix_self_break_union H :=
  repeat match type of H with
  | _ ∈ _ ∪ _ => apply elem_of_union in H as [H | H]
  | _ ∈ {[ _ ]} => apply elem_of_singleton in H; subst
  end.

Local Ltac fix_self_notin_union :=
  let Hbad := fresh "Hbad" in
  intros Hbad;
  fix_self_break_union Hbad;
  match type of Hbad with
  | ?x ∈ _ =>
    match goal with
    | H : x ∉ _ |- False =>
      apply H; fix_self_in_union
    end
  end.

Lemma fix_self_rec_call_zero
    (Σ : tyctx) Γ τx τ vf b t (my : WfWorldT) y :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  context_typing_wf Σ
    (CtxComma Γ (CtxBind y τx))
    (tret ({0 ~> vfvar y} vf))
    (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ)) ->
  y ∉ dom (ctx_erasure_under Σ Γ) ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ->
  my ⊨ ty_denote_gas 0
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (fix_rec_call_ty b y τx τ)
    (tret (vfix (TBase b →ₜ t) vf)).
Proof.
  intros Hτx Hτ Hwf Hbody_wf Hy Hctx.
  assert (HyΓ : y ∉ dom (erase_ctx Γ)).
  { eapply ctx_erasure_under_notin_erase_ctx. exact Hy. }
  assert (Hself_wf :
      context_typing_wf Σ
        (CtxComma Γ (CtxBind y τx))
        (tret (vfix (TBase b →ₜ t) vf))
        (fix_rec_call_ty b y τx τ)).
  {
    unfold context_typing_wf.
    split.
    - exact (context_typing_wf_ctx Σ
        (CtxComma Γ (CtxBind y τx))
        (tret ({0 ~> vfvar y} vf))
        (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
        Hbody_wf).
    - split.
      + pose proof (context_typing_wf_context_ty Σ
          (CtxComma Γ (CtxBind y τx))
          (tret ({0 ~> vfvar y} vf))
          (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
          Hbody_wf) as Hτ_body.
        cbn [wf_context_ty_at] in Hτ_body.
        exact (proj1 Hτ_body).
      + rewrite (erase_fix_rec_call_ty b y τx τ t Hτx Hτ).
        pose proof (context_typing_wf_basic_typing Σ Γ
          (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf)
          as Hbasic.
        cbn [erase_ty] in Hbasic.
        rewrite Hτx, Hτ in Hbasic.
        eapply basic_typing_weaken_tm; [exact Hbasic|].
        rewrite erase_ctx_comma_bind_fresh.
        * apply insert_subseteq.
          apply not_elem_of_dom. exact HyΓ.
        * exact HyΓ.
  }
  pose proof (context_typing_wf_denot_static_guard_comma_bind_insert
    Σ Γ y τx (fix_rec_call_ty b y τx τ)
    (tret (vfix (TBase b →ₜ t) vf)) my HyΓ Hself_wf Hctx)
    as Hstatic.
  eapply ty_denote_gas_zero_tret_of_static_guard. exact Hstatic.
Qed.

Definition world_arg_min_at (b : base_ty) (x : atom)
    (m : WfWorldT) (μ : nat) : Prop :=
  (exists σ c,
    (m : WorldT) σ /\
    σ !! x = Some (vconst c) /\
    constant_measure_for_base b c = μ) /\
  forall σ c,
    (m : WorldT) σ ->
    σ !! x = Some (vconst c) ->
    μ <= constant_measure_for_base b c.

Definition fix_self_rec_call_reducible_at_measure
    (Σ : tyctx) Γ φx τ vf b t (L : aset) (μ : nat) : Prop :=
  forall (parent : WfWorldT) x,
    x ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_value vf ∪ fv_cty (over_ty b φx) ∪ fv_cty τ ->
    world_arg_min_at b x parent μ ->
    parent ⊨ ctx_denote_under Σ
      (CtxComma Γ (CtxBind x (over_ty b φx))) ->
    parent ⊨ ty_denote_gas
      (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
      ((<[LVFree x := TBase b]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (over_ty b φx)
      (tret (vfvar x)) ->
    parent ⊨ ty_denote_gas 0
      ((<[LVFree x := TBase b]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (fix_rec_call_ty b x (over_ty b φx) τ)
      (tret (vfix (TBase b →ₜ t) vf)) ->
    parent ⊨ ty_denote_gas
      (cty_depth (fix_rec_call_ty b x (over_ty b φx) τ))
      ((<[LVFree x := TBase b]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (fix_rec_call_ty b x (over_ty b φx) τ)
      (tret (vfix (TBase b →ₜ t) vf)).

Lemma nat_pred_min_exists (P : nat -> Prop) μ :
  P μ ->
  exists μmin,
    P μmin /\ forall ν, P ν -> μmin <= ν.
Proof.
  induction μ as [μ IH] using lt_wf_ind.
  intros HP.
  destruct (classic (exists ν, ν < μ /\ P ν)) as [[ν [Hνlt HPν]]|Hnone].
  - exact (IH ν Hνlt HPν).
  - exists μ. split; [exact HP|].
    intros ν HPν.
    destruct (le_gt_dec μ ν) as [Hle|Hgt]; [exact Hle|].
    exfalso. apply Hnone. exists ν. split; [lia|exact HPν].
Qed.

Lemma world_arg_min_exists_from_const
    b x (m : WfWorldT) :
  (forall σ,
    (m : WorldT) σ ->
    exists c, σ !! x = Some (vconst c)) ->
  exists μ, world_arg_min_at b x m μ.
Proof.
  intros Hconst.
  destruct (wfA_ne _ (world_wf m)) as [σ0 Hσ0].
  destruct (Hconst σ0 Hσ0) as [c0 Hσ0x].
  set (P := fun μ =>
    exists σ c,
      (m : WorldT) σ /\
      σ !! x = Some (vconst c) /\
      constant_measure_for_base b c = μ).
  destruct (nat_pred_min_exists P
    (constant_measure_for_base b c0)) as [μ [Hμmin Hμleast]].
  { exists σ0, c0. repeat split; eauto. }
  exists μ. split; [exact Hμmin|].
  intros σ c Hσ Hσx.
  apply Hμleast.
  exists σ, c. repeat split; eauto.
Qed.

Lemma fix_self_rec_call_world_min_exists
    gas Σ φx b x (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ
      (over_ty b φx)
      (tret (vfvar x)) ->
  exists μ, world_arg_min_at b x m μ.
Proof.
  intros Hden.
  apply world_arg_min_exists_from_const.
  intros σ Hσ.
  destruct (ty_denote_ret_fvar_base_const
    gas Σ (over_ty b φx) b x m ltac:(reflexivity) Hden σ Hσ)
    as [c [Hσx _]].
  exists c. exact Hσx.
Qed.

Lemma fix_rec_open_arg_normalize
    Γ φx τ vf b t x z (mz : WfWorldT) :
  lc_context_ty (over_ty b φx) ->
  x ∉ fv_cty (over_ty b φx) ->
  z <> x ->
  z ∉ dom (erase_ctx Γ) ∪ fv_value vf ∪
      fv_cty (over_ty b φx) ∪ fv_cty τ ->
  let Δx := (<[LVFree x := TBase b]>
    (atom_env_to_lty_env (erase_ctx Γ))) in
  let τarg := CTInter (over_ty b φx)
    (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))) in
  let τself := fix_rec_call_ty b x (over_ty b φx) τ in
  let self := tret (vfix (TBase b →ₜ t) vf) in
  mz ⊨ formula_open 0 z
    (ty_denote_gas (Nat.max (cty_depth τarg) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env Δx τself self)
        (erase_ty τarg))
      (cty_shift 0 τarg)
      (tret (vbvar 0))) ->
  let Δz := (<[LVFree z := TBase b]>
    (atom_env_to_lty_env (erase_ctx Γ))) in
  mz ⊨ ty_denote_gas
    (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
    Δz
    (over_ty b φx)
    (tret (vfvar z)) /\
  mz ⊨ ty_denote_gas
    (Nat.max (cty_depth (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))))
      (cty_depth τ))
    ((<[LVFree z := TBase b]>
      (<[LVFree x := TBase b]>
        (atom_env_to_lty_env (erase_ctx Γ)))))
    (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x)))
    (tret (vfvar z)).
Proof.
  cbn beta iota zeta.
  intros Hτx_lc Hxτx Hzx Hz Harg.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (τx := over_ty b φx).
  set (τlt := over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))).
  set (τarg := CTInter τx τlt).
  set (self := tret (vfix (TBase b →ₜ t) vf)).
  assert (Hτlt_lc : lc_context_ty τlt).
  { subst τlt. apply lc_context_ty_over_lt_bound_fvar. }
  assert (Hzτarg : z ∉ fv_cty τarg).
  {
    intros Hzbad.
    change (z ∈ lvars_fv
      (context_ty_lvars τx ∪ context_ty_lvars τlt)) in Hzbad.
    rewrite lvars_fv_union, !context_ty_lvars_fv in Hzbad.
    apply elem_of_union in Hzbad as [Hzτx_bad | Hzτlt_bad].
    - subst τx.
      revert Hzτx_bad. fix_self_notin_union.
    - change (z ∈ fv_cty
        (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x)))) in Hzτlt_bad.
      rewrite fv_cty_over_lt_bound_fvar in Hzτlt_bad.
      apply elem_of_singleton in Hzτlt_bad.
      exact (Hzx Hzτlt_bad).
  }
  assert (HΣclosed :
      lty_env_closed (<[LVFree x := TBase b]> Δ)).
  {
    subst Δ.
    apply lty_env_closed_insert_free.
    apply atom_store_to_lvar_store_closed.
  }
  assert (HzΣ : LVFree z ∉ dom (<[LVFree x := TBase b]> Δ : lty_env)).
  {
    subst Δ.
    rewrite dom_insert_L.
    rewrite atom_store_to_lvar_store_dom.
    intros Hzdom.
    apply lvars_fv_elem in Hzdom.
    rewrite lvars_fv_union, lvars_fv_singleton_free, lvars_fv_of_atoms
      in Hzdom.
    apply elem_of_union in Hzdom as [Hzx_bad | HzΓ_bad].
    - apply elem_of_singleton in Hzx_bad.
      exact (Hzx Hzx_bad).
    - revert HzΓ_bad. fix_self_notin_union.
  }
  assert (Hzarg_env :
      z ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env (<[LVFree x := TBase b]> Δ)
            (fix_rec_call_ty b x τx τ) self)
          (erase_ty τarg)))).
  {
    rewrite typed_lty_env_bind_lvars_fv_dom.
    intros Hzrel.
    apply lvars_fv_elem in Hzrel.
    eapply (relevant_env_fresh_free
      (<[LVFree x := TBase b]> Δ)
      (fix_rec_call_ty b x τx τ) self z).
	    - subst τx.
	      apply fv_cty_fix_rec_call_ty_fresh.
	      + exact Hzx.
	      + fix_self_notin_union.
	      + fix_self_notin_union.
	    - subst self. cbn [fv_tm fv_value]. fix_self_notin_union.
    - exact Hzrel.
  }
  pose proof (arrow_open_arg_to_inserted_env_normalized
    (Nat.max (cty_depth τarg) (cty_depth τ))
    (<[LVFree x := TBase b]> Δ) τarg τ self mz z
    HΣclosed HzΣ Hzτarg
    ltac:(subst τarg; cbn [cty_lc_at]; split; assumption)
    Hzarg_env) as Hopened.
  unfold fix_rec_call_ty in Harg.
  fold τx τlt τarg self Δ in Harg.
  pose proof (Hopened Harg) as Harg_open.
  rewrite ty_denote_gas_saturate in Harg_open by lia.
  subst τarg τx τlt Δ self.
  cbn [cty_depth ty_denote_gas erase_ty] in Harg_open.
  rewrite res_models_and_iff in Harg_open.
  destruct Harg_open as [_ Harg_body].
  rewrite res_models_and_iff in Harg_body.
  destruct Harg_body as [Hleft Hright].
  split.
  - rewrite ty_denote_gas_saturate by cty_depth_solve.
    rewrite ty_denote_gas_saturate in Hleft by
      cty_depth_solve.
    eapply (res_models_ty_denote_gas_env_agree_on
        (cty_depth (over_ty b φx))
        (<[LVFree z := TBase b]>
          (<[LVFree x := TBase b]>
            (atom_env_to_lty_env (erase_ctx Γ))))
        (<[LVFree z := TBase b]>
          (atom_env_to_lty_env (erase_ctx Γ)))
        (over_ty b φx) (tret (vfvar z))
        (relevant_lvars (over_ty b φx) (tret (vfvar z))) mz).
	    + reflexivity.
	    + rewrite <- (lvar_store_insert_free_commute
	        (atom_env_to_lty_env (erase_ctx Γ)) x z (TBase b) (TBase b))
	        by congruence.
	      apply lty_env_restrict_lvars_insert_fresh.
	        intros Hbad.
        apply lvars_fv_elem in Hbad.
        rewrite relevant_lvars_fv in Hbad.
        cbn [fv_tm fv_value] in Hbad.
        better_set_solver.
    + exact Hleft.
  - rewrite ty_denote_gas_saturate by cty_depth_solve.
    rewrite ty_denote_gas_saturate in Hright by
      cty_depth_solve.
    exact Hright.
Qed.

Lemma fix_rec_arg_decreases_min
    gas Σ b x z μ (parent mz : WfWorldT) :
  z <> x ->
  lty_env_closed Σ ->
  0 < gas ->
  parent ⊑ mz ->
  world_arg_min_at b x parent μ ->
  mz ⊨ ty_denote_gas gas Σ
    (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x)))
    (tret (vfvar z)) ->
  exists μ',
    μ' < μ /\
    world_arg_min_at b z mz μ'.
Proof.
  intros Hzx HΣclosed Hgas_pos Hle Hmin Hlt.
  destruct gas as [|gas']; [lia|].
  pose proof (ty_denote_lt_arg_fiber
    gas' Σ b z x mz Hzx HΣclosed Hlt) as Hlt_store.
  destruct (world_arg_min_exists_from_const b z mz) as [μ' Hmin_z].
  {
    intros σ Hσ.
    destruct (Hlt_store σ Hσ) as [cz [cx [Hz [_ _]]]].
    exists cz. exact Hz.
  }
  destruct Hmin as [[σparent [cxparent
    [Hσparent [Hxparent Hμeq]]]] Hmin_lower].
  destruct (res_le_store_lift parent mz σparent Hle Hσparent)
    as [σmz [Hσmz Hrestrict]].
  destruct (Hlt_store σmz Hσmz) as
    [cz [cxmz [Hzmz [Hxmz Hlt_cz_cx]]]].
  assert (Hx_parent_dom : x ∈ world_dom (parent : WorldT)).
  {
    rewrite <- (wfworld_store_dom parent σparent Hσparent).
    change (x ∈ dom (σparent : gmap atom value)).
    eapply elem_of_dom_2. exact Hxparent.
  }
  assert (Hxmz_restrict :
      store_restrict σmz (world_dom (parent : WorldT)) !! x =
      Some (vconst cxmz)).
  {
    apply storeA_restrict_lookup_some_2; [exact Hxmz|exact Hx_parent_dom].
  }
  rewrite Hrestrict, Hxparent in Hxmz_restrict.
  inversion Hxmz_restrict. subst cxmz.
  exists μ'. split; [|exact Hmin_z].
  destruct Hmin_z as [_ Hmin_z_lower].
  pose proof (Hmin_z_lower σmz cz Hσmz Hzmz) as Hμ'_le_z.
  unfold constant_lt_for_base in Hlt_cz_cx.
  unfold ltof in Hlt_cz_cx.
  lia.
Qed.

Lemma fix_rec_child_ctx_from_arg
    Σ Γ φx τ b x z (parent mz : WfWorldT) :
  basic_ctx (dom Σ) Γ ->
  fv_cty (over_ty b φx) ⊆ dom (erase_ctx Γ) ->
  parent ⊑ mz ->
  parent ⊨ ctx_denote_under Σ
    (CtxComma Γ (CtxBind x (over_ty b φx))) ->
  mz ⊨ ty_denote_gas
    (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
    ((<[LVFree z := TBase b]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (over_ty b φx)
    (tret (vfvar z)) ->
  z ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
      fv_cty (over_ty b φx) ->
  mz ⊨ ctx_denote_under Σ
    (CtxComma Γ (CtxBind z (over_ty b φx))).
Proof.
  intros HbasicΓ Hτxfv Hle Hctx Harg Hz.
  set (τx := over_ty b φx).
  assert (HΓ_parent : parent ⊨ ctx_denote_under Σ Γ).
  { exact (ctx_denote_under_comma_left Σ Γ (CtxBind x τx) parent Hctx). }
  assert (HΓ_mz : mz ⊨ ctx_denote_under Σ Γ).
  { eapply res_models_kripke; eauto. }
  assert (Harg_depth :
      mz ⊨ ty_denote_gas (cty_depth τx)
        (<[LVFree z := erase_ty τx]>
          (atom_env_to_lty_env (erase_ctx Γ)))
        τx (tret (vfvar z))).
  {
    subst τx.
    rewrite ty_denote_gas_saturate in Harg by cty_depth_solve.
    exact Harg.
  }
  pose proof (ty_denote_gas_ret_fvar_insert_ctx_erasure_under
    (cty_depth τx) Σ Γ τx z mz HbasicΓ Hτxfv Harg_depth)
    as Harg_erasure.
  assert (Hworld_bind :
      mz ⊨ basic_world_formula
        (atom_env_to_lty_env (<[z := erase_ty τx]>
          (ctx_erasure_under Σ Γ)))).
  {
    replace (atom_env_to_lty_env
        (<[z := erase_ty τx]> (ctx_erasure_under Σ Γ)))
      with (<[LVFree z := erase_ty τx]>
        (atom_env_to_lty_env (ctx_erasure_under Σ Γ))).
    2:{ symmetry. apply atom_store_to_lvar_store_insert. }
	    eapply (basic_world_insert_of_arg
	      (atom_env_to_lty_env (ctx_erasure_under Σ Γ)) τx z
	      (erase_ty τx) (cty_depth τx)).
	    - apply atom_env_to_lty_env_dom_free_notin.
	      ctx_erasure_under_norm_in Hz. better_set_solver.
	    - exact (ctx_denote_under_basic_world Σ Γ mz HΓ_mz).
	    - rewrite <- atom_store_to_lvar_store_insert.
	      exact Harg_erasure.
	  }
  assert (Hagree :
      ty_env_agree_on (fv_cty τx)
        (Σ ∪ erase_ctx Γ) (ctx_erasure_under Σ Γ)).
  {
    eapply ty_env_agree_ctx_erasure_under_of_basic_ctx; eauto.
  }
  assert (Hbind :
      mz ⊨ ctx_denote_under (Σ ∪ erase_ctx Γ) (CtxBind z τx)).
  {
    eapply ctx_bind_from_inserted_erasure_denotation.
    - ctx_erasure_under_norm_in Hz. better_set_solver.
    - exact Hagree.
    - exact Hworld_bind.
    - exact Harg_erasure.
  }
  subst τx.
  eapply ctx_denote_under_comma_intro; eauto.
Qed.

Lemma fix_rec_unfolded_result_to_open_goal
    Σ Γ φx τ vf b t (mz : WfWorldT) x z :
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow (over_ty b φx) τ) ->
  z <> x ->
  x ∉ fv_value vf ∪ fv_cty τ ->
  z ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
      fv_value vf ∪ fv_cty (over_ty b φx) ∪ fv_cty τ ->
  mz ⊨ ctx_denote_under Σ
    (CtxComma Γ (CtxBind z (over_ty b φx))) ->
  mz ⊨ ty_denote_gas
    (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
    ((<[LVFree z := TBase b]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 z τ)
    (tapp_tm (tret (open_value 0 (vfvar z) vf))
      (vfix (TBase b →ₜ t) vf)) ->
  let Δx := (<[LVFree x := TBase b]>
    (atom_env_to_lty_env (erase_ctx Γ))) in
  let τarg := CTInter (over_ty b φx)
    (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))) in
  let τself := fix_rec_call_ty b x (over_ty b φx) τ in
  let self := tret (vfix (TBase b →ₜ t) vf) in
  mz ⊨ formula_open 0 z
    (ty_denote_gas (Nat.max (cty_depth τarg) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env Δx τself self)
        (erase_ty τarg))
      τ
      (tapp_tm (tm_shift 0 self) (vbvar 0))).
Proof.
  intros Hτ Hwf Hzx Hx_fresh Hzfresh Hctx_z Hunfolded.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (Δx := <[LVFree x := TBase b]> Δ).
  set (τx := over_ty b φx).
  set (τarg := CTInter τx
    (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x)))).
  set (τself := fix_rec_call_ty b x τx τ).
  set (self := tret (vfix (TBase b →ₜ t) vf)).
  set (Gouter := Nat.max (cty_depth τx) (cty_depth τ)).
  set (Gtarget := Nat.max (cty_depth τarg) (cty_depth τ)).
  assert (Hzτ : z ∉ fv_cty τ) by fix_self_notin_union.
  assert (Hzτx : z ∉ fv_cty τx).
  { subst τx. fix_self_notin_union. }
  assert (Hzτself_fix : z ∉ fv_cty (fix_rec_call_ty b x τx τ)).
  {
    apply fv_cty_fix_rec_call_ty_fresh; [exact Hzx|exact Hzτx|exact Hzτ].
  }
  assert (Hzself : z ∉ fv_tm self).
  { subst self. cbn [fv_tm fv_value]. fix_self_notin_union. }
  assert (Hlc_self : lc_tm self).
  {
    subst self.
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vfix (TBase b →ₜ t) vf)) (CTArrow (over_ty b φx) τ)
      Hwf).
  }
  pose proof (fix_arrow_opened_app_static_guard_full
    Σ Γ τx τ vf b t mz z Hwf ltac:(subst τx; exact Hzfresh) Hctx_z)
    as Hstatic_fix.
  pose proof (fix_unfolded_result_to_opened_goal
    Σ Γ τx τ vf b t mz z Hwf ltac:(subst τx; exact Hzfresh)
    Hunfolded Hstatic_fix) as Houter_raw.
  assert (Houter_rel :
      mz ⊨ ty_denote_gas Gouter
        (<[LVFree z := erase_ty τx]>
          (relevant_env Δ (CTArrow τx τ) self))
        (cty_open 0 z τ)
        (tapp_tm self (vfvar z))).
  {
    subst Gouter Δ self.
    rewrite (formula_open_ty_denote_gas_singleton 0 z
      (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vfix (TBase b →ₜ t) vf)))
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret (vfix (TBase b →ₜ t) vf))) (vbvar 0)))
      in Houter_raw.
    2:{
      rewrite typed_lty_env_bind_lvars_fv_dom.
      intros Hzrel.
      apply lvars_fv_elem in Hzrel.
      pose proof (relevant_env_arrow_fresh_free
        (atom_env_to_lty_env (erase_ctx Γ)) τx τ
        (tret (vfix (TBase b →ₜ t) vf)) z
        Hzτx Hzτ ltac:(cbn [fv_tm fv_value]; better_set_solver))
        as Hfresh_rel.
      exact (Hfresh_rel Hzrel).
    }
    2:{
      rewrite fv_tapp_tm, tm_shift_fv.
      cbn [fv_tm fv_value]. better_set_solver.
    }
    2:{ exact Hzτ. }
    rewrite open_tapp_tm_shift_bvar0_lc in Houter_raw by exact Hlc_self.
    rewrite typed_lty_env_bind_open_current in Houter_raw.
    - exact Houter_raw.
	    - eapply relevant_env_arrow_fresh_free.
	      + exact Hzτx.
	      + exact Hzτ.
	      + exact Hzself.
    - apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
  }
  assert (Houter_mid :
      mz ⊨ ty_denote_gas Gouter
        (<[LVFree z := erase_ty τx]> Δ)
        (cty_open 0 z τ)
        (tapp_tm self (vfvar z))).
  {
    eapply ty_equiv_arrow_result_src_mid_inserted.
    - subst Δ. apply atom_store_to_lvar_store_closed.
    - subst Δ. apply atom_env_to_lty_env_dom_free_notin.
      ctx_erasure_under_norm_in Hzfresh. better_set_solver.
    - eapply relevant_env_arrow_fresh_free.
      + exact Hzτx.
      + exact Hzτ.
      + subst self. exact Hzself.
    - exact Hlc_self.
    - exact Hzτ.
    - exact Houter_rel.
  }
  assert (Hmid_big :
      mz ⊨ ty_denote_gas Gtarget
        (<[LVFree z := erase_ty τx]> Δ)
        (cty_open 0 z τ)
        (tapp_tm self (vfvar z))).
  {
    subst Gouter Gtarget.
    rewrite ty_denote_gas_saturate by cty_depth_solve.
      rewrite ty_denote_gas_saturate in Houter_mid by cty_depth_solve.
      exact Houter_mid.
  }
  assert (Htarget_rel_lc :
      lc_lvars (relevant_lvars (cty_open 0 z τ)
        (tapp_tm self (vfvar z)))).
  {
    apply lc_lvars_relevant_lvars.
    - pose proof (context_typing_wf_context_ty Σ Γ
        (tret (vfix (TBase b →ₜ t) vf))
        (CTArrow (over_ty b φx) τ) Hwf) as Hτ_arrow.
      cbn [wf_context_ty_at] in Hτ_arrow.
      apply wf_context_ty_at_lc with
        (D := dom (erase_ctx Γ) ∪ ({[z]} : aset)).
      apply wf_context_ty_at_open_at.
      + ctx_erasure_under_norm_in Hzfresh. better_set_solver.
      + exact (proj2 Hτ_arrow).
    - apply lc_tapp_tm; [exact Hlc_self|constructor].
  }
  assert (Hx_not_rel :
      LVFree x ∉ relevant_lvars (cty_open 0 z τ)
        (tapp_tm self (vfvar z))).
  {
    subst self.
    intros Hbad.
    unfold relevant_lvars in Hbad.
    apply elem_of_union in Hbad as [Hτbad|Htmbad].
    - apply Hx_fresh.
      apply elem_of_union_r.
      pose proof (cty_open_fv_subset 0 z τ) as Hτopen.
      apply lvars_fv_elem in Hτbad.
      rewrite context_ty_lvars_fv in Hτbad.
      better_set_solver.
    - apply Hx_fresh.
      apply elem_of_union_l.
      apply lvars_fv_elem in Htmbad.
      rewrite tm_lvars_fv, fv_tapp_tm in Htmbad.
      cbn [fv_tm fv_value] in Htmbad.
      better_set_solver.
  }
  assert (Hmid_x :
      mz ⊨ ty_denote_gas Gtarget
        (<[LVFree z := erase_ty τarg]> Δx)
        (cty_open 0 z τ)
        (tapp_tm self (vfvar z))).
  {
    eapply (res_models_ty_denote_gas_env_agree_on
      Gtarget
      (<[LVFree z := erase_ty τx]> Δ)
      (<[LVFree z := erase_ty τarg]> Δx)
      (cty_open 0 z τ)
      (tapp_tm self (vfvar z))
      (relevant_lvars (cty_open 0 z τ)
        (tapp_tm self (vfvar z)))
      mz).
    - reflexivity.
    - subst Δx Δ τx τarg.
      unfold over_ty.
      cbn [erase_ty].
      symmetry.
      rewrite <- (lvar_store_insert_free_commute
        (atom_env_to_lty_env (erase_ctx Γ)) x z (TBase b) (TBase b))
        by congruence.
      apply lty_env_restrict_lvars_insert_fresh.
      exact Hx_not_rel.
    - exact Hmid_big.
  }
  assert (Htarget_open :
      mz ⊨ ty_denote_gas Gtarget
        (<[LVFree z := erase_ty τarg]>
          (relevant_env Δx τself self))
        (cty_open 0 z τ)
        (tapp_tm self (vfvar z))).
  {
    eapply ty_equiv_arrow_result_tgt_goal_inserted.
    - subst Δx Δ. apply lty_env_closed_insert_free.
      apply atom_store_to_lvar_store_closed.
	    - subst Δx Δ.
	      rewrite dom_insert_L.
	      intros Hzdom.
	      apply elem_of_union in Hzdom as [Hzx_bad | HzΓ_bad].
	      + apply elem_of_singleton in Hzx_bad.
	        inversion Hzx_bad. congruence.
	      + pose proof (atom_env_to_lty_env_dom_free_notin
	          (erase_ctx Γ) z
	          ltac:(ctx_erasure_under_norm_in Hzfresh; better_set_solver))
	          as Hznot.
	        exact (Hznot HzΓ_bad).
    - eapply relevant_env_fresh_free.
      + exact Hzτself_fix.
      + exact Hzself.
    - subst self. exact Hlc_self.
    - exact Hzτ.
    - exact Hmid_x.
  }
  cbn beta iota zeta.
  subst Gtarget Δx τself τarg self.
  rewrite (formula_open_ty_denote_gas_singleton 0 z
    (Nat.max
      (cty_depth
        (CTInter (over_ty b φx)
          (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x)))))
      (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env
        (<[LVFree x := TBase b]> (atom_env_to_lty_env (erase_ctx Γ)))
        (fix_rec_call_ty b x (over_ty b φx) τ)
        (tret (vfix (TBase b →ₜ t) vf)))
      (erase_ty
        (CTInter (over_ty b φx)
          (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x)))))
    )
    τ
    (tapp_tm (tm_shift 0 (tret (vfix (TBase b →ₜ t) vf))) (vbvar 0))).
  2:{
    rewrite typed_lty_env_bind_lvars_fv_dom.
    intros Hzrel.
    apply lvars_fv_elem in Hzrel.
    eapply (relevant_env_fresh_free
      (<[LVFree x := TBase b]> (atom_env_to_lty_env (erase_ctx Γ)))
      (fix_rec_call_ty b x (over_ty b φx) τ)
      (tret (vfix (TBase b →ₜ t) vf)) z).
	    - exact Hzτself_fix.
	    - exact Hzself.
	    - exact Hzrel.
	  }
	  2:{
	    rewrite fv_tapp_tm, tm_shift_fv.
	    cbn [fv_tm fv_value].
	    intros Hzbad.
	    apply elem_of_union in Hzbad as [Hzfix | Hzempty].
	    - exact (Hzself Hzfix).
	    - set_unfold in Hzempty. exact Hzempty.
	  }
  2:{ exact Hzτ. }
	  rewrite open_tapp_tm_shift_bvar0_lc by
	    (exact (context_typing_wf_lc_tm
	      Σ Γ (tret (vfix (TBase b →ₜ t) vf)) (CTArrow (over_ty b φx) τ)
	      Hwf)).
  rewrite typed_lty_env_bind_open_current.
  - exact Htarget_open.
  - eapply relevant_env_fresh_free.
    + exact Hzτself_fix.
    + exact Hzself.
  - apply relevant_env_closed.
    apply lty_env_closed_insert_free.
    apply atom_store_to_lvar_store_closed.
Qed.

Lemma fix_self_rec_call_reducible_measure_step Σ Γ φx τ vf b t (L : aset) μ :
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow (over_ty b φx) τ) ->
  (forall x, x ∉ L ->
    context_typing_wf Σ
      (CtxComma Γ (CtxBind x (over_ty b φx)))
      (tret ({0 ~> vfvar x} vf))
      (CTArrow (fix_rec_call_ty b x (over_ty b φx) τ) ({0 ~> x} τ))) ->
  (forall x, x ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind x (over_ty b φx))) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind x (over_ty b φx)))
        (CTArrow (fix_rec_call_ty b x (over_ty b φx) τ) ({0 ~> x} τ))
        (tret ({0 ~> vfvar x} vf))) ->
  (forall μ',
    μ' < μ ->
    fix_self_rec_call_reducible_at_measure Σ Γ φx τ vf b t L μ') ->
  fix_self_rec_call_reducible_at_measure Σ Γ φx τ vf b t L μ.
Proof.
  intros Hτ Hwf Hbody_wf Hbody_IH Hsmaller.
  unfold fix_self_rec_call_reducible_at_measure.
  intros parent x Hx Hmin Hctx Harg Hzero.
  set (Δx := (<[LVFree x := TBase b]>
    (atom_env_to_lty_env (erase_ctx Γ)))).
  set (τarg := CTInter (over_ty b φx)
    (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x)))).
  set (τself := fix_rec_call_ty b x (over_ty b φx) τ).
  set (self := tret (vfix (TBase b →ₜ t) vf)).
  pose proof (ty_denote_gas_guard_of_zero
    Δx τself self parent Hzero) as Hguard.
  pose proof (ty_denote_gas_scope_from_zero_any
    (cty_depth τself) Δx τself self parent Hzero) as Hscope_full.
  subst τself τarg self Δx.
  unfold fix_rec_call_ty in Hguard, Hscope_full |- *.
  cbn [cty_depth ty_denote_gas] in Hguard, Hscope_full |- *.
  rewrite res_models_and_iff. split.
  - exact Hguard.
  - pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_body.
    eapply res_models_forall_rev_intro; [exact Hscope_body|].
    exists (L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
      fv_value vf ∪ fv_cty (over_ty b φx) ∪ fv_cty τ ∪
      world_dom (parent : WorldT)).
    intros z Hz mz Hdom Hrestrict.
    assert (Hle : parent ⊑ mz).
    { rewrite <- Hrestrict. apply res_restrict_le. }
    assert (Hz_mz : z ∈ world_dom (mz : WorldT)).
    { rewrite Hdom. fix_self_in_union. }
	    pose proof (formula_scoped_forall_open_res_le
	      parent mz z _ Hscope_body Hle Hz_mz) as Hopen_scope.
	    eapply res_models_impl_intro; [exact Hopen_scope|].
	    intros Hrec_arg.
	    assert (Hτx_lc : lc_context_ty (over_ty b φx)).
		    {
		      pose proof (context_typing_wf_context_ty Σ Γ
		        (tret (vfix (TBase b →ₜ t) vf))
		        (CTArrow (over_ty b φx) τ) Hwf) as Hτ_arrow.
		      cbn [wf_context_ty_at] in Hτ_arrow.
		      eapply wf_context_ty_at_lc. exact (proj1 Hτ_arrow).
		    }
	    assert (Hx_parent_dom : x ∈ world_dom (parent : WorldT)).
	    {
	      destruct Hmin as [[σmin [cmin [Hσmin [Hxσmin _]]]] _].
	      rewrite <- (wfworld_store_dom parent σmin Hσmin).
	      change (x ∈ dom (σmin : gmap atom value)).
	      eapply elem_of_dom_2. exact Hxσmin.
	    }
	    assert (Hz_not_parent : z ∉ world_dom (parent : WorldT)).
	    { fix_self_notin_union. }
	    assert (Hzx_neq : z <> x).
	    {
	      intros ->. exact (Hz_not_parent Hx_parent_dom).
	    }
		    pose proof (fix_rec_open_arg_normalize
		      Γ φx τ vf b t x z mz Hτx_lc ltac:(fix_self_notin_union)
		      Hzx_neq
		      ltac:(ctx_erasure_under_norm_in Hz; better_set_solver)
		      Hrec_arg)
		      as [Harg_z Hlt_z].
	    assert (Hlt_env_closed :
	        lty_env_closed
	          (<[LVFree z := TBase b]>
	            (<[LVFree x := TBase b]>
	            (atom_env_to_lty_env (erase_ctx Γ))))).
	    {
	      apply lty_env_closed_insert_free.
	      apply lty_env_closed_insert_free.
	      apply atom_store_to_lvar_store_closed.
	    }
    assert (Hlt_gas_pos :
        0 <
        Nat.max
          (cty_depth (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))))
          (cty_depth τ)).
    { cty_depth_solve. }
	    destruct (fix_rec_arg_decreases_min
	      (Nat.max
	        (cty_depth (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))))
	        (cty_depth τ))
	      ((<[LVFree z := TBase b]>
	        (<[LVFree x := TBase b]>
	        (atom_env_to_lty_env (erase_ctx Γ)))))
	      b x z μ parent mz Hzx_neq Hlt_env_closed Hlt_gas_pos Hle Hmin Hlt_z)
	      as [μ' [Hμ'lt Hmin_z]].
	    pose proof (context_typing_wf_ctx Σ Γ
	      (tret (vfix (TBase b →ₜ t) vf))
	      (CTArrow (over_ty b φx) τ) Hwf) as HwfctxΓ.
	    pose proof (wf_ctx_under_basic Σ Γ HwfctxΓ) as HbasicΓ.
	    pose proof (context_typing_wf_context_ty Σ Γ
	      (tret (vfix (TBase b →ₜ t) vf))
	      (CTArrow (over_ty b φx) τ) Hwf) as Hτ_arrow.
	    cbn [wf_context_ty_at] in Hτ_arrow.
	    pose proof (wf_context_ty_at_fv_subset 0 (dom (erase_ctx Γ))
	      (over_ty b φx) (proj1 Hτ_arrow)) as Hτxfv.
	    pose proof (fix_rec_child_ctx_from_arg
	      Σ Γ φx τ b x z parent mz HbasicΓ Hτxfv Hle Hctx Harg_z
	      ltac:(fix_self_notin_union)) as Hctx_z.
    pose proof (Hsmaller μ' Hμ'lt) as Hrec_smaller.
    pose proof (Hbody_wf z ltac:(fix_self_notin_union)) as Hbody_wf_z.
    pose proof (Hbody_IH z ltac:(fix_self_notin_union) mz Hctx_z)
      as Hbody_arrow_z.
    pose proof (fix_self_rec_call_zero
      Σ Γ (over_ty b φx) τ vf b t mz z
      ltac:(reflexivity) Hτ Hwf Hbody_wf_z
      ltac:(fix_self_notin_union) Hctx_z) as Hzero_z.
    unfold fix_self_rec_call_reducible_at_measure in Hrec_smaller.
    pose proof (Hrec_smaller mz z ltac:(fix_self_notin_union)
      Hmin_z Hctx_z Harg_z Hzero_z) as Hself_z.
	    pose proof (fix_body_arrow_apply_self
	      Σ Γ (over_ty b φx) τ vf b t mz z
	      ltac:(reflexivity) Hτ Hwf Hbody_wf_z
	      ltac:(fix_self_notin_union) Hctx_z Hbody_arrow_z Hself_z)
	      as Hunfolded_z.
	    eapply fix_rec_unfolded_result_to_open_goal.
	    + exact Hτ.
	    + exact Hwf.
	    + exact Hzx_neq.
	    + fix_self_notin_union.
	    + fix_self_notin_union.
	    + exact Hctx_z.
	    + exact Hunfolded_z.
Qed.

Lemma fix_self_rec_call_denotation_by_world_min_induction Σ Γ φx τ vf b t (L : aset) :
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow (over_ty b φx) τ) ->
  (forall x, x ∉ L ->
    context_typing_wf Σ
      (CtxComma Γ (CtxBind x (over_ty b φx)))
      (tret ({0 ~> vfvar x} vf))
      (CTArrow (fix_rec_call_ty b x (over_ty b φx) τ) ({0 ~> x} τ))) ->
  (forall x, x ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind x (over_ty b φx))) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind x (over_ty b φx)))
        (CTArrow (fix_rec_call_ty b x (over_ty b φx) τ) ({0 ~> x} τ))
        (tret ({0 ~> vfvar x} vf))) ->
  forall μ, fix_self_rec_call_reducible_at_measure Σ Γ φx τ vf b t L μ.
Proof.
  intros Hτ Hwf Hbody_wf Hbody_IH.
  refine (well_founded_induction
    lt_wf
    (fun μ => fix_self_rec_call_reducible_at_measure Σ Γ φx τ vf b t L μ)
    _).
  intros μ Hsmaller.
  eapply fix_self_rec_call_reducible_measure_step; eauto.
Qed.

Lemma fix_self_rec_call_denotation Σ Γ φx τ vf b t (L : aset)
    (my : WfWorldT) y :
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow (over_ty b φx) τ) ->
  (forall y, y ∉ L ->
    context_typing_wf Σ
      (CtxComma Γ (CtxBind y (over_ty b φx)))
      (tret ({0 ~> vfvar y} vf))
      (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx))) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx)))
        (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty (over_ty b φx) ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx))) ->
  my ⊨ ty_denote_gas
      (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
      ((<[LVFree y := TBase b]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (over_ty b φx) (tret (vfvar y)) ->
  my ⊨ ty_denote_gas
      (cty_depth (fix_rec_call_ty b y (over_ty b φx) τ))
      ((<[LVFree y := TBase b]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (fix_rec_call_ty b y (over_ty b φx) τ)
      (tret (vfix (TBase b →ₜ t) vf)).
Proof.
  intros Hτ Hwf Hbody_wf Hbody_IH Hy Hctx Harg.
  pose proof (fix_self_rec_call_world_min_exists
    (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
    ((<[LVFree y := TBase b]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    φx b y my Harg) as [μ Hmin].
  pose proof (fix_self_rec_call_zero
    Σ Γ (over_ty b φx) τ vf b t my y
    ltac:(reflexivity) Hτ Hwf (Hbody_wf y ltac:(fix_self_notin_union))
    ltac:(fix_self_notin_union) Hctx) as Hzero.
  pose proof (fix_self_rec_call_denotation_by_world_min_induction
    Σ Γ φx τ vf b t L Hτ Hwf Hbody_wf Hbody_IH μ)
    as Hμ.
  unfold fix_self_rec_call_reducible_at_measure in Hμ.
  eapply Hμ; eauto.
Qed.
