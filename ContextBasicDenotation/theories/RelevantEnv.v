(** * BasicDenotation.RelevantEnv

    Syntactic relevant-environment support for denotation guards.

    These definitions do not depend on the recursive context-type denotation:
    they only restrict an lvar-keyed type environment to the lvars mentioned by
    a context type and a term. *)

From ContextBasicDenotation Require Import Notation StoreTyping TermSyntax TermOpen
  BasicTypingFormula.
From ContextBase Require Import BaseTactics.

Section RelevantEnv.

Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Definition lty_env_restrict_lvars (Σ : lty_env) (D : lvset) : lty_env :=
  storeA_restrict Σ D.

Definition relevant_lvars (τ : context_ty) (e : tm) : lvset :=
  context_ty_lvars τ ∪ tm_lvars e.

Definition relevant_env (Σ : lty_env) (τ : context_ty) (e : tm)
    : lty_env :=
  lty_env_restrict_lvars Σ (relevant_lvars τ e).

Lemma relevant_lvars_fv τ e :
  lvars_fv (relevant_lvars τ e) = fv_cty τ ∪ fv_tm e.
Proof.
  unfold relevant_lvars.
  rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv.
  set_solver.
Qed.

Lemma lc_lvars_relevant_lvars τ e :
  lc_context_ty τ ->
  lc_tm e ->
  lc_lvars (relevant_lvars τ e).
Proof.
  intros Hτ He u Hu.
  unfold relevant_lvars in Hu.
  apply elem_of_union in Hu as [Huτ | Hue].
  - pose proof (cty_lc_at_lvars_bv_empty 0 τ Hτ) as Hbv.
    destruct u as [k|a]; [|exact I].
    exfalso.
    assert (k ∈ lvars_bv (context_ty_lvars τ)).
    { apply lvars_bv_elem. exact Huτ. }
    change (context_ty_lvars τ) with (context_ty_lvars_at 0 τ) in H.
    rewrite Hbv in H.
    exact (not_elem_of_empty k H).
  - exact (tm_lvars_lc e He u Hue).
Qed.

Lemma relevant_env_empty (Σ : lty_env) τ e :
  relevant_lvars τ e = (∅ : lvset) ->
  relevant_env Σ τ e = (∅ : lty_env).
Proof.
  intros Hempty.
  unfold relevant_env, lty_env_restrict_lvars.
  rewrite Hempty.
  apply storeA_restrict_empty_set.
Qed.

Lemma relevant_env_fresh_free (Σ : lty_env) τ e x :
  x ∉ fv_cty τ ->
  x ∉ fv_tm e ->
  LVFree x ∉ dom (relevant_env Σ τ e : lty_env).
Proof.
  intros Hxτ Hxe Hbad.
  unfold relevant_env, lty_env_restrict_lvars in Hbad.
  rewrite storeA_restrict_dom in Hbad.
  apply elem_of_intersection in Hbad as [_ Hrel].
  apply lvars_fv_elem in Hrel.
  rewrite relevant_lvars_fv in Hrel.
  set_solver.
Qed.

Lemma relevant_env_arrow_fresh_free
    (Σ : lty_env) τx τr e x :
  x ∉ fv_cty τx ->
  x ∉ fv_cty τr ->
  x ∉ fv_tm e ->
  LVFree x ∉ dom (relevant_env Σ (CTArrow τx τr) e : lty_env).
Proof.
  intros Hxτx Hxτr Hxe.
  apply relevant_env_fresh_free; [|exact Hxe].
  unfold fv_cty, context_ty_lvars.
  cbn [context_ty_lvars_at].
  rewrite lvars_fv_union, !context_ty_lvars_fv_at.
  set_solver.
Qed.

Lemma relevant_env_wand_fresh_free
    (Σ : lty_env) τx τr e x :
  x ∉ fv_cty τx ->
  x ∉ fv_cty τr ->
  x ∉ fv_tm e ->
  LVFree x ∉ dom (relevant_env Σ (CTWand τx τr) e : lty_env).
Proof.
  intros Hxτx Hxτr Hxe.
  change (relevant_env Σ (CTWand τx τr) e)
    with (relevant_env Σ (CTArrow τx τr) e).
  eapply relevant_env_arrow_fresh_free; eauto.
Qed.

Lemma soundness_relevant_env_arrow_value_fresh
    (Δ : lty_env) τx τ v x :
  x ∉ fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  LVFree x ∉ dom (relevant_env Δ (CTArrow τx τ) (tret v) : lty_env).
Proof.
  intros Hfresh.
  apply relevant_env_arrow_fresh_free; cbn [fv_tm fv_value]; set_solver.
Qed.

Lemma soundness_relevant_env_wand_value_fresh
    (Δ : lty_env) τx τ v x :
  x ∉ fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  LVFree x ∉ dom (relevant_env Δ (CTWand τx τ) (tret v) : lty_env).
Proof.
  intros Hfresh.
  apply relevant_env_wand_fresh_free; cbn [fv_tm fv_value]; set_solver.
Qed.

Lemma soundness_typed_bind_arrow_value_fresh
    (Δ : lty_env) τx τ v x T :
  x ∉ fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  x ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Δ (CTArrow τx τ) (tret v)) T)).
Proof.
  intros Hfresh Hbad.
  rewrite typed_lty_env_bind_lvars_fv_dom in Hbad.
  apply lvars_fv_elem in Hbad.
  eapply soundness_relevant_env_arrow_value_fresh; eauto.
Qed.

Lemma soundness_typed_bind_wand_value_fresh
    (Δ : lty_env) τx τ v x T :
  x ∉ fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  x ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Δ (CTWand τx τ) (tret v)) T)).
Proof.
  intros Hfresh Hbad.
  rewrite typed_lty_env_bind_lvars_fv_dom in Hbad.
  apply lvars_fv_elem in Hbad.
  eapply soundness_relevant_env_wand_value_fresh; eauto.
Qed.

Lemma lvars_of_atoms_empty :
  lvars_of_atoms (∅ : aset) = (∅ : lvset).
Proof.
  unfold lvars_of_atoms.
  rewrite set_map_empty. reflexivity.
Qed.

Lemma relevant_lvars_basic_ret_fvar_subset x τ :
  basic_context_ty ∅ τ ->
  relevant_lvars τ (tret (vfvar x)) ⊆ {[LVFree x]}.
Proof.
  intros Hbasic v Hv.
  pose proof (basic_context_ty_to_lvars _ _ Hbasic) as [Hτ _].
  rewrite lvars_of_atoms_empty in Hτ.
  unfold relevant_lvars in Hv.
  cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hv.
  set_solver.
Qed.

Lemma relevant_lvars_wf_empty_ret_fvar_subset x τ :
  wf_context_ty_at 0 ∅ τ ->
  relevant_lvars τ (tret (vfvar x)) ⊆ {[LVFree x]}.
Proof.
  intros Hτ.
  apply relevant_lvars_basic_ret_fvar_subset.
  rewrite basic_context_ty_iff_wf_context_ty_at.
  exact Hτ.
Qed.

Lemma lty_env_restrict_relevant_ret_fvar_closed_eq
    (Σ1 Σ2 : lty_env) τ x T :
  wf_context_ty_at 0 ∅ τ ->
  Σ1 !! LVFree x = Some T ->
  Σ2 !! LVFree x = Some T ->
  lty_env_restrict_lvars Σ1 (relevant_lvars τ (tret (vfvar x))) =
  lty_env_restrict_lvars Σ2 (relevant_lvars τ (tret (vfvar x))).
Proof.
  intros Hτ HΣ1x HΣ2x.
  unfold lty_env_restrict_lvars.
  eapply storeA_restrict_eq_mono.
  - apply relevant_lvars_wf_empty_ret_fvar_subset. exact Hτ.
  - rewrite (storeA_restrict_singleton_lookup Σ1 (LVFree x) T HΣ1x).
    rewrite (storeA_restrict_singleton_lookup Σ2 (LVFree x) T HΣ2x).
    reflexivity.
Qed.

Lemma lty_env_restrict_relevant_arrow_arg_insert_eq
    (Σ : lty_env) τx τ v x :
  Σ !! LVFree x = Some (erase_ty τx) ->
  x ∉ fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  lty_env_restrict_lvars Σ (relevant_lvars τx (tret (vfvar x))) =
  lty_env_restrict_lvars
    (<[LVFree x := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τ) (tret v)))
    (relevant_lvars τx (tret (vfvar x))).
Proof.
  intros HΣx Hfresh.
  apply storeA_map_eq. intros u.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (u ∈ relevant_lvars τx (tret (vfvar x)))) as [Hu|Hu].
  - destruct u as [k|y].
    + rewrite lookup_insert_ne by congruence.
      unfold relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide
        (LVBound k ∈ relevant_lvars (CTArrow τx τ) (tret v)))
        as [_|Hbad].
      * reflexivity.
      * exfalso. apply Hbad.
        unfold relevant_lvars in Hu |- *.
        cbn [relevant_lvars tm_lvars tm_lvars_at value_lvars_at
          lvar_value_keys context_ty_lvars context_ty_lvars_at] in Hu |- *.
        better_set_solver.
    + destruct (decide (y = x)) as [->|Hyx].
      * rewrite lookup_insert.
        rewrite decide_True by reflexivity.
        exact HΣx.
      * rewrite lookup_insert_ne by congruence.
        unfold relevant_env, lty_env_restrict_lvars.
        rewrite storeA_restrict_lookup.
        destruct (decide
          (LVFree y ∈ relevant_lvars (CTArrow τx τ) (tret v)))
          as [_|Hbad].
        -- reflexivity.
        -- exfalso. apply Hbad.
           unfold relevant_lvars in Hu |- *.
           cbn [relevant_lvars tm_lvars tm_lvars_at value_lvars_at
             lvar_value_keys context_ty_lvars context_ty_lvars_at] in Hu |- *.
           apply elem_of_union_l.
           apply elem_of_union_l.
           apply elem_of_union in Hu as [Hyτx|Hyx_eq].
           ++ exact Hyτx.
           ++ apply elem_of_singleton in Hyx_eq.
              inversion Hyx_eq. congruence.
  - reflexivity.
Qed.

Lemma insert_relevant_env_ret_value_restrict_eq Σ τ v y :
  y ∉ lvars_fv (dom Σ) ∪ fv_cty τ ∪ fv_value v ->
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τ]>
      (relevant_env Σ τ (tret v)))
    (relevant_lvars τ (tret (vfvar y))) =
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τ]> Σ)
    (relevant_lvars τ (tret (vfvar y))).
Proof.
  intros Hy.
  unfold relevant_env, relevant_lvars, lty_env_restrict_lvars.
  apply storeA_map_eq. intros lv.
  rewrite !storeA_restrict_lookup.
  destruct (decide (lv ∈ context_ty_lvars τ ∪ tm_lvars (tret (vfvar y))))
    as [Hvrel|Hvrel]; [|reflexivity].
  destruct (decide (lv = LVFree y)) as [->|Hvy].
  - rewrite !lookup_insert.
    destruct decide as [_|Hbad]; [reflexivity|contradiction].
  - rewrite !lookup_insert_ne by congruence.
    rewrite storeA_restrict_lookup.
    destruct (decide (lv ∈ context_ty_lvars τ ∪ tm_lvars (tret v)))
      as [Hvsrc|Hvsrc]; [reflexivity|].
    exfalso.
    apply elem_of_union in Hvrel as [Hvτ|Hvy_lvars].
    + apply Hvsrc. apply elem_of_union_l. exact Hvτ.
    + cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys]
        in Hvy_lvars.
      apply elem_of_singleton in Hvy_lvars. subst lv.
      contradiction.
Qed.

Lemma lty_env_restrict_open_one_bind_current_eq
    (Σ : lty_env) (D : lvset) x T :
  Σ !! LVFree x = Some T ->
  lc_lvars D ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 x (typed_lty_env_bind Σ T)) D =
  lty_env_restrict_lvars Σ D.
Proof.
  intros HΣx Hlc.
  apply storeA_map_eq. intros v.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ D)) as [Hv|Hv]; [|reflexivity].
  destruct v as [k|y].
  - exfalso. specialize (Hlc (LVBound k) Hv).
    cbn [lc_logic_var_key] in Hlc. exact Hlc.
  - destruct (decide (y = x)) as [->|Hyx].
    + rewrite lty_env_open_one_typed_bind_lookup_current.
      symmetry. exact HΣx.
    + rewrite lty_env_open_one_typed_bind_lookup_free_ne by congruence.
      reflexivity.
Qed.

Lemma lty_env_restrict_open_one_bind_agree_on
    (Σ1 Σ2 : lty_env) (D : lvset) x T :
  lc_lvars D ->
  (forall y,
    LVFree y ∈ D ->
    y <> x ->
    Σ1 !! LVFree y = Σ2 !! LVFree y) ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 x (typed_lty_env_bind Σ1 T)) D =
  lty_env_restrict_lvars
    (lty_env_open_one 0 x (typed_lty_env_bind Σ2 T)) D.
Proof.
  intros Hlc Hagree.
  apply storeA_map_eq. intros v.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ D)) as [Hv|Hv]; [|reflexivity].
  destruct v as [k|y].
  - exfalso. specialize (Hlc (LVBound k) Hv).
    cbn [lc_logic_var_key] in Hlc. exact Hlc.
  - destruct (decide (y = x)) as [->|Hyx].
    + rewrite !lty_env_open_one_typed_bind_lookup_current.
      reflexivity.
    + rewrite !lty_env_open_one_typed_bind_lookup_free_ne by congruence.
      exact (Hagree y Hv Hyx).
Qed.

Lemma lty_env_restrict_open_one_bind_insert_fresh
    (Σ : lty_env) (D : lvset) x y T U :
  lc_lvars D ->
  LVFree x ∉ D ->
  x <> y ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind (<[LVFree x := U]> Σ) T)) D =
  lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σ T)) D.
Proof.
  intros Hlc HxD Hxy.
  eapply lty_env_restrict_open_one_bind_agree_on.
  - exact Hlc.
  - intros z HzD Hzy.
    destruct (decide (z = x)) as [->|Hzx].
    + exfalso. exact (HxD HzD).
    + rewrite lookup_insert_ne by
        (intros Heq; apply Hzx; inversion Heq; reflexivity).
      reflexivity.
Qed.

Lemma lty_env_restrict_open_one_bind_relevant_tapp_eq
    (Σ : lty_env) τ τx v1 x :
  Σ !! LVFree x = Some (erase_ty τx) ->
  lc_value v1 ->
  lty_env_restrict_lvars Σ (tm_lvars (tapp v1 (vfvar x))) =
  lty_env_restrict_lvars
    (relevant_env
      (lty_env_open_one 0 x (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 x τ) (tapp v1 (vfvar x)))
    (tm_lvars (tapp v1 (vfvar x))).
Proof.
  intros HΣx Hlc_v1.
  apply storeA_map_eq. intros u.
  unfold relevant_env, lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (u ∈ tm_lvars (tapp v1 (vfvar x))))
    as [Hu|Hu]; [|reflexivity].
  destruct u as [k|y].
  - pose proof (tm_lvars_lc (tapp v1 (vfvar x))
      ltac:(constructor; [exact Hlc_v1|constructor])) as Hlc_tm.
    specialize (Hlc_tm (LVBound k) Hu).
    cbn [lc_logic_var_key] in Hlc_tm. contradiction.
  - assert (Hyrel :
        LVFree y ∈ relevant_lvars (cty_open 0 x τ)
          (tapp v1 (vfvar x))).
    { unfold relevant_lvars. better_set_solver. }
    rewrite decide_True by exact Hyrel.
    destruct (decide (y = x)) as [->|Hyx].
    + rewrite lty_env_open_one_typed_bind_lookup_current.
      exact HΣx.
    + rewrite lty_env_open_one_typed_bind_lookup_free_ne by congruence.
      reflexivity.
Qed.

Lemma relevant_lvars_ret_fvar_subset_singleton x τ :
  basic_context_ty {[x]} τ ->
  relevant_lvars τ (tret (vfvar x)) ⊆ {[LVFree x]}.
Proof.
  intros Hbasic v Hv.
  pose proof (basic_context_ty_to_lvars _ _ Hbasic) as [Hτ _].
  unfold relevant_lvars in Hv.
  cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hv.
  unfold lvars_of_atoms in Hτ.
  set_solver.
Qed.

Lemma relevant_lvars_basic_open_tprim_fvar_subset op x τ :
  wf_context_ty_at 1 ∅ τ ->
  relevant_lvars ({0 ~> x} τ) (tprim op (vfvar x)) ⊆ {[LVFree x]}.
Proof.
  intros Hwf v Hv.
  pose proof (wf_context_ty_at_to_lvars_shape 1 ∅ τ Hwf) as [Hτ _].
  rewrite lvars_of_atoms_empty in Hτ.
  unfold relevant_lvars in Hv.
  cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hv.
  set_unfold in Hv.
  destruct Hv as [Hv|Hv].
  - destruct (decide (v = LVFree x)) as [->|Hvx].
    { set_solver. }
    assert (Hsmall :
        v ∈ context_ty_lvars (cty_open 0 x τ) ∖ {[LVFree x]}).
    {
      apply elem_of_difference. split; [exact Hv|].
      intros Hin. apply elem_of_singleton in Hin. congruence.
    }
    assert (Hlc_empty : lc_lvars (∅ : lvset)).
    { unfold lc_lvars. set_solver. }
    assert (Hx_empty : LVFree x ∉ (∅ : lvset)).
    { set_solver. }
    pose proof (cty_lvars_open_body_closed_no_fresh
      (∅ : lvset) τ x Hlc_empty Hx_empty Hτ v Hsmall) as Hcontra.
    set_solver.
  - better_set_solver.
Qed.

Lemma atom_env_restrict_singleton_lookup
    (Δ : gmap atom ty) x T :
  Δ !! x = Some T ->
  lty_env_restrict_lvars (atom_env_to_lty_env Δ) ({[LVFree x]}) =
  lty_env_restrict_lvars
    (atom_env_to_lty_env (<[x := T]> (∅ : gmap atom ty))) ({[LVFree x]}).
Proof.
  intros Hlookup.
  unfold lty_env_restrict_lvars.
  rewrite (storeA_restrict_singleton_lookup
    (atom_env_to_lty_env Δ : gmap logic_var ty) (LVFree x) T).
  2:{ rewrite atom_store_to_lvar_store_lookup_free. exact Hlookup. }
  rewrite (storeA_restrict_singleton_lookup
    (atom_env_to_lty_env (<[x := T]> (∅ : gmap atom ty)) : gmap logic_var ty)
    (LVFree x) T).
  2:{
    rewrite atom_store_to_lvar_store_lookup_free.
    exact (map_lookup_insert (∅ : gmap atom ty) x T).
  }
  reflexivity.
Qed.

Lemma atom_env_insert_restrict_singleton
    (Δ : gmap atom ty) x T :
  lty_env_restrict_lvars (atom_env_to_lty_env (<[x := T]> Δ))
    ({[LVFree x]}) =
  lty_env_restrict_lvars
    (atom_env_to_lty_env (<[x := T]> (∅ : gmap atom ty))) ({[LVFree x]}).
Proof.
  apply atom_env_restrict_singleton_lookup.
  apply map_lookup_insert.
Qed.

Lemma atom_env_to_lty_env_dom_free_notin
    (Δ : gmap atom ty) x :
  x ∉ dom Δ ->
  LVFree x ∉ dom (atom_env_to_lty_env Δ).
Proof.
  intros Hx Hbad.
  rewrite atom_store_to_lvar_store_dom in Hbad.
  unfold lvars_of_atoms in Hbad.
  apply elem_of_map in Hbad as [y [Heq Hy]].
  inversion Heq. subst y.
  exact (Hx Hy).
Qed.

Lemma atom_env_to_lty_env_erase_ctx_comma_bind_open_one
    Γ y τ :
  y ∉ dom (erase_ctx Γ) ->
  atom_env_to_lty_env (erase_ctx (CtxComma Γ (CtxBind y τ))) =
  lty_env_open_one 0 y
    (typed_lty_env_bind (atom_env_to_lty_env (erase_ctx Γ)) (erase_ty τ)).
Proof.
  intros Hy.
  rewrite typed_lty_env_bind_open_current.
  - rewrite <- atom_store_to_lvar_store_insert.
    rewrite erase_ctx_comma_bind_fresh by exact Hy.
    reflexivity.
  - apply atom_env_to_lty_env_dom_free_notin. exact Hy.
  - apply atom_store_to_lvar_store_closed.
Qed.

Lemma atom_env_to_lty_env_erase_ctx_star_bind_open_one
    Γ y τ :
  y ∉ dom (erase_ctx Γ) ->
  atom_env_to_lty_env (erase_ctx (CtxStar Γ (CtxBind y τ))) =
  lty_env_open_one 0 y
    (typed_lty_env_bind (atom_env_to_lty_env (erase_ctx Γ)) (erase_ty τ)).
Proof.
  intros Hy.
  rewrite typed_lty_env_bind_open_current.
  - rewrite <- atom_store_to_lvar_store_insert.
    rewrite erase_ctx_star_bind_fresh by exact Hy.
    reflexivity.
  - apply atom_env_to_lty_env_dom_free_notin. exact Hy.
  - apply atom_store_to_lvar_store_closed.
Qed.

Lemma basic_world_formula_atom_env_dom_subset
    (Δ : gmap atom ty) (m : WfWorldT) :
  m ⊨ basic_world_formula (atom_env_to_lty_env Δ) ->
  dom Δ ⊆ world_dom (m : WorldT).
Proof.
  intros Hworld.
  apply basic_world_formula_models_iff in Hworld as [_ [Hdom _]].
  rewrite atom_store_to_lvar_store_dom, lvars_fv_of_atoms in Hdom.
  exact Hdom.
Qed.

Lemma basic_world_formula_singleton_free_closed_on
    y T (m : WfWorldT) :
  m ⊨ basic_world_formula
    ((<[LVFree y := T]> (∅ : gmap logic_var ty)) : lty_env) ->
  wfworld_closed_on ({[y]} : aset) m.
Proof.
  intros Hworld.
  eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
  rewrite dom_insert, dom_empty_L.
  unfold lvars_of_atoms. set_solver.
Qed.

Lemma atom_env_to_lty_env_erase_ctx_union_subenv
    (Σ : gmap atom ty) Γ v T :
  basic_ctx (dom Σ) Γ ->
  atom_env_to_lty_env (erase_ctx Γ) !! v = Some T ->
  atom_env_to_lty_env (Σ ∪ erase_ctx Γ) !! v = Some T.
Proof.
  intros Hbasic Hlook.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ Hbasic) as HdomΓ.
  pose proof (basic_ctx_dom_fresh (dom Σ) Γ Hbasic) as HfreshΓ.
  destruct v as [k|x].
  - rewrite atom_store_to_lvar_store_lookup_bound_none in Hlook.
    discriminate.
  - rewrite atom_store_to_lvar_store_lookup_free in Hlook.
    rewrite atom_store_to_lvar_store_lookup_free.
    apply map_lookup_union_Some_raw. right.
    split; [|exact Hlook].
    apply not_elem_of_dom.
    apply elem_of_dom_2 in Hlook.
    rewrite HdomΓ in Hlook.
    better_set_solver.
Qed.

Lemma erase_ctx_union_lookup_local_of_basic_ctx
    (Σ : gmap atom ty) Γ x :
  basic_ctx (dom Σ) Γ ->
  x ∈ dom (erase_ctx Γ) ->
  (erase_ctx Γ : gmap atom ty) !! x =
  (Σ ∪ erase_ctx Γ : gmap atom ty) !! x.
Proof.
  intros Hbasic HxΓ.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ Hbasic) as HdomΓ.
  pose proof (basic_ctx_dom_fresh (dom Σ) Γ Hbasic) as HfreshΓ.
  symmetry.
  apply lookup_union_r.
  apply not_elem_of_dom. intros HxΣ.
  rewrite HdomΓ in HxΓ.
  better_set_solver.
Qed.

Lemma relevant_env_erase_ctx_union_subenv
    (Σ : gmap atom ty) Γ τ e v T :
  basic_ctx (dom Σ) Γ ->
  relevant_env (atom_env_to_lty_env (erase_ctx Γ)) τ e !! v = Some T ->
  atom_env_to_lty_env (Σ ∪ erase_ctx Γ) !! v = Some T.
Proof.
  intros Hbasic Hlook.
  unfold relevant_env, lty_env_restrict_lvars in Hlook.
  apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
  eapply atom_env_to_lty_env_erase_ctx_union_subenv; eauto.
Qed.

Lemma lty_singleton_subenv_relevant_ret
    (Σ : lty_env) τ y T v U :
  (<[LVFree y := T]> (∅ : lty_env)) !! v = Some U ->
  relevant_env (<[LVFree y := T]> Σ) τ (tret (vfvar y)) !! v = Some U.
Proof.
  intros Hv.
  change (((<[LVFree y := T]> (∅ : gmap logic_var ty))
    : gmap logic_var ty) !! v = Some U) in Hv.
  destruct v as [k|z].
  - rewrite lookup_insert_ne in Hv by discriminate.
    rewrite lookup_empty in Hv. discriminate.
  - destruct (decide (z = y)) as [->|Hzy].
    + change ((<[LVFree y := T]> (∅ : gmap logic_var ty) : gmap logic_var ty)
          !! LVFree y = Some U) in Hv.
      rewrite lookup_insert_eq in Hv. inversion Hv. subst U.
      unfold relevant_env, lty_env_restrict_lvars.
      apply storeA_restrict_lookup_some_2.
      * apply map_lookup_insert.
      * unfold relevant_lvars.
        cbn [tm_lvars tm_lvars_at value_lvars value_lvars_at].
        set_solver.
    + rewrite lookup_insert_ne in Hv by congruence.
      rewrite lookup_empty in Hv. discriminate.
Qed.

Lemma lty_env_restrict_lvars_twice_subset (Σ : lty_env) X Y :
  Y ⊆ X ->
  lty_env_restrict_lvars (lty_env_restrict_lvars Σ X) Y =
  lty_env_restrict_lvars Σ Y.
Proof.
  intros HYX.
  unfold lty_env_restrict_lvars.
  apply storeA_restrict_twice_subset. exact HYX.
Qed.

Lemma relevant_env_idemp (Σ : lty_env) τ e :
  relevant_env (relevant_env Σ τ e) τ e =
	  relevant_env Σ τ e.
Proof.
  unfold relevant_env.
  unfold lty_env_restrict_lvars.
  apply storeA_restrict_twice_same.
Qed.

Lemma relevant_env_restrict_subset (Σ : lty_env) τ e X :
  X ⊆ relevant_lvars τ e ->
  lty_env_restrict_lvars (relevant_env Σ τ e) X =
  lty_env_restrict_lvars Σ X.
Proof.
  unfold relevant_env.
  apply lty_env_restrict_lvars_twice_subset.
Qed.

Lemma relevant_env_dom_subset_direct (Σ : lty_env) τ e :
  dom (relevant_env Σ τ e : lty_env) ⊆
  dom (Σ : gmap logic_var ty).
Proof.
  intros v Hv.
  apply elem_of_dom in Hv as [T Hlookup].
  unfold relevant_env, lty_env_restrict_lvars in Hlookup.
  apply storeA_restrict_lookup_some in Hlookup as [_ Hlookup].
  eapply elem_of_dom_2. exact Hlookup.
Qed.

Lemma relevant_env_lookup_mono_context
    (Σ : lty_env) τsmall τbig e v T :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  relevant_env Σ τsmall e !! v = Some T ->
  relevant_env Σ τbig e !! v = Some T.
Proof.
  intros Hτ Hlookup.
  unfold relevant_env, lty_env_restrict_lvars,
    relevant_lvars in Hlookup |- *.
  apply storeA_restrict_lookup_some in Hlookup as [Hv HΣ].
  apply storeA_restrict_lookup_some_2; [exact HΣ | set_solver].
Qed.

Lemma relevant_env_dom_mono_context
    (Σ : lty_env) τsmall τbig e :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  dom (relevant_env Σ τsmall e) ⊆
  dom (relevant_env Σ τbig e).
Proof.
  intros Hτ v Hv.
  apply elem_of_dom in Hv as [T Hlookup].
  apply elem_of_dom. exists T.
  eapply relevant_env_lookup_mono_context; eauto.
Qed.

Lemma basic_world_relevant_mono_context
    (Σ : lty_env) τsmall τbig e (m : WfWorldT) :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  m ⊨ basic_world_formula (relevant_env Σ τbig e) ->
  m ⊨ basic_world_formula (relevant_env Σ τsmall e).
Proof.
  intros Hτ Hworld.
  apply basic_world_formula_models_iff in Hworld
    as [Hlc_big [Hscope_big Htyped_big]].
  apply basic_world_formula_models_iff.
  pose proof (relevant_env_dom_mono_context Σ τsmall τbig e Hτ)
    as Hdom.
  split.
  - intros v Hv. apply Hlc_big. exact (Hdom v Hv).
  - split.
    + intros a Ha.
      apply Hscope_big.
      apply lvars_fv_elem in Ha.
      apply lvars_fv_elem. exact (Hdom (LVFree a) Ha).
    + unfold lworld_has_type, worldA_has_type in Htyped_big |- *.
      destruct Htyped_big as [Hdom_big Hstores_big].
      split.
      * intros v Hv. apply Hdom_big. exact (Hdom v Hv).
      * intros σ Hσ v T val HΣv Hσv.
        eapply Hstores_big; [exact Hσ| |exact Hσv].
        eapply relevant_env_lookup_mono_context; eauto.
Qed.

Lemma relevant_lvars_open k y τ e :
  y ∉ fv_tm e ->
  lvars_open k y (relevant_lvars τ e) =
  relevant_lvars (cty_open k y τ) (open_tm k (vfvar y) e).
Proof.
  intros Hy.
  unfold relevant_lvars.
  rewrite lvars_open_union.
  rewrite cty_open_vars.
  rewrite tm_lvars_open by exact Hy.
  reflexivity.
Qed.

Lemma relevant_env_open_one k y Σ τ e :
  y ∉ fv_tm e ->
  lty_env_open_one k y (relevant_env Σ τ e) =
  relevant_env (lty_env_open_one k y Σ)
    (cty_open k y τ) (open_tm k (vfvar y) e).
Proof.
  intros Hy.
  unfold relevant_env, lty_env_restrict_lvars, lty_env_open_one.
  rewrite <- relevant_lvars_open by exact Hy.
  symmetry. apply storeA_restrict_swap.
Qed.

Lemma relevant_env_open_env η Σ τ e :
  open_env_fresh_for_lvars η (dom Σ ∪ relevant_lvars τ e) ->
  open_env_values_inj η ->
  lty_env_open_lvars η (relevant_env Σ τ e) =
  relevant_env (lty_env_open_lvars η Σ)
    (open_cty_env η τ) (open_tm_env η e).
Proof.
  revert Σ τ e.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros Σ τ e _ _.
    rewrite lty_env_open_lvars_empty, open_cty_env_empty.
    rewrite (lty_env_open_lvars_empty Σ).
    rewrite map_fold_empty. reflexivity.
  - intros Σ τ e Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    assert (Hfreshη :
      open_env_fresh_for_lvars η (dom Σ ∪ relevant_lvars τ e)).
    { eapply open_env_fresh_for_lvars_insert_tail; eassumption. }
    rewrite lty_env_open_lvars_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2:{
      eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
      unfold relevant_env, lty_env_restrict_lvars.
      intros v Hv.
      apply elem_of_dom in Hv as [Tv Hlook].
      apply storeA_restrict_lookup_some in Hlook as [Hvrel HΣv].
      apply elem_of_union.
      left. eapply elem_of_dom_2. exact HΣv.
    }
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite open_cty_env_insert_fresh by (exact Hnone || exact Havoid || exact Hinjη).
    rewrite open_tm_env_insert_fresh_plain by exact Hnone.
    rewrite lty_env_open_lvars_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2:{
      eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
      intros v Hv. set_solver.
    }
    rewrite relevant_env_open_one.
    + reflexivity.
    + rewrite <- tm_lvars_fv.
      rewrite tm_lvars_open_tm_env.
      * pose proof (open_env_fresh_for_lvars_insert_head η k x
          (dom Σ ∪ relevant_lvars τ e) Hnone Hfresh) as Hhead.
        intros Hbad. apply Hhead.
        eapply lvars_fv_mono; [|exact Hbad].
        apply lvars_open_env_mono.
        unfold relevant_lvars. set_solver.
      * eapply open_env_fresh_for_lvars_mono; [|exact Hfreshη].
        unfold relevant_lvars. set_solver.
Qed.

Lemma lty_env_restrict_lvars_closed Σ D :
  lty_env_closed Σ ->
  lty_env_closed (lty_env_restrict_lvars Σ D).
Proof.
  intros Hclosed.
  unfold lty_env_closed in *.
  intros v Hv.
  unfold lty_env_restrict_lvars in Hv.
  pose proof (storeA_restrict_dom (Σ : lty_env) D) as Hdom_restrict.
  rewrite Hdom_restrict in Hv.
  apply elem_of_intersection in Hv as [Hv _].
  exact (Hclosed v Hv).
Qed.

Lemma relevant_env_closed Σ τ e :
  lty_env_closed Σ ->
  lty_env_closed (relevant_env Σ τ e).
Proof.
  apply lty_env_restrict_lvars_closed.
Qed.

Lemma lty_env_to_atom_env_restrict_lvars_lookup Σ D x :
  LVFree x ∈ D ->
  lty_env_to_atom_env (lty_env_restrict_lvars Σ D) !! x =
  lty_env_to_atom_env Σ !! x.
Proof.
  intros HxD.
  rewrite !lvar_store_to_atom_store_lookup.
  unfold lty_env_restrict_lvars.
  destruct ((Σ : gmap logic_var ty) !! LVFree x) as [T|] eqn:HΣ.
  - apply storeA_restrict_lookup_some_2; assumption.
  - apply storeA_restrict_lookup_none_l. exact HΣ.
Qed.

Lemma basic_typing_restrict_lvars_to_atom_env Σ D e T :
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

Lemma basic_typing_lty_env_to_atom_env_relevant Σ τ e T :
  lty_env_to_atom_env Σ ⊢ₑ e ⋮ T ->
  lty_env_to_atom_env (relevant_env Σ τ e) ⊢ₑ e ⋮ T.
Proof.
  intros Hty.
  unfold relevant_env, relevant_lvars.
  eapply basic_typing_restrict_lvars_to_atom_env; [|exact Hty].
  set_solver.
Qed.

Lemma basic_context_ty_lvars_relevant_env Σ τ e :
  basic_context_ty_lvars (dom Σ) τ ->
  basic_context_ty_lvars (dom (relevant_env Σ τ e)) τ.
Proof.
  intros [Hvars Hshape]. split; [|exact Hshape].
  intros v Hv.
  unfold relevant_env, lty_env_restrict_lvars, relevant_lvars.
  rewrite storeA_restrict_dom.
  apply elem_of_intersection. split; [apply Hvars; exact Hv|set_solver].
Qed.

Lemma context_ty_wf_formula_relevant_env
    Σ τ e (m : WfWorldT) :
  m ⊨ basic_world_formula (relevant_env Σ τ e) ->
  m ⊨ context_ty_wf_formula Σ τ ->
  m ⊨ context_ty_wf_formula (relevant_env Σ τ e) τ.
Proof.
  intros Hworld Hwf.
  apply basic_world_formula_models_iff in Hworld
    as [Hlc [Hscope _]].
  apply context_ty_wf_formula_models_iff in Hwf
    as [_ [_ Hbasicτ]].
  apply context_ty_wf_formula_models_iff.
  split; [exact Hlc|]. split; [exact Hscope|].
  apply basic_context_ty_lvars_relevant_env.
  exact Hbasicτ.
Qed.

Lemma context_ty_wf_formula_relevant_env_change_term
    Σ τ e1 e2 (m : WfWorldT) :
  m ⊨ basic_world_formula (relevant_env Σ τ e2) ->
  m ⊨ context_ty_wf_formula (relevant_env Σ τ e1) τ ->
  m ⊨ context_ty_wf_formula (relevant_env Σ τ e2) τ.
Proof.
  intros Hworld Hwf.
  apply basic_world_formula_models_iff in Hworld
    as [Hlc [Hscope _]].
  apply context_ty_wf_formula_models_iff in Hwf
    as [_ [_ Hbasicτ]].
  apply context_ty_wf_formula_models_iff.
  split; [exact Hlc|]. split; [exact Hscope|].
  apply basic_context_ty_lvars_relevant_env.
  eapply basic_context_ty_lvars_mono; [|exact Hbasicτ].
  unfold relevant_env, lty_env_restrict_lvars.
  rewrite storeA_restrict_dom.
  set_solver.
Qed.

Lemma basic_context_ty_atom_env_relevant_env
    (Δ : gmap atom ty) τ e :
  basic_context_ty (dom Δ) τ ->
  basic_context_ty_lvars
    (dom (relevant_env (atom_env_to_lty_env Δ) τ e)) τ.
Proof.
  intros Hτ.
  apply basic_context_ty_lvars_relevant_env.
  rewrite atom_store_to_lvar_store_dom.
  apply basic_context_ty_to_lvars. exact Hτ.
Qed.

Lemma lty_env_restrict_lvars_fv_subset Σ D :
  lvars_fv (dom (lty_env_restrict_lvars Σ D)) ⊆ lvars_fv D.
Proof.
  unfold lty_env_restrict_lvars.
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
  apply storeA_restrict_insert_notin. exact HxD.
Qed.

Lemma relevant_env_insert_fresh Σ τ e x T :
  LVFree x ∉ relevant_lvars τ e ->
  relevant_env (<[LVFree x := T]> Σ) τ e =
  relevant_env Σ τ e.
Proof.
  intros Hx.
  unfold relevant_env.
  apply lty_env_restrict_lvars_insert_fresh.
  exact Hx.
Qed.

Lemma relevant_env_fv_subset Σ τ e :
  lvars_fv (dom (relevant_env Σ τ e)) ⊆
  fv_cty τ ∪ fv_tm e.
Proof.
  unfold relevant_env, relevant_lvars.
  transitivity (lvars_fv (context_ty_lvars τ ∪ tm_lvars e)).
  - apply lty_env_restrict_lvars_fv_subset.
  - rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv.
    set_solver.
Qed.

Lemma relevant_world_closed_on_term_lvars_eq
    (Σ : lty_env) τ e_src e_tgt (m : WfWorldT) :
  tm_lvars e_tgt = tm_lvars e_src ->
  m ⊨ basic_world_formula (relevant_env Σ τ e_src) ->
  m ⊨ expr_basic_typing_formula
    (relevant_env Σ τ e_src) e_src (erase_ty τ) ->
  wfworld_closed_on (fv_tm e_tgt) m.
Proof.
  intros Hlvars Hworld Hbasic.
  eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
  unfold relevant_env, relevant_lvars, lty_env_restrict_lvars.
  rewrite storeA_restrict_dom.
  intros v Hv.
  unfold lvars_of_atoms in Hv.
  apply elem_of_map in Hv as [a [-> Ha]].
  apply elem_of_intersection. split.
  - pose proof (expr_basic_typing_formula_basic_ltype _ _ _ _ Hbasic)
      as Hbasic_ltype.
    pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_ltype) as Hsub.
    assert (Ha_lvars : LVFree a ∈ lvars_of_atoms (fv_tm e_src)).
    {
      unfold lvars_of_atoms.
      apply elem_of_map. exists a. split; [reflexivity|].
      rewrite <- (tm_lvars_fv e_src).
      rewrite <- Hlvars.
      rewrite (tm_lvars_fv e_tgt).
      exact Ha.
    }
    specialize (Hsub _ Ha_lvars).
    unfold relevant_env, relevant_lvars,
      lty_env_restrict_lvars in Hsub.
    rewrite storeA_restrict_dom in Hsub.
    apply elem_of_intersection in Hsub as [HaΣ _].
    exact HaΣ.
  - apply elem_of_union_r.
    rewrite <- Hlvars.
    apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
Qed.

Lemma relevant_world_typing_closed_on_term
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ basic_world_formula (relevant_env Σ τ e) ->
  m ⊨ expr_basic_typing_formula
    (relevant_env Σ τ e) e (erase_ty τ) ->
  wfworld_closed_on (fv_tm e) m.
Proof.
  eapply relevant_world_closed_on_term_lvars_eq.
  reflexivity.
Qed.

Lemma relevant_lvars_insert_fresh x τ e :
  LVFree x ∉ context_ty_lvars τ ->
  x ∉ fv_tm e ->
  LVFree x ∉ relevant_lvars τ e.
Proof.
  intros Hxτ Hxe.
  unfold relevant_lvars.
  pose proof (tm_lvars_free_notin_of_fv x e Hxe).
  set_solver.
Qed.

Lemma lty_restrict_insert_relevant_eq
    Σ τ e X y T :
  X ∖ {[LVFree y]} ⊆ relevant_lvars τ e ->
  lty_env_restrict_lvars
    (<[LVFree y := T]> (relevant_env Σ τ e)) X =
  lty_env_restrict_lvars (<[LVFree y := T]> Σ) X.
Proof.
  intros Hsub.
  unfold lty_env_restrict_lvars, relevant_env.
  apply storeA_map_eq. intros v.
  change ((storeA_restrict
    (<[LVFree y := T]>
      (storeA_restrict (Σ : gmap logic_var ty) (relevant_lvars τ e)
        : gmap logic_var ty)) X : gmap logic_var ty) !! v =
    (storeA_restrict (<[LVFree y := T]> (Σ : gmap logic_var ty)) X
      : gmap logic_var ty) !! v).
  rewrite (storeA_restrict_lookup
    (<[LVFree y := T]>
      (storeA_restrict (Σ : gmap logic_var ty) (relevant_lvars τ e)
        : gmap logic_var ty)) X v).
  rewrite (storeA_restrict_lookup
    (<[LVFree y := T]> (Σ : gmap logic_var ty)) X v).
  destruct (decide (v ∈ X)) as [HvX|HvX]; [|reflexivity].
  destruct (decide (v = LVFree y)) as [->|Hvy].
  - rewrite !lookup_insert_eq. reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    unfold lty_env_restrict_lvars.
    rewrite storeA_restrict_lookup.
    destruct (decide (v ∈ relevant_lvars τ e)) as [_|Hvrel].
    + reflexivity.
    + exfalso. apply Hvrel. apply Hsub. set_solver.
Qed.

Lemma arrow_body_relevant_lvars_subset
    τx τr e_src e_body y :
  context_ty_lvars (cty_open 0 y τr) ∖ {[LVFree y]} ⊆
    context_ty_lvars_at 1 τr ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  relevant_lvars (cty_open 0 y τr) e_body ∖ {[LVFree y]} ⊆
  relevant_lvars (CTArrow τx τr) e_src.
Proof.
  intros Hτ He.
  unfold relevant_lvars.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma arrow_body_relevant_env_agree
    (Σsrc : lty_env) Ty y τx τr e_src e_body :
  context_ty_lvars (cty_open 0 y τr) ∖ {[LVFree y]} ⊆
    context_ty_lvars_at 1 τr ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  lty_env_restrict_lvars
    (<[LVFree y := Ty]>
      (relevant_env Σsrc (CTArrow τx τr) e_src))
    (relevant_lvars (cty_open 0 y τr) e_body) =
  lty_env_restrict_lvars (<[LVFree y := Ty]> Σsrc)
    (relevant_lvars (cty_open 0 y τr) e_body).
Proof.
  intros Hτ He.
  apply lty_restrict_insert_relevant_eq.
  eapply arrow_body_relevant_lvars_subset; eauto.
Qed.

Lemma arrow_body_env_agree
    (Σsrc : lty_env) Ty y τx τr e_src e_body :
  lc_lvars (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  LVFree y ∉ (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  basic_context_ty_lvars
    (dom (Σsrc : gmap logic_var ty) : gset logic_var) (CTArrow τx τr) ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  lty_env_restrict_lvars
    (<[LVFree y := Ty]>
      (relevant_env Σsrc (CTArrow τx τr) e_src))
    (relevant_lvars (cty_open 0 y τr) e_body) =
  lty_env_restrict_lvars (<[LVFree y := Ty]> Σsrc)
    (relevant_lvars (cty_open 0 y τr) e_body).
Proof.
  intros Hlc HyΣ Hbasic He.
  apply arrow_body_relevant_env_agree; [|exact He].
  apply cty_lvars_open_body_closed_no_fresh
    with (D := (dom (Σsrc : gmap logic_var ty) : gset logic_var)).
  - exact Hlc.
  - exact HyΣ.
  - destruct Hbasic as [Hvars _].
    cbn [context_ty_lvars context_ty_lvars_at] in Hvars.
    set_solver.
Qed.

Lemma arrow_body_world_from_source_arg
    (Σsrc : lty_env) Ty y τx τr e_src e_body (m : WfWorldT) :
  lc_lvars (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  LVFree y ∉ (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  basic_context_ty_lvars
    (dom (Σsrc : gmap logic_var ty) : gset logic_var) (CTArrow τx τr) ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  m ⊨ basic_world_formula (relevant_env Σsrc (CTArrow τx τr) e_src) ->
  m ⊨ basic_world_formula
    ((<[LVFree y := Ty]> (∅ : gmap logic_var ty)) : lty_env) ->
  m ⊨ basic_world_formula
    (relevant_env (<[LVFree y := Ty]> Σsrc)
      (cty_open 0 y τr) e_body).
Proof.
  intros Hlc HyΣ Hbasic He Hsrc Hy.
  pose proof (basic_world_formula_union
    (relevant_env Σsrc (CTArrow τx τr) e_src)
    ((<[LVFree y := Ty]> (∅ : gmap logic_var ty)) : lty_env)
    m Hsrc Hy) as Hunion.
  eapply basic_world_formula_subenv; [|exact Hunion].
  intros v Tv Hlook.
  pose proof (arrow_body_env_agree
    Σsrc Ty y τx τr e_src e_body Hlc HyΣ Hbasic He) as Hagree.
  change ((lty_env_restrict_lvars (<[LVFree y := Ty]> Σsrc)
    (relevant_lvars (cty_open 0 y τr) e_body) : lty_env) !!
    v = Some Tv) in Hlook.
  rewrite <- Hagree in Hlook.
  unfold lty_env_restrict_lvars in Hlook.
  change ((storeA_restrict
    (<[LVFree y := Ty]>
      (relevant_env Σsrc (CTArrow τx τr) e_src))
    (relevant_lvars (cty_open 0 y τr) e_body)
    : gmap logic_var ty) !! v = Some Tv) in Hlook.
  apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
  assert (Hyrel : LVFree y ∉ dom
    (relevant_env Σsrc (CTArrow τx τr) e_src : lty_env)).
  {
    intros Hyrel.
    change (LVFree y ∈ dom
      ((relevant_env Σsrc (CTArrow τx τr) e_src : lty_env)
        : gmap logic_var ty)) in Hyrel.
    apply elem_of_dom in Hyrel as [Ty' Hrel].
    unfold relevant_env, lty_env_restrict_lvars in Hrel.
    change ((storeA_restrict Σsrc
      (relevant_lvars (CTArrow τx τr) e_src)
      : gmap logic_var ty) !! LVFree y = Some Ty') in Hrel.
    apply storeA_restrict_lookup_some in Hrel as [_ HΣ].
    apply HyΣ. eapply elem_of_dom_2. exact HΣ.
  }
  change ((((relevant_env Σsrc (CTArrow τx τr) e_src : lty_env)
    : gmap logic_var ty) ∪
    (<[LVFree y := Ty]> (∅ : gmap logic_var ty))) !! v = Some Tv).
  change (<[LVFree y := Ty]> (∅ : gmap logic_var ty))
    with ({[LVFree y := Ty]} : gmap logic_var ty).
  rewrite storeA_union_singleton_insert_fresh by exact Hyrel.
  exact Hlook.
Qed.

Lemma wand_body_world_from_source_arg
    (Σsrc : lty_env) Ty y τx τr e_src e_body (m : WfWorldT) :
  lc_lvars (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  LVFree y ∉ (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  basic_context_ty_lvars
    (dom (Σsrc : gmap logic_var ty) : gset logic_var) (CTWand τx τr) ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  m ⊨ basic_world_formula (relevant_env Σsrc (CTWand τx τr) e_src) ->
  m ⊨ basic_world_formula
    ((<[LVFree y := Ty]> (∅ : gmap logic_var ty)) : lty_env) ->
  m ⊨ basic_world_formula
    (relevant_env (<[LVFree y := Ty]> Σsrc)
      (cty_open 0 y τr) e_body).
Proof.
  intros Hlc HyΣ Hbasic He Hsrc Hy.
  change (relevant_env Σsrc (CTWand τx τr) e_src)
    with (relevant_env Σsrc (CTArrow τx τr) e_src) in Hsrc.
  eapply arrow_body_world_from_source_arg; eauto.
Qed.

Lemma wand_body_relevant_env_agree_open_one_core
    (Σsrc : lty_env) Ty y τx τr e_src e_body :
  y ∉ fv_cty τr ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ lvars_shift_from 0 (tm_lvars e_src) ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σsrc (CTWand τx τr) e_src) Ty))
    (relevant_lvars (cty_open 0 y τr) e_body) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σsrc Ty))
    (relevant_lvars (cty_open 0 y τr) e_body).
Proof.
  intros Hyτr He.
  set (X := relevant_lvars (cty_open 0 y τr) e_body).
  apply storeA_map_eq. intros v.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ X)) as [HvX|HvX]; [|reflexivity].
  unfold lty_env_open_one, lvar_store_open_one.
  replace v with (logic_var_open 0 y (logic_var_open 0 y v))
    by exact (logic_var_open_involutive 0 y v).
  rewrite !storeA_rekey_lookup by apply swap_inj.
  unfold typed_lty_env_bind, lvar_store_bind.
  set (u := logic_var_open 0 y v).
  fold u.
  destruct u as [k|z] eqn:Hu.
  - destruct k as [|k].
    + rewrite !lookup_insert_eq. reflexivity.
    + cbn [insert].
      rewrite !lookup_insert_ne by discriminate.
      assert (Hv_eq : v = LVBound (S k)).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVBound (S k))) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from.
      replace (LVBound (S k)) with (logic_var_shift_from 0 (LVBound k))
        by reflexivity.
      rewrite !storeA_rekey_lookup by apply logic_var_shift_from_inj.
      unfold relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide (LVBound k ∈ relevant_lvars
        (CTWand τx τr) e_src)) as [Hrel|Hrel]; [reflexivity|].
      exfalso. apply Hrel.
      subst X.
      unfold relevant_lvars in *.
      cbn [tm_lvars tm_lvars_at value_lvars_at] in *.
      apply elem_of_union in HvX as [Hτopen|Hebody].
      * assert (Hbody : LVBound k ∈ context_ty_lvars_at 1 τr).
        {
          rewrite <- (context_ty_lvars_depth τr 1).
          apply lvars_at_depth_elem.
          exists (LVBound (S k)). split.
          - rewrite cty_open_vars in Hτopen.
            unfold context_ty_open_lvars in Hτopen.
            rewrite set_swap_elem in Hτopen.
            rewrite (swap_fresh (LVBound 0) (LVFree y) (LVBound (S k)))
              in Hτopen by congruence.
            exact Hτopen.
          - cbn [logic_var_at_depth].
            rewrite decide_True by lia.
            replace (S k - 1) with k by lia.
            reflexivity.
        }
        cbn [relevant_lvars context_ty_lvars context_ty_lvars_at].
        set_solver.
      * assert (Hbody : LVBound k ∈ tm_lvars e_src).
        {
          assert (Hshift : LVBound (S k) ∈ lvars_shift_from 0 (tm_lvars e_src)).
          {
            apply He. apply elem_of_difference. split; [exact Hebody|].
            set_solver.
          }
          unfold lvars_shift_from in Hshift.
          apply elem_of_map in Hshift as [w [Hwshift Hw]].
          destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift.
          - destruct (decide (0 <= n)); [|lia].
            inversion Hwshift. subst n. exact Hw.
          - discriminate.
        }
        cbn [relevant_lvars context_ty_lvars context_ty_lvars_at].
        set_solver.
  - destruct (decide (z = y)) as [->|Hzy].
    + exfalso.
      unfold u in Hu.
      assert (Hv_eq : v = LVBound 0).
      {
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVFree y)) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      subst X.
      unfold relevant_lvars in *.
      cbn [tm_lvars tm_lvars_at value_lvars_at] in *.
      apply elem_of_union in HvX as [Hτopen|Hebody].
      * apply Hyτr.
        change (y ∈ lvars_fv (context_ty_lvars τr)).
        rewrite context_ty_lvars_fv.
        apply lvars_fv_elem.
        rewrite cty_open_vars in Hτopen.
        unfold context_ty_open_lvars in Hτopen.
        rewrite set_swap_elem in Hτopen.
        rewrite swap_l in Hτopen.
        exact Hτopen.
      * assert (Hshift : LVBound 0 ∈ lvars_shift_from 0 (tm_lvars e_src)).
        {
          apply He. apply elem_of_difference. split; [exact Hebody|].
          set_solver.
        }
        unfold lvars_shift_from in Hshift.
        apply elem_of_map in Hshift as [w [Hwshift _]].
        destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift.
        -- destruct (decide (0 <= n)); [|lia].
           inversion Hwshift.
        -- discriminate.
    + rewrite !lookup_insert_ne by congruence.
      assert (Hv_eq : v = LVFree z).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVFree z)) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from.
      replace (LVFree z) with (logic_var_shift_from 0 (LVFree z))
        by reflexivity.
      rewrite !storeA_rekey_lookup by apply logic_var_shift_from_inj.
      unfold relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide (LVFree z ∈ relevant_lvars
        (CTWand τx τr) e_src)) as [Hrel|Hrel]; [reflexivity|].
      exfalso. apply Hrel.
      subst X.
      unfold relevant_lvars in *.
      cbn [tm_lvars tm_lvars_at value_lvars_at] in *.
      apply elem_of_union in HvX as [Hτopen|Hebody].
      * assert (Hbody : LVFree z ∈ context_ty_lvars_at 1 τr).
        {
          rewrite <- (context_ty_lvars_depth τr 1).
          apply lvars_at_depth_elem.
          exists (LVFree z). split.
          - rewrite cty_open_vars in Hτopen.
            unfold context_ty_open_lvars in Hτopen.
            rewrite set_swap_elem in Hτopen.
            rewrite (swap_fresh (LVBound 0) (LVFree y) (LVFree z))
              in Hτopen by congruence.
            exact Hτopen.
          - reflexivity.
        }
        cbn [relevant_lvars context_ty_lvars context_ty_lvars_at].
        set_solver.
      * assert (Hbody : LVFree z ∈ tm_lvars e_src).
        {
          assert (Hshift : LVFree z ∈ lvars_shift_from 0 (tm_lvars e_src)).
          {
            apply He. apply elem_of_difference. split; [exact Hebody|].
            set_solver.
          }
          unfold lvars_shift_from in Hshift.
          apply elem_of_map in Hshift as [w [Hwshift Hw]].
          destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift.
          - destruct (decide (0 <= n)); discriminate.
          - inversion Hwshift. subst a. exact Hw.
        }
        cbn [relevant_lvars context_ty_lvars context_ty_lvars_at].
        set_solver.
Qed.

Lemma arrow_body_relevant_env_agree_open_one_core
    (Σsrc : lty_env) Ty y τx τr e_src e_body :
  y ∉ fv_cty τr ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ lvars_shift_from 0 (tm_lvars e_src) ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σsrc (CTArrow τx τr) e_src) Ty))
    (relevant_lvars (cty_open 0 y τr) e_body) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σsrc Ty))
    (relevant_lvars (cty_open 0 y τr) e_body).
Proof.
  intros Hyτr He.
  change (relevant_env Σsrc (CTArrow τx τr) e_src)
    with (relevant_env Σsrc (CTWand τx τr) e_src).
  apply wand_body_relevant_env_agree_open_one_core; assumption.
Qed.

Lemma lvars_at_depth_relevant_env_subset_relevant d Σ τ e :
  lvars_at_depth d (dom (relevant_env Σ τ e)) ⊆
  context_ty_lvars_at d τ ∪ tm_lvars_at d e.
Proof.
  unfold relevant_env, lty_env_restrict_lvars, relevant_lvars.
  change (lvars_at_depth d
    (dom (storeA_restrict (Σ : gmap logic_var ty)
      (context_ty_lvars τ ∪ tm_lvars e))) ⊆
    context_ty_lvars_at d τ ∪ tm_lvars_at d e).
  rewrite storeA_restrict_dom.
  transitivity (lvars_at_depth d (context_ty_lvars τ ∪ tm_lvars e)).
  - apply lvars_at_depth_mono. set_solver.
  - rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
    set_solver.
Qed.

Lemma lvars_at_depth_arrow_arg_lift_support_subset Σ τx τr e :
  lvars_at_depth 1
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx)) ∪
     relevant_lvars (cty_shift 0 τx) (tret (vbvar 0))) ⊆
  dom Σ ∪ relevant_lvars (CTArrow τx τr) e.
Proof.
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_typed_lty_env_bind.
  pose proof (lvars_at_depth_relevant_env_subset_relevant
    0 Σ (CTArrow τx τr) e) as Hrel.
  unfold relevant_lvars.
  rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
  rewrite context_ty_lvars_at_shift_under by lia.
  rewrite tm_lvars_at_tret_bound0_under.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma arrow_body_lvars_lift_support_subset Σ τx τr e :
  lvars_at_depth 1
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx)) ∪
     relevant_lvars τr (tapp_tm (tm_shift 0 e) (vbvar 0))) ⊆
  dom Σ ∪ relevant_lvars (CTArrow τx τr) e.
Proof.
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_typed_lty_env_bind.
  pose proof (lvars_at_depth_relevant_env_subset_relevant
    0 Σ (CTArrow τx τr) e) as Hrel.
  pose proof (tm_lvars_at_tapp_shift0_bound0 e 0) as Htapp.
  unfold relevant_lvars.
  rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma lvars_at_depth_wand_arg_lift_support_subset Σ τx τr e :
  lvars_at_depth 1
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e) (erase_ty τx)) ∪
     relevant_lvars (cty_shift 0 τx) (tret (vbvar 0))) ⊆
  dom Σ ∪ relevant_lvars (CTWand τx τr) e.
Proof.
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_typed_lty_env_bind.
  pose proof (lvars_at_depth_relevant_env_subset_relevant
    0 Σ (CTWand τx τr) e) as Hrel.
  unfold relevant_lvars.
  rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
  rewrite context_ty_lvars_at_shift_under by lia.
  rewrite tm_lvars_at_tret_bound0_under.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma lvars_at_depth_wand_body_lift_support_subset Σ τx τr e :
  lvars_at_depth 1
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e) (erase_ty τx)) ∪
     relevant_lvars τr (tapp_tm (tm_shift 0 e) (vbvar 0))) ⊆
  dom Σ ∪ relevant_lvars (CTWand τx τr) e.
Proof.
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_typed_lty_env_bind.
  pose proof (lvars_at_depth_relevant_env_subset_relevant
    0 Σ (CTWand τx τr) e) as Hrel.
  pose proof (tm_lvars_at_tapp_shift0_bound0 e 0) as Htapp.
  unfold relevant_lvars.
  rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma lvars_at_depth_dom_singleton_bound0_succ d T :
  lvars_at_depth (S d) (dom (<[LVBound 0 := T]> (∅ : lty_env))) = ∅.
Proof.
  rewrite dom_insert_L, dom_empty_L, lvars_at_depth_union.
  rewrite lvars_at_depth_singleton_bound0_succ, lvars_at_depth_empty.
  set_solver.
Qed.

Lemma wand_arg_relevant_env_agree_open_one_core
    (Σsrc : lty_env) Ty y τx τr e_src :
  y ∉ fv_cty τx ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σsrc (CTWand τx τr) e_src) Ty))
    (relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σsrc Ty))
    (relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))).
Proof.
  intros Hyτx.
  set (X := relevant_lvars (cty_open 0 y (cty_shift 0 τx))
    (tret (vfvar y))).
  apply storeA_map_eq. intros v.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ X)) as [HvX|HvX]; [|reflexivity].
  unfold lty_env_open_one, lvar_store_open_one.
  replace v with (logic_var_open 0 y (logic_var_open 0 y v))
    by exact (logic_var_open_involutive 0 y v).
  rewrite !storeA_rekey_lookup by apply swap_inj.
  unfold typed_lty_env_bind, lvar_store_bind.
  set (u := logic_var_open 0 y v).
  fold u.
  destruct u as [k|z] eqn:Hu.
  - destruct k as [|k].
    + rewrite !lookup_insert_eq. reflexivity.
    + cbn [insert].
      rewrite !lookup_insert_ne by discriminate.
      assert (Hv_eq : v = LVBound (S k)).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVBound (S k))) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from.
      replace (LVBound (S k)) with (logic_var_shift_from 0 (LVBound k))
        by reflexivity.
      rewrite !storeA_rekey_lookup by apply logic_var_shift_from_inj.
      unfold relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide (LVBound k ∈ relevant_lvars (CTWand τx τr) e_src))
        as [Hrel|Hrel]; [reflexivity|].
      exfalso. apply Hrel.
      subst X.
      unfold relevant_lvars in *.
      cbn [context_ty_lvars context_ty_lvars_at
        tm_lvars tm_lvars_at value_lvars_at] in *.
      rewrite cty_open_vars in HvX.
      unfold context_ty_open_lvars in HvX.
      rewrite cty_shift_vars in HvX.
      unfold context_ty_shift_lvars in HvX.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      apply elem_of_union_l.
      apply elem_of_union_l.
      apply elem_of_union in HvX as [Hopen|Hret].
      2:{ set_solver. }
      rewrite set_swap_elem in Hopen.
      rewrite (swap_fresh (LVBound 0) (LVFree y) (LVBound (S k))) in Hopen
        by congruence.
      unfold lvars_shift_from in Hopen.
      apply elem_of_map in Hopen as [w [Hwshift Hw]].
      destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift;
        repeat destruct decide; inversion Hwshift; subst; try lia.
      exact Hw.
  - destruct (decide (z = y)) as [->|Hzy].
    + exfalso.
      unfold u in Hu.
      assert (Hv_eq : v = LVBound 0).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVFree y)) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      subst X.
      unfold relevant_lvars in *.
      cbn [context_ty_lvars context_ty_lvars_at
        tm_lvars tm_lvars_at value_lvars_at] in *.
      rewrite cty_open_vars in HvX.
      unfold context_ty_open_lvars in HvX.
      rewrite cty_shift_vars in HvX.
      unfold context_ty_shift_lvars in HvX.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      apply elem_of_union in HvX as [Hopen|Hret].
      { rewrite set_swap_elem in Hopen.
        rewrite swap_l in Hopen.
        apply Hyτx.
        change (y ∈ lvars_fv (context_ty_lvars τx)).
        rewrite <- (lvars_shift_from_fv 0 (context_ty_lvars τx)).
        apply lvars_fv_elem. exact Hopen. }
      { set_solver. }
    + rewrite !lookup_insert_ne by congruence.
      assert (Hv_eq : v = LVFree z).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVFree z)) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from.
      replace (LVFree z) with (logic_var_shift_from 0 (LVFree z))
        by reflexivity.
      rewrite !storeA_rekey_lookup by apply logic_var_shift_from_inj.
      unfold relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide (LVFree z ∈ relevant_lvars (CTWand τx τr) e_src))
        as [Hrel|Hrel]; [reflexivity|].
      exfalso. apply Hrel.
      subst X.
      unfold relevant_lvars in *.
      cbn [context_ty_lvars context_ty_lvars_at
        tm_lvars tm_lvars_at value_lvars_at] in *.
      rewrite cty_open_vars in HvX.
      unfold context_ty_open_lvars in HvX.
      rewrite cty_shift_vars in HvX.
      unfold context_ty_shift_lvars in HvX.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      apply elem_of_union in HvX as [Hopen|Hret].
      { rewrite set_swap_elem in Hopen.
        rewrite (swap_fresh (LVBound 0) (LVFree y) (LVFree z)) in Hopen
          by congruence.
        unfold lvars_shift_from in Hopen.
        apply elem_of_map in Hopen as [w [Hwshift Hw]].
        destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift;
          repeat destruct decide; inversion Hwshift; subst; try lia.
        apply elem_of_union_l. apply elem_of_union_l. exact Hw. }
      { set_solver. }
Qed.

Lemma sum_branch_relevant_env_agree_open_one_core
    (Σsrc : lty_env) Ty y τbranch τsum e_src :
  context_ty_lvars τbranch ⊆ context_ty_lvars τsum ->
  y ∉ fv_cty τbranch ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σsrc τsum e_src) Ty))
    (relevant_lvars (cty_open 0 y (cty_shift 0 τbranch))
      (tret (vfvar y))) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σsrc Ty))
    (relevant_lvars (cty_open 0 y (cty_shift 0 τbranch))
      (tret (vfvar y))).
Proof.
  intros Hτsub Hyτ.
  set (X := relevant_lvars (cty_open 0 y (cty_shift 0 τbranch))
    (tret (vfvar y))).
  apply storeA_map_eq. intros v.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ X)) as [HvX|HvX]; [|reflexivity].
  unfold lty_env_open_one, lvar_store_open_one.
  replace v with (logic_var_open 0 y (logic_var_open 0 y v))
    by exact (logic_var_open_involutive 0 y v).
  rewrite !storeA_rekey_lookup by apply swap_inj.
  unfold typed_lty_env_bind, lvar_store_bind.
  set (u := logic_var_open 0 y v).
  fold u.
  destruct u as [k|z] eqn:Hu.
  - destruct k as [|k].
    + rewrite !lookup_insert_eq. reflexivity.
    + cbn [insert].
      rewrite !lookup_insert_ne by discriminate.
      assert (Hv_eq : v = LVBound (S k)).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVBound (S k))) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from.
      replace (LVBound (S k)) with (logic_var_shift_from 0 (LVBound k))
        by reflexivity.
      rewrite !storeA_rekey_lookup by apply logic_var_shift_from_inj.
      unfold relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide (LVBound k ∈ relevant_lvars τsum e_src))
        as [Hrel|Hrel]; [reflexivity|].
      exfalso. apply Hrel.
      subst X.
      unfold relevant_lvars in *.
      cbn [tm_lvars tm_lvars_at value_lvars_at] in *.
      rewrite cty_open_vars in HvX.
      unfold context_ty_open_lvars in HvX.
      rewrite cty_shift_vars in HvX.
      unfold context_ty_shift_lvars in HvX.
      apply elem_of_union_l.
      apply Hτsub.
      apply elem_of_union in HvX as [Hopen|Hret].
      2:{ set_solver. }
      rewrite set_swap_elem in Hopen.
      rewrite (swap_fresh (LVBound 0) (LVFree y) (LVBound (S k))) in Hopen
        by congruence.
      unfold lvars_shift_from in Hopen.
      apply elem_of_map in Hopen as [w [Hwshift Hw]].
      destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift;
        repeat destruct decide; inversion Hwshift; subst; try lia.
      exact Hw.
  - destruct (decide (z = y)) as [->|Hzy].
    + exfalso.
      unfold u in Hu.
      assert (Hv_eq : v = LVBound 0).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVFree y)) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      subst X.
      unfold relevant_lvars in *.
      cbn [tm_lvars tm_lvars_at value_lvars_at] in *.
      rewrite cty_open_vars in HvX.
      unfold context_ty_open_lvars in HvX.
      rewrite cty_shift_vars in HvX.
      unfold context_ty_shift_lvars in HvX.
      apply elem_of_union in HvX as [Hopen|Hret].
      { rewrite set_swap_elem in Hopen.
        rewrite swap_l in Hopen.
        apply Hyτ.
        change (y ∈ lvars_fv (context_ty_lvars τbranch)).
        rewrite <- (lvars_shift_from_fv 0 (context_ty_lvars τbranch)).
        apply lvars_fv_elem. exact Hopen. }
      { set_solver. }
    + rewrite !lookup_insert_ne by congruence.
      assert (Hv_eq : v = LVFree z).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVFree z)) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from.
      replace (LVFree z) with (logic_var_shift_from 0 (LVFree z))
        by reflexivity.
      rewrite !storeA_rekey_lookup by apply logic_var_shift_from_inj.
      unfold relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide (LVFree z ∈ relevant_lvars τsum e_src))
        as [Hrel|Hrel]; [reflexivity|].
      exfalso. apply Hrel.
      subst X.
      unfold relevant_lvars in *.
      cbn [tm_lvars tm_lvars_at value_lvars_at] in *.
      rewrite cty_open_vars in HvX.
      unfold context_ty_open_lvars in HvX.
      rewrite cty_shift_vars in HvX.
      unfold context_ty_shift_lvars in HvX.
      apply elem_of_union in HvX as [Hopen|Hret].
      { rewrite set_swap_elem in Hopen.
        rewrite (swap_fresh (LVBound 0) (LVFree y) (LVFree z)) in Hopen
          by congruence.
        unfold lvars_shift_from in Hopen.
        apply elem_of_map in Hopen as [w [Hwshift Hw]].
        destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift;
          repeat destruct decide; inversion Hwshift; subst; try lia.
        apply elem_of_union_l. apply Hτsub. exact Hw. }
      { set_solver. }
Qed.

Lemma arrow_arg_relevant_env_agree_open_one_core
    (Σsrc : lty_env) Ty y τx τr e_src :
  y ∉ fv_cty τx ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σsrc (CTArrow τx τr) e_src) Ty))
    (relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σsrc Ty))
    (relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))).
Proof.
  intros Hyτx.
  change (relevant_env Σsrc (CTArrow τx τr) e_src)
    with (relevant_env Σsrc (CTWand τx τr) e_src).
  apply wand_arg_relevant_env_agree_open_one_core. exact Hyτx.
Qed.

End RelevantEnv.

Notation "'rlv[' τ ']'" :=
  (relevant_lvars τ)
  (at level 20, τ at level 200,
   format "rlv[ τ ]").

Notation "'rlv[' τ ']' e" :=
  (relevant_lvars τ e)
  (at level 20, τ at level 200, e at level 20,
   format "rlv[ τ ]  e").

Notation "'rel[' Σ '|' τ ']'" :=
  (relevant_env Σ τ)
  (at level 20, Σ at level 200, τ at level 200,
   format "rel[ Σ  |  τ ]").

Notation "'rel[' Σ '|' τ ']' e" :=
  (relevant_env Σ τ e)
  (at level 20, Σ at level 200, τ at level 200, e at level 20,
   format "rel[ Σ  |  τ ]  e").

Ltac relevant_lvars_norm :=
  unfold relevant_lvars;
  type_open_env_syntax_norm;
  cbn [context_ty_lvars context_ty_lvars_at tm_lvars tm_lvars_at
    value_lvars_at lvar_value_keys fv_tm fv_value];
  rewrite ?fv_tapp_tm, ?tm_shift_fv, ?cty_shift_fv;
  rewrite ?relevant_lvars_fv, ?lvars_fv_union,
    ?context_ty_lvars_fv, ?tm_lvars_fv;
  rewrite ?lvars_at_depth_union, ?lvars_at_depth_empty;
  rewrite ?lvars_fv_empty, ?lvars_fv_singleton_bound,
    ?lvars_fv_singleton_free, ?lvars_fv_of_atoms;
  rewrite ?typed_lty_env_bind_lvars_fv_dom,
    ?lvar_store_bind_lvars_fv_dom;
  rewrite ?dom_insert_L, ?dom_empty_L, ?dom_union_L;
  rewrite ?context_ty_lvars_depth, ?tm_lvars_depth;
  try rewrite ?context_ty_lvars_at_shift_under by lia;
  try rewrite ?tm_lvars_at_shift_under by lia;
  rewrite ?tm_lvars_at_tret_bound0_under.

Ltac relevant_lvars_norm_in H :=
  unfold relevant_lvars in H;
  type_open_env_syntax_norm_in H;
  cbn [context_ty_lvars context_ty_lvars_at tm_lvars tm_lvars_at
    value_lvars_at lvar_value_keys fv_tm fv_value] in H;
  rewrite ?fv_tapp_tm in H;
  rewrite ?tm_shift_fv in H;
  rewrite ?cty_shift_fv in H;
  rewrite ?relevant_lvars_fv in H;
  rewrite ?lvars_fv_union in H;
  rewrite ?context_ty_lvars_fv in H;
  rewrite ?tm_lvars_fv in H;
  rewrite ?lvars_at_depth_union in H;
  rewrite ?lvars_at_depth_empty in H;
  rewrite ?lvars_fv_empty in H;
  rewrite ?lvars_fv_singleton_bound in H;
  rewrite ?lvars_fv_singleton_free in H;
  rewrite ?lvars_fv_of_atoms in H;
  rewrite ?typed_lty_env_bind_lvars_fv_dom in H;
  rewrite ?lvar_store_bind_lvars_fv_dom in H;
  rewrite ?dom_insert_L in H;
  rewrite ?dom_empty_L in H;
  rewrite ?dom_union_L in H;
  rewrite ?context_ty_lvars_depth in H;
  rewrite ?tm_lvars_depth in H;
  try rewrite ?context_ty_lvars_at_shift_under in H by lia;
  try rewrite ?tm_lvars_at_shift_under in H by lia;
  rewrite ?tm_lvars_at_tret_bound0_under in H.

Ltac lty_env_open_bind_norm :=
  rewrite ?atom_env_to_lty_env_erase_ctx_comma_bind_open_one
    by (eauto; better_set_solver);
  rewrite ?atom_env_to_lty_env_erase_ctx_star_bind_open_one
    by (eauto; better_set_solver);
  rewrite ?typed_lty_env_bind_open_current
    by (eauto using atom_env_to_lty_env_dom_free_notin,
        atom_store_to_lvar_store_closed; try better_set_solver);
  rewrite ?atom_store_to_lvar_store_insert;
  rewrite ?typed_lty_env_bind_lvars_fv_dom, ?lty_env_open_one_dom.

Ltac lty_env_open_bind_norm_in H :=
  rewrite ?atom_env_to_lty_env_erase_ctx_comma_bind_open_one in H
    by (eauto; better_set_solver);
  rewrite ?atom_env_to_lty_env_erase_ctx_star_bind_open_one in H
    by (eauto; better_set_solver);
  rewrite ?typed_lty_env_bind_open_current in H
    by (eauto using atom_env_to_lty_env_dom_free_notin,
        atom_store_to_lvar_store_closed; try better_set_solver);
  rewrite ?atom_store_to_lvar_store_insert in H;
  rewrite ?typed_lty_env_bind_lvars_fv_dom in H;
  rewrite ?lty_env_open_one_dom in H.

Ltac relevant_env_norm :=
  unfold relevant_env, lty_env_restrict_lvars;
  relevant_lvars_norm;
  lty_env_open_bind_norm;
  store_normalize;
  rewrite ?storeA_restrict_dom.

Ltac relevant_env_norm_in H :=
  unfold relevant_env, lty_env_restrict_lvars in H;
  relevant_lvars_norm_in H;
  lty_env_open_bind_norm_in H;
  store_normalize;
  rewrite ?storeA_restrict_dom in H.

Ltac relevant_env_set :=
  relevant_env_norm; better_set_solver.

Ltac closed_side_solve :=
  eauto using lc_lvars_relevant_lvars,
    wf_context_ty_at_lc, basic_context_ty_lc,
    lty_env_closed_insert_free, atom_store_to_lvar_store_closed.
