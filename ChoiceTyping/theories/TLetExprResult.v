(** * ChoiceTyping.TLetExprResult

    Expression-result and fiber bridges for the [tlet] proof. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps.
From ChoiceTyping Require Export TLetTotal.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma denot_tlet_semantic_at_world
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    (m : WfWorld) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
Admitted.

(** The fold order chosen by [stdpp.set_fold] is intentionally abstract.  For
    the tlet proof we need to expose the semantic order [X] first and the bound
    result coordinate [x] second.  This is pure fiber bookkeeping: it follows
    from commutation of independent [FFib] modalities and [res_fiber_commute]. *)
Lemma fib_vars_obligation_step_commute x y R ρ (m : WfWorld) :
  x ≠ y →
  x ∈ world_dom (m : World) →
  y ∈ world_dom (m : World) →
  fib_vars_obligation_step y (fib_vars_obligation_step x R) ρ m →
  fib_vars_obligation_step x (fib_vars_obligation_step y R) ρ m.
Proof.
  intros Hxy Hxm Hym [Hρy Hy].
  unfold fib_vars_obligation_step in *.
  split.
  - destruct (world_wf m) as [[σ Hσ] _].
    set (σy := store_restrict σ {[y]}).
    assert (Hprojy : res_restrict m {[y]} σy).
    { exists σ. split; [exact Hσ | reflexivity]. }
    destruct (Hy σy Hprojy) as [Hρσy_x _].
    subst σy.
    rewrite dom_union_L in Hρσy_x.
    rewrite store_restrict_dom in Hρσy_x.
    set_solver.
  - intros σx Hprojx.
    split.
    + rewrite dom_union_L.
      destruct Hprojx as [σ [Hσ Hσx]].
      assert (Hdomσx : dom σx ⊆ {[x]}).
      { rewrite <- Hσx, store_restrict_dom. set_solver. }
      set_solver.
    + intros σy Hprojy_after_x.
      pose proof (res_projection_from_fiber_projection
        m {[x]} {[y]} σx σy Hprojx Hprojy_after_x) as Hprojy.
      assert (Hprojx_after_y :
        res_restrict
          (res_fiber_from_projection m {[y]} σy Hprojy) {[x]} σx).
      {
        assert (Hdomσx : dom σx = {[x]}).
        {
          destruct Hprojx as [σ0 [Hσ0 Hσ0x]].
          rewrite <- Hσ0x, store_restrict_dom.
          pose proof (wfworld_store_dom m σ0 Hσ0) as Hdomσ0.
          set_solver.
        }
        destruct Hprojy_after_x as [σ [Hσfiber_x Hσy]].
        destruct Hσfiber_x as [Hσm Hσx].
        exists σ. split.
        - apply res_fiber_from_projection_member; [exact Hσm | exact Hσy].
        - rewrite <- Hdomσx. exact Hσx.
      }
      destruct (Hy σy Hprojy) as [_ Hyx].
      specialize (Hyx σx Hprojx_after_y).
      assert (Hfib_eq :
        res_fiber_from_projection
          (res_fiber_from_projection m {[y]} σy Hprojy) {[x]} σx Hprojx_after_y =
        res_fiber_from_projection
          (res_fiber_from_projection m {[x]} σx Hprojx) {[y]} σy Hprojy_after_x).
      {
        apply wfworld_ext. apply world_ext.
        - reflexivity.
        - intros τ. simpl. tauto.
      }
      replace (ρ ∪ σx ∪ σy) with (ρ ∪ σy ∪ σx).
      2:{
        assert (Hdomσx : dom σx = {[x]}).
        {
          destruct Hprojx as [σ0 [Hσ0 Hσ0x]].
          rewrite <- Hσ0x, store_restrict_dom.
          pose proof (wfworld_store_dom m σ0 Hσ0) as Hdomσ0.
          set_solver.
        }
        assert (Hdomσy : dom σy = {[y]}).
        {
          destruct Hprojy as [σ0 [Hσ0 Hσ0y]].
          rewrite <- Hσ0y, store_restrict_dom.
          pose proof (wfworld_store_dom m σ0 Hσ0) as Hdomσ0.
          set_solver.
        }
        assert (Hdisj_xy : σx ##ₘ σy).
        {
          apply map_disjoint_dom.
          rewrite Hdomσx, Hdomσy. set_solver.
        }
        rewrite <- (assoc_L (∪) ρ σx σy).
        rewrite <- (assoc_L (∪) ρ σy σx).
        f_equal. symmetry. apply map_union_comm. exact Hdisj_xy.
      }
      rewrite <- Hfib_eq. exact Hyx.
Qed.

Lemma fib_vars_obligation_insert_fresh_to_fib
    X x p ρ m :
  x ∉ X →
  fib_vars_obligation (X ∪ {[x]}) p ρ m →
  fib_vars_obligation X (FFib x p) ρ m.
Proof.
Admitted.

Lemma expr_result_store_from_body_xfiber
    X e2 x ν ρ (mlet : WfWorld) σ vx v :
  x ∉ X →
  store_restrict σ X = ρ →
  (mlet : World) (<[x := vx]> σ) →
  res_models_with_store ρ mlet (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  expr_result_store ν
    (subst_map (<[x := vx]> (store_restrict σ X)) (e2 ^^ x))
    {[ν := v]} →
  expr_result_store ν
    (subst_map (<[x := vx]> ρ) (e2 ^^ x))
    {[ν := v]}.
Proof.
  intros _ Hρ _ _ Hstore. rewrite <- Hρ. exact Hstore.
Qed.

Lemma expr_result_in_world_tlete_xfiber_sound
    X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx)
    (ρ : Store) (m mlet : WfWorld) σν :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  (∀ σ, (m : World) σ → (n : World) σ ∧ store_restrict σ X = ρ) →
  (∀ σx, (mlet : World) σx →
    ∃ σ vx,
      (m : World) σ ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      σx = <[x := vx]> σ) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    (mlet : World) (<[x := vx]> σ)) →
  res_models_with_store ρ mlet (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  (res_restrict m {[ν]} : World) σν →
  expr_result_in_store ρ (tlete e1 e2) ν σν.
Proof.
  intros Hx Hclosed Hlc Hresult_closed Hbody Hm Hmlet_elim Hmlet_intro Hbody_model Hν.
  destruct Hν as [σ [Hσm Hσν]].
  destruct (Hm σ Hσm) as [Hσn HσX].
  destruct (Hresult σ Hσn) as [vx He1].
  pose proof (Hmlet_intro σ vx Hσm He1) as Hσx_mlet.
  assert (Hprojx : res_restrict mlet {[x]} {[x := vx]}).
  {
    exists (<[x := vx]> σ). split; [exact Hσx_mlet |].
    apply store_restrict_insert_singleton.
  }
  unfold res_models_with_store in Hbody_model. simpl in Hbody_model.
  destruct Hbody_model as [_ [Hdisj Hfib]].
  specialize (Hfib {[x := vx]} Hprojx).
  assert (Hatom :
    res_models_with_store (ρ ∪ {[x := vx]})
      (res_fiber_from_projection mlet {[x]} {[x := vx]} Hprojx)
      (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))).
  { unfold res_models_with_store. exact Hfib. }
  pose proof (FAtom_expr_logic_qual_on_exact
    (X ∪ {[x]}) (e2 ^^ x) ν (ρ ∪ {[x := vx]})
    (res_fiber_from_projection mlet {[x]} {[x := vx]} Hprojx)
    Hatom) as Hbody_exact.
  assert (Hσν_body :
    (res_restrict
      (res_fiber_from_projection mlet {[x]} {[x := vx]} Hprojx) {[ν]} : World) σν).
  {
    exists (<[x := vx]> σ). split.
    - apply res_fiber_from_projection_member.
      + exact Hσx_mlet.
      + apply store_restrict_insert_singleton.
    - rewrite store_restrict_insert_notin by set_solver.
      exact Hσν.
  }
  pose proof (expr_result_in_world_sound
    (store_restrict (ρ ∪ {[x := vx]}) (X ∪ {[x]}))
    (e2 ^^ x) ν
    (res_fiber_from_projection mlet {[x]} {[x := vx]} Hprojx)
    σν Hbody_exact Hσν_body) as Hbody_store.
  assert (Hρx :
    store_restrict (ρ ∪ {[x := vx]}) (X ∪ {[x]}) =
    <[x := vx]> ρ).
  {
    apply store_restrict_union_singleton_insert.
    - rewrite <- HσX. rewrite store_restrict_dom. set_solver.
    - set_solver.
  }
  rewrite Hρx in Hbody_store.
  destruct (expr_result_store_elim ν
    (subst_map (<[x := vx]> ρ) (e2 ^^ x)) σν Hbody_store)
    as [v [Hσν_eq [Hv_stale [Hv_lc Hbody_steps]]]].
  subst σν.
  rewrite Hσν_eq.
  apply expr_result_store_intro; [exact Hv_stale | exact Hv_lc |].
  assert (HxX : x ∉ X) by set_solver.
  assert (Hxe2 : x ∉ fv_tm e2) by set_solver.
  rewrite <- HσX.
  eapply expr_result_value_tlete_from_body_projection.
  - exact HxX.
  - exact Hxe2.
  - apply Hclosed. exact Hσn.
  - apply Hlc. exact Hσn.
  - apply (proj1 (Hresult_closed σ vx Hσn He1)).
  - apply (proj2 (Hresult_closed σ vx Hσn He1)).
  - apply Hbody. exact Hσn.
  - exact He1.
  - rewrite HσX. exact Hbody_steps.
Qed.

Lemma expr_result_in_world_tlete_xfiber_complete
    X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx)
    (ρ : Store) (m mlet : WfWorld) σν :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  (∀ σ, (m : World) σ → (n : World) σ ∧ store_restrict σ X = ρ) →
  (∀ σx, (mlet : World) σx →
    ∃ σ vx,
      (m : World) σ ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      σx = <[x := vx]> σ) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    (mlet : World) (<[x := vx]> σ)) →
  res_models_with_store ρ mlet (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  expr_result_in_store ρ (tlete e1 e2) ν σν →
  (res_restrict m {[ν]} : World) σν.
Proof.
  intros Hx Hclosed Hlc Hresult_closed Hbody Hm Hmlet_elim Hmlet_intro Hbody_model Hstore.
  destruct (expr_result_store_elim ν (subst_map ρ (tlete e1 e2)) σν Hstore)
    as [v [Hσν_eq [Hv_stale [Hv_lc Hsteps]]]].
  subst σν.
  destruct (world_wf m) as [[σ Hσm] _].
  destruct (Hm σ Hσm) as [Hσn HσX].
  rewrite <- HσX in Hsteps.
  change (subst_map (store_restrict σ X) (tlete e1 e2)) with
    (m{store_restrict σ X} (tlete e1 e2)) in Hsteps.
  rewrite msubst_lete in Hsteps.
  destruct (reduction_lete (m{store_restrict σ X} e1)
    (m{store_restrict σ X} e2) v Hsteps) as [vx [He1 Hbody_steps_open]].
  pose proof (Hmlet_intro σ vx Hσm He1) as Hσx_mlet.
  assert (Hprojx : res_restrict mlet {[x]} {[x := vx]}).
  {
    exists (<[x := vx]> σ). split; [exact Hσx_mlet |].
    apply store_restrict_insert_singleton.
  }
  unfold res_models_with_store in Hbody_model. simpl in Hbody_model.
  destruct Hbody_model as [_ [Hdisj Hfib]].
  specialize (Hfib {[x := vx]} Hprojx).
  assert (Hatom :
    res_models_with_store (ρ ∪ {[x := vx]})
      (res_fiber_from_projection mlet {[x]} {[x := vx]} Hprojx)
      (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))).
  { unfold res_models_with_store. exact Hfib. }
  pose proof (FAtom_expr_logic_qual_on_exact
    (X ∪ {[x]}) (e2 ^^ x) ν (ρ ∪ {[x := vx]})
    (res_fiber_from_projection mlet {[x]} {[x := vx]} Hprojx)
    Hatom) as Hbody_exact.
  assert (HxX : x ∉ X) by set_solver.
  assert (Hxe2 : x ∉ fv_tm e2) by set_solver.
  assert (Hρx :
    store_restrict (ρ ∪ {[x := vx]}) (X ∪ {[x]}) =
    <[x := vx]> ρ).
  {
    apply store_restrict_union_singleton_insert.
    - rewrite <- HσX. rewrite store_restrict_dom. set_solver.
    - exact HxX.
  }
  assert (Hbody_steps :
    subst_map (<[x := vx]> ρ) (e2 ^^ x) →* tret v).
  {
    pose proof Hbody_steps_open as Htmp.
    rewrite <- (msubst_intro_open_tm e2 0 vx x (store_restrict σ X)) in Htmp.
    - rewrite HσX in Htmp. exact Htmp.
    - apply Hclosed. exact Hσn.
    - apply (proj1 (Hresult_closed σ vx Hσn He1)).
    - apply (proj2 (Hresult_closed σ vx Hσn He1)).
    - apply Hlc. exact Hσn.
    - change (x ∉ dom (store_restrict σ X) ∪ fv_tm e2).
      rewrite store_restrict_dom. set_solver.
  }
  assert (Hbody_store :
    expr_result_in_store
      (store_restrict (ρ ∪ {[x := vx]}) (X ∪ {[x]}))
      (e2 ^^ x) ν {[ν := v]}).
  {
    rewrite Hρx.
    apply expr_result_store_intro; [exact Hv_stale | exact Hv_lc | exact Hbody_steps].
  }
  pose proof (expr_result_in_world_complete
    (store_restrict (ρ ∪ {[x := vx]}) (X ∪ {[x]}))
    (e2 ^^ x) ν
    (res_fiber_from_projection mlet {[x]} {[x := vx]} Hprojx)
    {[ν := v]} Hbody_exact Hbody_store) as Hν_body.
  destruct Hν_body as [σx [[Hσx_mlet' Hσx_proj] Hσxν]].
  destruct (Hmlet_elim σx Hσx_mlet') as [σ' [vx' [Hσ'm [He1' Hσx_eq]]]].
  subst σx.
  exists σ'. split; [exact Hσ'm |].
  rewrite <- Hσxν.
  rewrite store_restrict_insert_notin by set_solver.
  reflexivity.
Qed.

(** One-projection semantic core of tlet.

    After the outer [X]-fibers have fixed the input store [ρ], the body-side
    obligation still contains one more fiber for [x].  That [x]-fiber ranges
    over exactly the stores produced by [let_result_world_on]: each admissible
    input store is paired with an actual result [vx] of [e1].  Exactness of the
    inner result projection for [e2 ^^ x], together with the operational let
    bridge [expr_result_value_tlete_from_body_store], yields exactness of the
    [ν]-projection for [tlete e1 e2].

    The remaining proof work here is algebraic alignment of the fibered
    [let_result_world_on] with the fibered base world. *)
Lemma expr_result_in_world_tlete_from_body_xfiber
    X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx)
    (ρ : Store) (m mlet : WfWorld) :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  (* [m] is the current [X]-fiber of [n], and [ρ] is its fixed projection. *)
  (∀ σ, (m : World) σ → (n : World) σ ∧ store_restrict σ X = ρ) →
  (* [mlet] is the matching [X]-fiber of [let_result_world_on X e1 x n]. *)
  (∀ σx, (mlet : World) σx →
    ∃ σ vx,
      (m : World) σ ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      σx = <[x := vx]> σ) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    (mlet : World) (<[x := vx]> σ)) →
  res_models_with_store ρ mlet (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  expr_result_in_world ρ (tlete e1 e2) ν m.
Proof.
  intros Hx _ Hclosed Hlc Hresult_closed Hbody Hm Hmlet_elim Hmlet_intro Hbody_model.
  intros σν. split.
  - eapply expr_result_in_world_tlete_xfiber_sound; eauto.
  - eapply expr_result_in_world_tlete_xfiber_complete; eauto.
Qed.

Lemma expr_result_in_world_tlete_from_body_projection_fiber
    X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx)
    ρ Hprojn Hprojlet :
  X ⊆ world_dom (n : World) →
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  res_models_with_store ρ
    (res_fiber_from_projection
      (let_result_world_on X e1 x n Hfresh Hresult) X ρ Hprojlet)
    (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  expr_result_in_world ρ (tlete e1 e2) ν
    (res_fiber_from_projection n X ρ Hprojn).
Proof.
  intros HXdom Hx Hfv Hclosed Hlc Hresult_closed Hbody Hbody_model.
  eapply expr_result_in_world_tlete_from_body_xfiber; eauto.
  - intros σ Hσ.
    destruct Hσ as [Hσn Hσρ]. split; [exact Hσn |].
    assert (Hdomρ : dom ρ = X).
    {
      destruct Hprojn as [σ0 [Hσ0 Hσ0ρ]].
      assert (Hρeq : ρ = store_restrict σ0 X) by (symmetry; exact Hσ0ρ).
      pose proof (wfworld_store_dom n σ0 Hσ0) as Hdomσ0.
      rewrite Hρeq, store_restrict_dom. set_solver.
    }
    rewrite <- Hdomρ. exact Hσρ.
  - intros σx Hσx.
    eapply let_result_world_on_fiber_elim; eauto; set_solver.
  - intros σ vx Hσ Hsteps.
    eapply let_result_world_on_fiber_intro; eauto; set_solver.
Qed.

Lemma fib_vars_obligation_tlete_from_body_foldr_base
    X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx)
    ρ (m mlet : WfWorld) :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  world_dom (m : World) = world_dom (n : World) →
  world_dom (mlet : World) = world_dom (n : World) ∪ {[x]} →
  (∀ σ, (m : World) σ → (n : World) σ ∧ store_restrict σ X = ρ) →
  (∀ σx, (mlet : World) σx →
    ∃ σ vx,
      (m : World) σ ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      σx = <[x := vx]> σ) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    (mlet : World) (<[x := vx]> σ)) →
  res_models_with_store ρ mlet
    (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  res_models_with_store ρ m
    (FAtom (expr_logic_qual_on X (tlete e1 e2) ν)).
Proof.
  intros Hx Hfv Hclosed Hlc Hres_closed Hbody Hdomm Hdommlet
    Hm Hmlet_elim Hmlet_intro Hbody_model.
  assert (Hexact : expr_result_in_world ρ (tlete e1 e2) ν m).
  {
    eapply (expr_result_in_world_tlete_from_body_xfiber
      X e1 e2 x ν n Hfresh Hresult ρ m mlet).
    - exact Hx.
    - exact Hfv.
    - exact Hclosed.
    - exact Hlc.
    - exact Hres_closed.
    - exact Hbody.
    - exact Hm.
    - exact Hmlet_elim.
    - exact Hmlet_intro.
    - exact Hbody_model.
  }
  assert (Hscope_body :
    formula_scoped_in_world ρ mlet
      (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)))).
  { apply (res_models_with_store_fuel_scoped _ _ _ _ Hbody_model). }
  assert (Hscope :
    formula_scoped_in_world ρ m
      (FAtom (expr_logic_qual_on X (tlete e1 e2) ν))).
  {
    assert (HdomρX : dom ρ ⊆ X).
    {
      destruct (world_wf m) as [[σ Hσm] _].
      destruct (Hm σ Hσm) as [_ Hσρ].
      rewrite <- Hσρ, store_restrict_dom. set_solver.
    }
    unfold formula_scoped_in_world in *.
    simpl in *. unfold stale, stale_logic_qualifier in *. simpl in *.
    intros z Hz.
    rewrite Hdomm.
    assert (Hz_body :
      z ∈ dom ρ ∪ ({[x]} ∪ (X ∪ {[x]} ∪ {[ν]}))).
    { set_solver. }
    pose proof (Hscope_body z Hz_body) as Hz_mlet.
    rewrite Hdommlet in Hz_mlet.
    assert (z ≠ x) by set_solver.
    set_solver.
  }
  eapply FAtom_expr_logic_qual_on_intro.
  - exact Hscope.
  - replace (store_restrict ρ X) with ρ.
    + exact Hexact.
    + symmetry. apply store_restrict_idemp.
      destruct (world_wf m) as [[σ Hσm] _].
      destruct (Hm σ Hσm) as [_ Hσρ].
      rewrite <- Hσρ, store_restrict_dom. set_solver.
Qed.

Lemma fib_vars_obligation_tlete_from_body_foldr
    xs X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx) :
  NoDup xs →
  (list_to_set xs : aset) ⊆ X →
  X ⊆ world_dom (n : World) →
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  ∀ ρ (m mlet : WfWorld),
    world_dom (m : World) = world_dom (n : World) →
    world_dom (mlet : World) = world_dom (n : World) ∪ {[x]} →
    (∀ σ, (m : World) σ →
      (n : World) σ ∧
      store_restrict σ (X ∖ (list_to_set xs : aset)) = ρ) →
    (∀ σx, (mlet : World) σx →
      ∃ σ vx,
        (m : World) σ ∧
        subst_map (store_restrict σ X) e1 →* tret vx ∧
        σx = <[x := vx]> σ) →
    (∀ σ vx,
      (m : World) σ →
      subst_map (store_restrict σ X) e1 →* tret vx →
      (mlet : World) (<[x := vx]> σ)) →
    snd (foldr fib_vars_acc_step
      (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)),
       fun ρ m => res_models_with_store ρ m
         (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)))) xs)
      ρ mlet →
    snd (foldr fib_vars_acc_step
      (FAtom (expr_logic_qual_on X (tlete e1 e2) ν),
       fun ρ m => res_models_with_store ρ m
         (FAtom (expr_logic_qual_on X (tlete e1 e2) ν))) xs)
      ρ m.
Proof.
  induction xs as [|y xs IH]; simpl; intros Hnodup Hsub HXdom Hx Hfv Hclosed Hlc Hres_closed Hbody
    ρ m mlet Hdomm Hdommlet Hm Hmlet_elim Hmlet_intro Hbody_obl.
  - eapply (fib_vars_obligation_tlete_from_body_foldr_base
      X e1 e2 x ν n Hfresh Hresult ρ m mlet).
    + exact Hx.
    + exact Hfv.
    + exact Hclosed.
    + exact Hlc.
    + exact Hres_closed.
    + exact Hbody.
    + exact Hdomm.
    + exact Hdommlet.
    + intros σ Hσ. destruct (Hm σ Hσ) as [Hσn Hσρ].
      split; [exact Hσn |]. rewrite difference_empty_L in Hσρ. exact Hσρ.
    + exact Hmlet_elim.
    + exact Hmlet_intro.
    + exact Hbody_obl.
  - inversion Hnodup as [|? ? Hy_notin Hnodup']; subst.
    destruct (foldr fib_vars_acc_step
      (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)),
       fun ρ m => res_models_with_store ρ m
         (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)))) xs)
      as [p_body R_body] eqn:Hbody_tail.
    destruct (foldr fib_vars_acc_step
      (FAtom (expr_logic_qual_on X (tlete e1 e2) ν),
       fun ρ m => res_models_with_store ρ m
         (FAtom (expr_logic_qual_on X (tlete e1 e2) ν))) xs)
      as [p_let R_let] eqn:Hlet_tail.
    simpl in Hbody_obl |- *.
    unfold fib_vars_obligation_step in Hbody_obl.
    destruct Hbody_obl as [Hdisj Hfib]. split; [exact Hdisj |].
    intros σy Hprojy_m.
    assert (HyX : y ∈ X).
    { apply Hsub. set_solver. }
    assert (Hyx : y ≠ x) by set_solver.
    assert (Hdomσy : dom σy = {[y]}).
    {
      destruct Hprojy_m as [σ0 [Hσ0 Hσ0y]].
      assert (Hσyeq : σy = store_restrict σ0 {[y]}) by (symmetry; exact Hσ0y).
      pose proof (wfworld_store_dom m σ0 Hσ0) as Hdomσ0.
      rewrite Hσyeq, store_restrict_dom.
      set_solver.
    }
    assert (Hprojy_mlet : res_restrict mlet {[y]} σy).
    {
      destruct Hprojy_m as [σ0 [Hσ0 Hσ0y]].
      destruct (Hm σ0 Hσ0) as [Hσ0n _].
      destruct (Hresult σ0 Hσ0n) as [vx Hsteps].
      exists (<[x := vx]> σ0). split.
      - apply Hmlet_intro; [exact Hσ0 | exact Hsteps].
      - rewrite store_restrict_insert_notin by set_solver.
        exact Hσ0y.
    }
    specialize (Hfib σy Hprojy_mlet).
    eapply (IH Hnodup'
      ltac:(intros z Hz; apply Hsub; set_solver)
      HXdom Hx Hfv Hclosed Hlc Hres_closed Hbody
      (ρ ∪ σy)
      (res_fiber_from_projection m {[y]} σy Hprojy_m)
      (res_fiber_from_projection mlet {[y]} σy Hprojy_mlet)).
    + simpl. rewrite Hdomm. reflexivity.
    + simpl. rewrite Hdommlet. reflexivity.
    + intros σ Hσ.
      destruct Hσ as [Hσm Hσy].
      destruct (Hm σ Hσm) as [Hσn Hσρ].
      split; [exact Hσn |].
      replace (X ∖ (list_to_set xs : aset)) with
        ((X ∖ ({[y]} ∪ (list_to_set xs : aset))) ∪ {[y]}).
      rewrite (store_restrict_union_from_parts σ ρ σy
        (X ∖ ({[y]} ∪ (list_to_set xs : aset))) y).
      * reflexivity.
      * timeout 3 set_solver.
      * exact Hσρ.
      * rewrite <- Hdomσy. exact Hσy.
      * symmetry. apply difference_cons_decompose.
        -- exact HyX.
        -- rewrite elem_of_list_to_set. exact Hy_notin.
    + intros σx Hσx.
      destruct (fiber_projection_member_elim _ _ _ _ _ Hσx)
        as [Hσx_mlet Hσx_y].
      destruct (Hmlet_elim σx Hσx_mlet) as [σ [vx [Hσm [Hsteps ->]]]].
      exists σ, vx. split.
      * apply res_fiber_from_projection_member; [exact Hσm |].
        rewrite <- Hσx_y.
        rewrite Hdomσy.
        rewrite store_restrict_insert_notin by (timeout 3 set_solver).
        reflexivity.
      * split; [exact Hsteps | reflexivity].
    + intros σ vx Hσ Hsteps.
      destruct (fiber_projection_member_elim _ _ _ _ _ Hσ)
        as [Hσm Hσy].
      apply res_fiber_from_projection_member.
      * apply Hmlet_intro; [exact Hσm | exact Hsteps].
      * transitivity (store_restrict (<[x := vx]> σ) (dom σy)).
        -- rewrite Hdomσy. reflexivity.
        -- rewrite store_restrict_insert_notin.
           ++ exact Hσy.
           ++ rewrite Hdomσy. timeout 3 set_solver.
    + exact Hfib.
Qed.

(** Lifting the one-projection semantic core through the outer [X] fibers.
    This is the induction over [fib_vars_obligation X].  Its non-mechanical
    leaf is [expr_result_in_world_tlete_from_body_xfiber]; the rest is threading
    the invariant that the current fiber of [n] consists exactly of stores with
    the accumulated projection [ρ]. *)
Lemma fib_vars_obligation_tlete_from_body_normalized
    X e1 e2 x ν (n : WfWorld) Hfresh Hresult :
  X ⊆ world_dom (n : World) →
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  fib_vars_obligation X
    (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) ∅
    (let_result_world_on X e1 x n Hfresh Hresult) →
  fib_vars_obligation X
    (FAtom (expr_logic_qual_on X (tlete e1 e2) ν)) ∅ n.
Proof.
  intros HXdom Hx Hfv Hclosed Hlc Hresult_closed Hbody Hbody_obl.
  unfold fib_vars_obligation, fib_vars_acc, set_fold in *.
  assert (Hxs : (list_to_set (elements X) : aset) ⊆ X).
  {
    intros z Hz.
    rewrite elem_of_list_to_set, elem_of_elements in Hz.
    exact Hz.
  }
  pose proof (fib_vars_obligation_tlete_from_body_foldr
    (elements X) X e1 e2 x ν n Hfresh Hresult) as Hfold.
  eapply (Hfold
    (NoDup_elements X)
    Hxs
    HXdom Hx Hfv Hclosed Hlc Hresult_closed Hbody
    (∅ : Store) n (let_result_world_on X e1 x n Hfresh Hresult)).
  - reflexivity.
  - unfold let_result_world_on, let_result_raw_world_on. simpl. reflexivity.
  - intros σ Hσ. split; [exact Hσ |].
    replace (X ∖ list_to_set (elements X) : aset) with (∅ : aset).
    + apply store_restrict_empty_set.
    + apply set_eq. intros z. rewrite elem_of_difference.
      rewrite elem_of_list_to_set, elem_of_elements. set_solver.
  - intros σx Hσx.
    destruct (let_result_world_on_elim X e1 x n Hfresh Hresult σx Hσx)
      as [σ [vx [Hσ [Hsteps ->]]]].
    exists σ, vx. repeat split; eauto.
  - intros σ vx Hσ Hsteps.
    apply let_result_world_on_member; [exact Hσ | exact Hsteps].
  - exact Hbody_obl.
Qed.

Lemma fib_vars_obligation_tlete_from_body_result_world
    X e1 e2 x ν (n : WfWorld) Hfresh Hresult :
  X ⊆ world_dom (n : World) →
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  fib_vars_obligation (X ∪ {[x]})
    (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)) ∅
    (let_result_world_on X e1 x n Hfresh Hresult) →
  fib_vars_obligation X
    (FAtom (expr_logic_qual_on X (tlete e1 e2) ν)) ∅ n.
Proof.
  intros HXdom Hx Hfv Hclosed Hlc Hresult_closed Hbody Hbody_obl.
  eapply fib_vars_obligation_tlete_from_body_normalized; eauto.
  eapply fib_vars_obligation_insert_fresh_to_fib; [set_solver | exact Hbody_obl].
Qed.

Lemma FExprResultOn_tlete_from_body_result_world
    X e1 e2 x ν (n : WfWorld) Hfresh Hresult :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  let_result_world_on X e1 x n Hfresh Hresult ⊨
    FExprResultOn (X ∪ {[x]}) (e2 ^^ x) ν →
  n ⊨ FExprResultOn X (tlete e1 e2) ν.
Proof.
  intros Hx Hfv Hclosed Hlc Hresult_closed Hbody Hbody_model.
  unfold FExprResultOn, FExprResultOnRaw, res_models in *.
  pose proof (res_models_with_store_fuel_scoped _ _ _ _
    Hbody_model) as Hscope_body.
  assert (HXdom : X ⊆ world_dom (n : World)).
  {
    intros z Hz.
    assert (Hz_body :
      z ∈ dom (∅ : Store) ∪ formula_fv
        (fib_vars (X ∪ {[x]})
          (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)))).
    {
      apply elem_of_union. right.
      rewrite fib_vars_formula_fv. simpl.
      unfold stale, stale_logic_qualifier. simpl.
      set_solver.
    }
    pose proof (Hscope_body z Hz_body) as Hz_dom.
    unfold let_result_world_on, let_result_raw_world_on in Hz_dom.
    simpl in Hz_dom.
    apply elem_of_union in Hz_dom as [Hz_dom | Hzx].
    - exact Hz_dom.
    - assert (z = x) by set_solver.
      subst z. set_solver.
  }
  apply fib_vars_models_intro.
  - apply FExprResultOn_scoped_intro.
    intros z Hz.
    assert (Hz' : z ∈ X ∪ {[ν]}) by set_solver.
    unfold formula_scoped_in_world in Hscope_body.
    assert (Hz_body :
      z ∈ dom (∅ : Store) ∪ formula_fv
        (FExprResultOn (X ∪ {[x]}) (e2 ^^ x) ν)).
    {
      apply elem_of_union. right.
      unfold FExprResultOn, FExprResultOnRaw.
      rewrite fib_vars_formula_fv. simpl.
      unfold stale, stale_logic_qualifier. simpl.
      set_solver.
    }
    pose proof (Hscope_body z Hz_body) as Hz_dom.
    unfold let_result_world_on, let_result_raw_world_on in Hz_dom.
    simpl in Hz_dom.
    apply elem_of_union in Hz_dom as [Hz_dom | Hzx].
    + exact Hz_dom.
    + assert (z = x) by set_solver.
      subst z. set_solver.
  - eapply fib_vars_obligation_tlete_from_body_result_world; eauto.
    unfold FExprResultOn, FExprResultOnRaw, res_models in Hbody_model.
    exact (fib_vars_models_elim _ _ _ _ Hbody_model).
Qed.

(** Body-to-let lifting for the total tlet proof.

    This statement is deliberately phrased for an arbitrary result type [τ].
    The proof should use two ingredients:

    - expression-result exactness/composition for [tlete e1 e2];
    - a generic denotation transport theorem for [denot_ty_on].

    It should not prove the tlet case separately for [CTOver], [CTUnder], or
    any other type constructor.  Such a split would make the typing rule depend
    on the shape of [τ], which is the abstraction leak this lemma is meant to
    avoid.

    Anti-slip rule: the only let-specific work here should be expression-result
    composition for [tlete].  Once that composition is established, the
    arbitrary result type [τ] must be handled by a reusable
    [denot_ty_on]-transport theorem, not by local recursion on [τ2]. *)
