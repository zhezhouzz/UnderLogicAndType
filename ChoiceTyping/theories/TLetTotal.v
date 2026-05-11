(** * ChoiceTyping.TLetTotal

    Totality and context-preservation helpers for [tlet] result worlds. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps.
From ChoiceTyping Require Export TLetGraph.
From ChoiceTyping Require Import Naming.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma expr_total_results_on_le
    X e (m n : WfWorld) :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  (∀ σ, (m : World) σ →
    ∃ v, subst_map (store_restrict σ X) e →* tret v) →
  ∀ σ, (n : World) σ →
    ∃ v, subst_map (store_restrict σ X) e →* tret v.
Proof.
  intros HXm Hle Hresult σn Hσn.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
  specialize (Hresult (store_restrict σn (world_dom (m : World)))).
  assert (Hσm :
    (m : World) (store_restrict σn (world_dom (m : World)))).
  {
    rewrite Hle. simpl.
    exists σn. split; [exact Hσn |].
    pose proof (raw_le_dom (m : World) (n : World)
      ltac:(unfold raw_le; exact Hle)) as Hdom_mn.
    replace (world_dom (n : World) ∩ world_dom (m : World))
      with (world_dom (m : World)) by set_solver.
    reflexivity.
  }
  destruct (Hresult Hσm) as [v Hsteps].
  exists v.
  store_norm.
  exact Hsteps.
Qed.

Lemma expr_total_results_on_restrict
    X e (m n : WfWorld) :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  (∀ σ, (n : World) σ →
    ∃ v, subst_map (store_restrict σ X) e →* tret v) →
  ∀ σ, (m : World) σ →
    ∃ v, subst_map (store_restrict σ X) e →* tret v.
Proof.
  intros HXm Hle Hresult σm Hσm.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
  rewrite Hle in Hσm. simpl in Hσm.
  destruct Hσm as [σn [Hσn Hrestrict]].
  destruct (Hresult σn Hσn) as [v Hsteps].
  exists v.
  rewrite <- Hrestrict.
  store_norm.
  exact Hsteps.
Qed.

Lemma let_result_world_on_base_mono
    X e x (m n : WfWorld)
    (Hfresh_m : x ∉ world_dom (m : World))
    (Hfresh_n : x ∉ world_dom (n : World))
    Hresult_m Hresult_n :
  fv_tm e ⊆ X →
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  let_result_world_on e x m Hfresh_m Hresult_m ⊑
    let_result_world_on e x n Hfresh_n Hresult_n.
Proof.
  intros Hfv HXm Hle.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le.
  apply world_ext.
  - simpl.
    pose proof (raw_le_dom (m : World) (n : World) Hle) as Hdom.
    set_solver.
  - intros σx. simpl. split.
    + intros Hσx.
      destruct Hσx as [σm [vx [Hσm [Hsteps ->]]]].
      unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
      rewrite Hle in Hσm.
      destruct Hσm as [σn [Hσn Hrestrict_m]].
      exists (<[x := vx]> σn). split.
      * exists σn, vx. repeat split; eauto.
        assert (HstoreX :
          store_restrict σn (fv_tm e) = store_restrict σm (fv_tm e)).
        {
          rewrite <- Hrestrict_m.
          store_norm.
          replace (world_dom (m : World) ∩ fv_tm e) with (fv_tm e)
            by set_solver.
          reflexivity.
        }
        rewrite HstoreX. exact Hsteps.
      * rewrite <- Hrestrict_m.
        apply (map_eq (M := gmap atom)). intros z.
        rewrite !store_restrict_lookup.
        destruct (decide (z ∈ world_dom (m : World) ∪ {[x]})) as [Hz|Hz].
        -- destruct (decide (z = x)) as [->|Hzx].
           ++ change ((<[x:=vx]> σn : Store) !! x =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! x).
              rewrite !lookup_insert.
              rewrite !decide_True by reflexivity.
              reflexivity.
           ++ change ((<[x:=vx]> σn : Store) !! z =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! z).
              rewrite !lookup_insert_ne by congruence.
              rewrite store_restrict_lookup.
              rewrite decide_True by set_solver.
              reflexivity.
        -- destruct (decide (z = x)) as [->|Hzx].
           ++ exfalso. apply Hz. set_solver.
           ++ change (None =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! z).
              rewrite lookup_insert_ne by congruence.
              rewrite store_restrict_lookup.
              rewrite decide_False by set_solver.
              reflexivity.
    + intros Hσx.
      destruct Hσx as [σxn [Hσxn Hrestrict]].
      destruct Hσxn as [σn [vx [Hσn [Hsteps ->]]]].
      unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
      assert (Hσm : (m : World) (store_restrict σn (world_dom (m : World)))).
      {
        pose proof (raw_le_dom (m : World) (n : World)
          ltac:(unfold sqsubseteq, wf_world_sqsubseteq, raw_le; exact Hle)) as Hdom_mn.
        rewrite Hle.
        exists σn. split; [exact Hσn |].
        simpl.
        replace (world_dom (n : World) ∩ world_dom (m : World))
          with (world_dom (m : World)) by set_solver.
        reflexivity.
      }
      exists (store_restrict σn (world_dom (m : World))), vx.
      split; [exact Hσm |].
      split.
      * assert (HstoreX :
          store_restrict (store_restrict σn (world_dom (m : World))) (fv_tm e) =
          store_restrict σn (fv_tm e)).
        {
          store_norm.
          replace (world_dom (m : World) ∩ fv_tm e) with (fv_tm e)
            by set_solver.
          reflexivity.
        }
        rewrite HstoreX. exact Hsteps.
      * rewrite <- Hrestrict.
        apply (map_eq (M := gmap atom)). intros z.
        rewrite !store_restrict_lookup.
        destruct (decide (z ∈ world_dom (m : World) ∪ {[x]})) as [Hz|Hz].
        -- destruct (decide (z = x)) as [->|Hzx].
           ++ change ((<[x:=vx]> σn : Store) !! x =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! x).
              rewrite !lookup_insert.
              rewrite !decide_True by reflexivity.
              reflexivity.
           ++ change ((<[x:=vx]> σn : Store) !! z =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! z).
              rewrite !lookup_insert_ne by congruence.
              rewrite store_restrict_lookup.
              rewrite decide_True by set_solver.
              reflexivity.
        -- destruct (decide (z = x)) as [->|Hzx].
           ++ exfalso. apply Hz. set_solver.
           ++ change (None =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! z).
              rewrite lookup_insert_ne by congruence.
              rewrite store_restrict_lookup.
              rewrite decide_False by set_solver.
              reflexivity.
Qed.

Lemma let_result_world_on_base_mono_from_total
    X e x (m n : WfWorld)
    (Hfresh_m : x ∉ world_dom (m : World))
    (Hfresh_n : x ∉ world_dom (n : World))
    (Hresult_m :
      ∀ σ, (m : World) σ →
        ∃ v, subst_map (store_restrict σ (fv_tm e)) e →* tret v)
    (Hresult_n :
      ∀ σ, (n : World) σ →
        ∃ v, subst_map (store_restrict σ (fv_tm e)) e →* tret v) :
  fv_tm e ⊆ X →
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  let_result_world_on e x m Hfresh_m Hresult_m ⊑
    let_result_world_on e x n Hfresh_n Hresult_n.
Proof.
  intros Hfv HXm Hle.
  apply (let_result_world_on_base_mono X); assumption.
Qed.

Lemma let_result_world_on_preserves_context Σ Γ e x (w : WfWorld) Hfresh Hresult :
  w ⊨ denot_ctx_in_env Σ Γ →
  let_result_world_on e x w Hfresh Hresult ⊨ denot_ctx_in_env Σ Γ.
Proof.
  intros Hctx.
  eapply res_models_kripke.
  - apply let_result_world_on_le.
  - exact Hctx.
Qed.

Lemma let_result_world_on_erased_basic
    Σ Γ τ e x (m : WfWorld) Hfresh Hresult :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  x ∉ dom (erase_ctx_under Σ Γ) →
  let_result_world_on e x m Hfresh Hresult ⊨
    basic_world_formula
      (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)))
      (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)))).
Proof.
Admitted.

(** Result-binding compatibility for the let-result world.

    If [m] satisfies [τ] for the expression [e], then the world obtained by
    adding a fresh coordinate [x] containing exactly the possible results of
    [e] satisfies [τ] for [return x].

    This is intentionally a denotation-level transport theorem, not a
    constructor-specific typing case.  The proof must not split into local
    [CTOver]/[CTUnder] cases for the caller.  If structural induction over
    [τ] is needed, it belongs in a generic expression-result transport lemma
    that this theorem instantiates.

    Anti-slip rule: this lemma is about replacing an expression by its fresh
    result representative.  It should be proved by a general
    expression-result transport principle for [denot_ty_on], not by rebuilding
    the proof separately for each type constructor. *)
Lemma denot_ty_on_let_result_representative
    X Σ τ e x (m : WfWorld) Hfresh Hresult :
  basic_choice_ty (dom Σ) τ →
  fv_tm e ⊆ X →
  x ∉ X ∪ fv_cty τ ∪ fv_tm e →
  m ⊨ basic_world_formula Σ (dom Σ) →
  m ⊨ denot_ty_on Σ τ e →
  let_result_world_on e x m Hfresh Hresult ⊨
    denot_ty_on (<[x := erase_ty τ]> Σ) τ (tret (vfvar x)).
Proof.
(** Open: this is the same missing transport principle in a specialized
    representative form.  It should follow from a repaired generic
    expression-result/denotation transport theorem, not from a constructor-by-
    constructor proof over [τ]. *)
Admitted.

Lemma let_result_world_on_bound_type
    Σ Γ τ e x (m : WfWorld) Hfresh Hresult :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ ∪ fv_tm e →
  let_result_world_on e x m Hfresh Hresult ⊨
    denot_ty_on
      (<[x := erase_ty τ]> (erase_ctx_under Σ Γ))
      τ (tret (vfvar x)).
Proof.
  intros Hwf Hm Hτ Hx.
  eapply (denot_ty_on_let_result_representative
    (dom (erase_ctx_under Σ Γ)) (erase_ctx_under Σ Γ) τ e x m Hfresh Hresult).
  - exact (choice_typing_wf_basic_choice_ty_erased Σ Γ e τ Hwf).
  - exact (choice_typing_wf_fv_tm_subset_erase_dom Σ Γ e τ Hwf).
  - exact Hx.
  - apply denot_ctx_in_env_erased_basic. exact Hm.
  - exact Hτ.
Qed.

Lemma let_result_world_on_denot_ctx_in_env
    Σ Γ τ e x (m : WfWorld) Hfresh Hresult :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ ∪ fv_tm e →
  let_result_world_on e x m Hfresh Hresult ⊨
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ)).
Proof.
  intros Hwf Hm Hτ Hx.
  unfold denot_ctx_in_env.
  apply res_models_and_intro_from_models.
  - eapply res_models_kripke.
    + apply let_result_world_on_le.
    + eapply denot_ctx_in_env_basic; eauto.
  - apply res_models_and_intro_from_models.
    + eapply let_result_world_on_erased_basic; eauto. set_solver.
    + apply denot_ctx_under_comma. split.
      * apply denot_ctx_in_env_ctx.
        eapply let_result_world_on_preserves_context; exact Hm.
      * simpl.
        unfold erase_ctx_under.
        eapply let_result_world_on_bound_type; eauto.
Qed.

Lemma let_result_world_on_bound_fresh
    Σ Γ τ e x (m : WfWorld) :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  expr_total_on (dom (erase_ctx_under Σ Γ)) e m →
  x ∉ world_dom (m : World) →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ ∪ fv_tm e.
Proof.
  intros Hwf Hm Htotal Hfresh.
  destruct Htotal as [Hfv_e _].
  assert (Hfv_τ : fv_cty τ ⊆ dom (erase_ctx_under Σ Γ)).
  {
    exact (choice_typing_wf_fv_cty_subset_erase_dom Σ Γ e τ Hwf).
  }
  assert (Hdom_world : dom (erase_ctx_under Σ Γ) ⊆ world_dom (m : World)).
  {
    pose proof (res_models_with_store_fuel_scoped
      (formula_measure (denot_ctx_in_env Σ Γ)) ∅ m
      (denot_ctx_in_env Σ Γ) Hm) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    intros z Hz. apply Hscope.
    apply elem_of_union. right.
    apply denot_ctx_in_env_dom_subset_formula_fv.
    destruct Hwf as [Hwfτ _].
    replace (dom Σ ∪ ctx_dom Γ) with (dom (erase_ctx_under Σ Γ)).
    - exact Hz.
    - symmetry.
      pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ))
        as Hctx.
      unfold erase_ctx_under.
      rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hctx).
      reflexivity.
  }
  apply not_elem_of_union. split.
  - apply not_elem_of_union. split.
    + intros Hbad. apply Hfresh. apply Hdom_world. exact Hbad.
    + intros Hbad. apply Hfresh. apply Hdom_world. apply Hfv_τ. exact Hbad.
  - intros Hbad. apply Hfresh. apply Hdom_world. apply Hfv_e. exact Hbad.
Qed.

Lemma let_result_world_on_le_store_elim
    X e x (n w : WfWorld) Hfresh Hresult σw :
  fv_tm e ⊆ X →
  w ⊑ let_result_world_on e x n Hfresh Hresult →
  X ∪ {[x]} ⊆ world_dom (w : World) →
  x ∉ X →
  (w : World) σw →
  ∃ σ vx,
    (n : World) σ ∧
    σw !! x = Some vx ∧
    store_restrict σw X = store_restrict σ X ∧
    subst_map (store_restrict σw X) e →* tret vx.
Proof.
Admitted.

Lemma lc_env_restrict σ X :
  lc_env σ →
  lc_env (store_restrict σ X).
Proof.
  unfold lc_env. intros Hlc.
  apply map_Forall_lookup_2. intros y v Hlookup.
  apply store_restrict_lookup_some in Hlookup as [_ Hlookup].
  exact (map_Forall_lookup_1 _ _ _ _ Hlc Hlookup).
Qed.

Lemma difference_cons_decompose (X S : aset) (y : atom) :
  y ∈ X →
  y ∉ S →
  X ∖ S = (X ∖ ({[y]} ∪ S)) ∪ {[y]}.
Proof.
  intros HyX HyS.
  apply set_eq. intros z. split.
  - intros Hz.
    destruct (decide (z = y)) as [->|Hzy].
    + set_solver.
    + set_solver.
  - intros Hz. set_solver.
Qed.

Lemma fiber_projection_member_elim (w : WfWorld) X σ Hproj σw :
  (res_fiber_from_projection w X σ Hproj : World) σw →
  (w : World) σw ∧ store_restrict σw (dom σ) = σ.
Proof.
  unfold res_fiber_from_projection, res_fiber, raw_fiber.
  simpl. intros H. exact H.
Qed.

Lemma let_result_world_on_fiber_elim
    X e x (n : WfWorld) Hfresh Hresult ρ Hprojn Hprojlet σx :
  X ⊆ world_dom (n : World) →
  x ∉ X →
  (res_fiber_from_projection
    (let_result_world_on e x n Hfresh Hresult) X ρ Hprojlet : World) σx →
  ∃ σ vx,
    (res_fiber_from_projection n X ρ Hprojn : World) σ ∧
    subst_map (store_restrict σ (fv_tm e)) e →* tret vx ∧
    σx = <[x := vx]> σ.
Proof.
  intros _ HxX [Hσx Hσxρ].
  destruct (let_result_world_on_elim e x n Hfresh Hresult σx Hσx)
    as [σ [vx [Hσ [Hsteps ->]]]].
  exists σ, vx. split.
  - simpl. split; [exact Hσ |].
    assert (Hdomρ : dom ρ ⊆ X).
    { destruct Hprojlet as [τ [_ Hτrestrict]].
      rewrite <- Hτrestrict. rewrite store_restrict_dom. set_solver. }
    assert (Hxdomρ : x ∉ dom ρ) by set_solver.
    assert (Hσρ : store_restrict σ (dom ρ) = ρ).
    {
      transitivity (store_restrict (<[x := vx]> σ) (dom ρ)).
      - symmetry. apply store_restrict_insert_notin. exact Hxdomρ.
      - exact Hσxρ.
    }
    exact Hσρ.
  - split; [exact Hsteps | reflexivity].
Qed.

Lemma let_result_world_on_fiber_intro
    X e x (n : WfWorld) Hfresh Hresult ρ Hprojn Hprojlet σ vx :
  X ⊆ world_dom (n : World) →
  x ∉ X →
  (res_fiber_from_projection n X ρ Hprojn : World) σ →
  subst_map (store_restrict σ X) e →* tret vx →
  (res_fiber_from_projection
    (let_result_world_on e x n Hfresh Hresult) X ρ Hprojlet : World)
    (<[x := vx]> σ).
Proof.
Admitted.

Lemma expr_total_on_tlete_from_open
    (X : aset) e1 e2 x (m : WfWorld) Hfresh Hresult :
  x ∉ X →
  x ∉ fv_tm e2 →
  (∀ σ, (m : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (m : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (m : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  expr_total_on (X ∪ {[x]}) (e2 ^^ x)
    (let_result_world_on e1 x m Hfresh Hresult) →
  fv_tm (tlete e1 e2) ⊆ X →
  expr_total_on X (tlete e1 e2) m.
Proof.
Admitted.

Lemma expr_result_store_tlete_from_body_store
    X e1 e2 x ν σ vx v :
  x ∉ X →
  x ∉ fv_tm e2 →
  closed_env (store_restrict σ X) →
  lc_env (store_restrict σ X) →
  stale vx = ∅ →
  is_lc vx →
  body_tm (subst_map (store_restrict σ X) e2) →
  subst_map (store_restrict σ X) e1 →* tret vx →
  expr_result_store ν (subst_map (<[x := vx]> (store_restrict σ X)) (e2 ^^ x)) {[ν := v]} →
  expr_result_store ν (subst_map (store_restrict σ X) (tlete e1 e2)) {[ν := v]}.
Proof.
  intros HxX Hxe2 Hclosed Hlc Hvx_closed Hvx_lc Hbody He1 Hstore.
  destruct Hstore as [v' [Hσ [Hv_closed [Hv_lc Hbody_steps]]]].
  assert (Hv_eq : v' = v).
  {
    assert (Hlookup : ({[ν := v']} : Store) !! ν = Some v).
    {
      rewrite <- Hσ.
      rewrite lookup_singleton. rewrite decide_True by reflexivity.
      reflexivity.
    }
    rewrite lookup_singleton in Hlookup.
    rewrite decide_True in Hlookup by reflexivity.
    inversion Hlookup. reflexivity.
  }
  subst v'.
  exists v. repeat split; try reflexivity; try exact Hv_closed; try exact Hv_lc.
  eapply (steps_tlete_from_body_projection X e1 e2 x σ vx v); eauto.
Qed.

Lemma expr_result_store_ret_fvar_to_source
    ρ e x ν σ vx σν :
  stale vx = ∅ →
  ν ≠ x →
  σ !! x = None →
  subst_map σ (subst_map ρ e) →* tret vx →
  expr_result_store ν (subst_map ∅ (tret (vfvar x))) σν →
  store_restrict (<[x := vx]> σ) ({[x]} ∪ {[ν]}) = σν →
  expr_result_store ν (subst_map ρ e) σ.
Proof.
  intros _ _ _ _ Hret _.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σν Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.

Lemma expr_result_store_ret_fvar_to_source_restrict
    e x ν σ vx σν :
  let S := stale e ∪ {[ν]} in
  stale vx = ∅ →
  ν ≠ x →
  x ∉ S →
  closed_env (store_restrict σ S) →
  σ !! x = None →
  subst_map σ e →* tret vx →
  expr_result_store ν (subst_map ∅ (tret (vfvar x))) σν →
  store_restrict (<[x := vx]> σ) ({[x]} ∪ {[ν]}) = σν →
  expr_result_store ν (subst_map ∅ e) (store_restrict σ S).
Proof.
  intros S Hvx Hνx HxS Hclosed Hxnone Hsteps_e Hret Hrestrict.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σν Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.

Lemma closed_env_restrict_insert_result σ S ν vx :
  closed_env (store_restrict σ (S ∖ {[ν]})) →
  σ !! ν = Some vx →
  stale vx = ∅ →
  closed_env (store_restrict σ S).
Proof.
  intros Hclosed Hν Hvx.
  unfold closed_env in *.
  apply map_Forall_lookup_2. intros z v Hz.
  apply store_restrict_lookup_some in Hz as [HzS Hzσ].
  destruct (decide (z = ν)) as [->|Hzν].
  - rewrite Hν in Hzσ. inversion Hzσ. subst. exact Hvx.
  - apply (map_Forall_lookup_1 _ _ z v Hclosed).
    apply store_restrict_lookup_some_2; [exact Hzσ | set_solver].
Qed.

Lemma expr_result_in_world_ret_fvar_to_source_pullback
    e x ν (n p : WfWorld) Hle :
  ν ≠ x →
  x ∉ stale e ∪ {[ν]} →
  {[x]} ∪ {[ν]} ⊆ world_dom (p : World) →
  (∀ σx,
    (n : World) σx →
    ∃ σ vx,
      σx = <[x := vx]> σ ∧
      σ !! x = None ∧
      subst_map σ e →* tret vx) →
  (∀ σ vx,
    (n : World) (<[x := vx]> σ) →
    subst_map σ e →* tret vx →
    closed_env (store_restrict σ ((stale e ∪ {[ν]}) ∖ {[ν]}))) →
  (∀ σ vx,
    (n : World) (<[x := vx]> σ) →
    subst_map σ e →* tret vx →
    stale vx = ∅) →
  expr_result_in_world ∅ (tret (vfvar x)) ν
    (res_restrict p ({[x]} ∪ {[ν]})) →
  expr_result_in_world ∅ e ν
    (res_restrict (res_pullback_projection n p Hle) (stale e ∪ {[ν]})).
Proof.
  intros _ _ Hscope _ _ _ Hret_world.
  exfalso.
  destruct (world_wf p) as [[σp Hσp] _].
  set (σxν := store_restrict σp ({[x]} ∪ {[ν]})).
  assert (Hproj_xν : (res_restrict p ({[x]} ∪ {[ν]}) : World) σxν).
  { exists σp. split; [exact Hσp | reflexivity]. }
  set (σν := store_restrict σp {[ν]}).
  assert (Hproj_ν :
    (res_restrict (res_restrict p ({[x]} ∪ {[ν]})) {[ν]} : World) σν).
  {
    exists σxν. split; [exact Hproj_xν |].
    subst σxν σν.
    rewrite store_restrict_restrict.
    replace (({[x]} ∪ {[ν]}) ∩ {[ν]}) with ({[ν]} : aset) by set_solver.
    reflexivity.
  }
  pose proof (expr_result_in_world_sound ∅ (tret (vfvar x)) ν
    (res_restrict p ({[x]} ∪ {[ν]})) σν Hret_world Hproj_ν) as Hret.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σν Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.

(** Semantic compatibility of bunched let.

    This is the remaining tlet-specific denotation theorem.  Its proof should
    combine:
    - [expr_result_in_world_let_intro]/[_elim] for operational composition;
    - [choice_typing_wf_result_closed_in_ctx] for closed intermediate values;
    - the body entailment under [CtxComma Γ (CtxBind x τ1)].

    Keeping this theorem separate prevents the fundamental theorem case from
    doing any recursion on [τ2]. *)
