(** * Denotation.TypePersist

    Semantic support lemmas for the type-level persistency modality. *)

From Denotation Require Import Notation TypeDenote ResultFirstOpen
  DenotationSetMapFacts TypeEquivFiberBaseResult TypeEquiv.

Section TypePersist.

Definition over_open_body (φ : type_qualifier) (z : atom) : FormulaT :=
  FFibVars
    (qual_vars (qual_open_atom 0 z φ) ∖ {[LVFree z]})
    (FOver (FAtom (qual_open_atom 0 z φ))).

Definition under_open_body (φ : type_qualifier) (z : atom) : FormulaT :=
  FFibVars
    (qual_vars (qual_open_atom 0 z φ) ∖ {[LVFree z]})
    (FUnder (FAtom (qual_open_atom 0 z φ))).

Lemma lvars_open0_difference_bound0_normalize D z :
  LVFree z ∉ D ->
  lvars_open 0 z (D ∖ {[LVBound 0]}) =
  lvars_open 0 z D ∖ {[LVFree z]}.
Proof.
  intros HzD.
  apply set_eq. intros a.
  rewrite elem_of_difference.
  split.
  - intros Ha.
    split.
    + change (a ∈ set_swap (LVBound 0) (LVFree z) D).
      change (a ∈ set_swap (LVBound 0) (LVFree z)
        (D ∖ {[LVBound 0]})) in Ha.
      rewrite elem_of_set_swap in Ha.
      rewrite elem_of_set_swap.
      set_solver.
    + intros Haz.
      apply elem_of_singleton in Haz. subst a.
      change (LVFree z ∈ set_swap (LVBound 0) (LVFree z)
        (D ∖ {[LVBound 0]})) in Ha.
      rewrite elem_of_set_swap in Ha.
      apply elem_of_difference in Ha as [_ Hnot].
      apply Hnot. apply elem_of_singleton.
      unfold swap. rewrite decide_False by discriminate.
      rewrite decide_True by reflexivity. reflexivity.
  - intros [Ha Haz].
    change (a ∈ set_swap (LVBound 0) (LVFree z) D) in Ha.
    change (a ∈ set_swap (LVBound 0) (LVFree z)
      (D ∖ {[LVBound 0]})).
    rewrite elem_of_set_swap in Ha.
    rewrite elem_of_set_swap.
    apply elem_of_difference. split; [exact Ha|].
    intros Hbound.
    apply Haz. apply elem_of_singleton.
    apply elem_of_singleton in Hbound.
    unfold swap in Hbound.
    repeat destruct decide; congruence.
Qed.

Lemma formula_open_over_self_body_normalize φ z :
  LVFree z ∉ qual_vars φ ->
  formula_open 0 z
    (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FOver (FAtom φ))) =
  over_open_body φ z.
Proof.
  intros Hzφ.
  unfold over_open_body.
  rewrite formula_open_fibvars, formula_open_over, formula_open_atom.
  rewrite qual_open_atom_vars.
  rewrite lvars_open0_difference_bound0_normalize by exact Hzφ.
  reflexivity.
Qed.

Lemma formula_open_under_self_body_normalize φ z :
  LVFree z ∉ qual_vars φ ->
  formula_open 0 z
    (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FUnder (FAtom φ))) =
  under_open_body φ z.
Proof.
  intros Hzφ.
  unfold under_open_body.
  rewrite formula_open_fibvars, formula_open_under, formula_open_atom.
  rewrite qual_open_atom_vars.
  rewrite lvars_open0_difference_bound0_normalize by exact Hzφ.
  reflexivity.
Qed.

Lemma formula_atom_swap_over_open_body φ x y :
  x ∉ qual_dom φ ->
  y ∉ qual_dom φ ->
  formula_atom_swap x y (over_open_body φ x) =
  over_open_body φ y.
Proof.
  intros Hx Hy.
  set (P := FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FOver (FAtom φ))).
  assert (Hxvars : LVFree x ∉ qual_vars φ).
  {
    intros Hbad. apply Hx.
    unfold qual_dom. apply lvars_fv_elem. exact Hbad.
  }
  assert (Hyvars : LVFree y ∉ qual_vars φ).
  {
    intros Hbad. apply Hy.
    unfold qual_dom. apply lvars_fv_elem. exact Hbad.
  }
  assert (Hxfv : x ∉ formula_fv P).
  {
    subst P. rewrite formula_fv_fibvars, formula_fv_over, formula_fv_atom.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad]; [|exact (Hx Hbad)].
    apply Hx. unfold qual_dom.
    eapply lvars_fv_mono; [|exact Hbad].
    set_solver.
  }
  assert (Hyfv : y ∉ formula_fv P).
  {
    subst P. rewrite formula_fv_fibvars, formula_fv_over, formula_fv_atom.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad]; [|exact (Hy Hbad)].
    apply Hy. unfold qual_dom.
    eapply lvars_fv_mono; [|exact Hbad].
    set_solver.
  }
  rewrite <- (formula_open_over_self_body_normalize φ x Hxvars).
  rewrite formula_atom_swap_open_fresh by (exact Hxfv || exact Hyfv).
  rewrite formula_open_over_self_body_normalize by exact Hyvars.
  reflexivity.
Qed.

Lemma formula_atom_swap_under_open_body φ x y :
  x ∉ qual_dom φ ->
  y ∉ qual_dom φ ->
  formula_atom_swap x y (under_open_body φ x) =
  under_open_body φ y.
Proof.
  intros Hx Hy.
  set (P := FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FUnder (FAtom φ))).
  assert (Hxvars : LVFree x ∉ qual_vars φ).
  {
    intros Hbad. apply Hx.
    unfold qual_dom. apply lvars_fv_elem. exact Hbad.
  }
  assert (Hyvars : LVFree y ∉ qual_vars φ).
  {
    intros Hbad. apply Hy.
    unfold qual_dom. apply lvars_fv_elem. exact Hbad.
  }
  assert (Hxfv : x ∉ formula_fv P).
  {
    subst P. rewrite formula_fv_fibvars, formula_fv_under, formula_fv_atom.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad]; [|exact (Hx Hbad)].
    apply Hx. unfold qual_dom.
    eapply lvars_fv_mono; [|exact Hbad].
    set_solver.
  }
  assert (Hyfv : y ∉ formula_fv P).
  {
    subst P. rewrite formula_fv_fibvars, formula_fv_under, formula_fv_atom.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad]; [|exact (Hy Hbad)].
    apply Hy. unfold qual_dom.
    eapply lvars_fv_mono; [|exact Hbad].
    set_solver.
  }
  rewrite <- (formula_open_under_self_body_normalize φ x Hxvars).
  rewrite formula_atom_swap_open_fresh by (exact Hxfv || exact Hyfv).
  rewrite formula_open_under_self_body_normalize by exact Hyvars.
  reflexivity.
Qed.

Lemma formula_fv_over_open_body_subset φ z :
  formula_fv (over_open_body φ z) ⊆ qual_dom φ ∪ {[z]}.
Proof.
  unfold over_open_body.
  rewrite formula_fv_fibvars, formula_fv_over, formula_fv_atom.
  intros a Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - apply lvars_fv_elem in Ha.
    apply elem_of_difference in Ha as [Ha _].
    rewrite qual_open_atom_vars in Ha.
    pose proof (lvars_fv_open_subset 0 z (qual_vars φ)) as Hsub.
    assert (Ha_fv : a ∈ lvars_fv (lvars_open 0 z (qual_vars φ))).
    { apply lvars_fv_elem. exact Ha. }
    apply Hsub in Ha_fv.
    unfold qual_dom. set_solver.
  - pose proof (qual_open_atom_dom_subset 0 z φ) as Hsub.
    unfold qual_dom in Ha.
    apply Hsub in Ha. set_solver.
Qed.

Lemma formula_fv_under_open_body_subset φ z :
  formula_fv (under_open_body φ z) ⊆ qual_dom φ ∪ {[z]}.
Proof.
  unfold under_open_body.
  rewrite formula_fv_fibvars, formula_fv_under, formula_fv_atom.
  intros a Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - apply lvars_fv_elem in Ha.
    apply elem_of_difference in Ha as [Ha _].
    rewrite qual_open_atom_vars in Ha.
    pose proof (lvars_fv_open_subset 0 z (qual_vars φ)) as Hsub.
    assert (Ha_fv : a ∈ lvars_fv (lvars_open 0 z (qual_vars φ))).
    { apply lvars_fv_elem. exact Ha. }
    apply Hsub in Ha_fv.
    unfold qual_dom. set_solver.
  - pose proof (qual_open_atom_dom_subset 0 z φ) as Hsub.
    unfold qual_dom in Ha.
    apply Hsub in Ha. set_solver.
Qed.

Lemma ty_denote_gas_persist_open_result
    gas (Σ : lty_env) τ e y (m my : WfWorldT) :
  m ⊨ ty_denote_gas (S gas) Σ (CTPersist τ) e ->
  y ∉ world_dom (m : WorldT) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ formula_open 0 y
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env Σ (CTPersist τ) e)))
      (tm_shift 0 e) (LVBound 0)) ->
  my ⊨ formula_open 0 y
    (FPersist
      (ty_denote_gas gas
        (typed_lty_env_bind
          (relevant_env Σ (CTPersist τ) e)
          (erase_ty (CTPersist τ)))
        (cty_shift 0 τ) (tret (vbvar 0)))).
Proof.
  intros Hden Hy Hdom Hrestrict Hresult.
  cbn [ty_denote_gas] in Hden.
  rewrite res_models_and_iff in Hden.
  destruct Hden as [_ Hbody].
  eapply result_first_forall_impl_open_elim; eauto.
Qed.

Lemma expr_result_formula_at_ret_fvar_lookup_eq
    D x y (m : WfWorldT) σ :
  tm_lvars (tret (vfvar x)) ⊆ D ->
  LVFree y ∉ D ->
  store_closed (store_restrict σ ({[x]} : aset)) ->
  x ∈ dom (store_restrict σ ({[x]} : aset) : StoreT) ->
  m ⊨ expr_result_formula_at D (tret (vfvar x)) (LVFree y) ->
  (m : WorldT) σ ->
  σ !! y = σ !! x.
Proof.
  intros HD HyD Hclosed Hxdom Hres Hσ.
  pose proof (expr_result_formula_at_models_elim
    D (tret (vfvar x)) y m HD HyD Hres σ Hσ) as Hstore.
  destruct Hstore as [_ [v [Hy Heval]]].
  assert (Heval_restrict :
      tm_eval_in_store (store_restrict σ ({[x]} : aset))
        (tret (vfvar x)) v).
  {
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tret (vfvar x)) v ({[x]} : aset)
      ltac:(cbn [fv_tm fv_value]; set_solver))).
    exact Heval.
  }
  pose proof (tm_eval_in_store_ret_fvar_inv
    (store_restrict σ ({[x]} : aset)) x v Hclosed Hxdom Heval_restrict)
    as Hx.
  rewrite lstore_lift_free_lookup_free in Hy.
  apply storeA_restrict_lookup_some in Hx as [_ Hx].
  transitivity (Some v); [exact Hy|symmetry; exact Hx].
Qed.

Lemma expr_result_formula_at_ret_fvar_flip
    Dsrc Dtgt x y (m : WfWorldT) :
  tm_lvars (tret (vfvar x)) ⊆ Dsrc ->
  LVFree y ∉ Dsrc ->
  lc_lvars Dtgt ->
  tm_lvars (tret (vfvar y)) ⊆ Dtgt ->
  LVFree x ∉ Dtgt ->
  lvars_fv Dtgt ∪ {[x; y]} ⊆ world_dom (m : WorldT) ->
  wfworld_closed_on ({[x]} : aset) m ->
  wfworld_closed_on ({[y]} : aset) m ->
  m ⊨ expr_result_formula_at Dsrc (tret (vfvar x)) (LVFree y) ->
  m ⊨ expr_result_formula_at Dtgt (tret (vfvar y)) (LVFree x).
Proof.
  intros HsrcD HyD HlcDtgt HtgtD HxD Hscope_dom Hclosed_x Hclosed_y Hres.
  eapply expr_result_formula_at_intro.
  - exact HlcDtgt.
  - exact HtgtD.
  - exact HxD.
  - unfold formula_scoped_in_world.
    rewrite formula_fv_expr_result_formula_at.
    cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
    rewrite lvars_fv_union, !lvars_fv_singleton_free.
    intros a Ha. apply Hscope_dom.
    set_solver.
  - intros σ Hσ.
    pose proof (expr_result_formula_at_ret_fvar_lookup_eq
      Dsrc x y m σ HsrcD HyD (Hclosed_x σ Hσ) ltac:(
        change (x ∈ dom (storeA_restrict σ ({[x]} : aset) : gmap atom value));
        rewrite storeA_restrict_dom;
        rewrite (wfworld_store_dom m σ Hσ);
        set_solver) Hres Hσ) as Hxy.
    unfold expr_result_at_store.
    split.
    + intros Hbad. apply HxD. apply HtgtD.
      exact Hbad.
    + destruct (σ !! y) as [v|] eqn:Hylookup.
      * exists v. split.
        -- rewrite lstore_lift_free_lookup_free.
           rewrite <- Hxy. reflexivity.
        -- apply (proj1 (tm_eval_in_store_restrict_fv_subset
             σ (tret (vfvar y)) v ({[y]} : aset)
             ltac:(cbn [fv_tm fv_value]; set_solver))).
           apply tm_eval_in_store_ret_fvar_lookup.
           ++ exact (Hclosed_y σ Hσ).
           ++ change ((storeA_restrict σ ({[y]} : aset) : gmap atom value)
                !! y = Some v).
              apply storeA_restrict_lookup_some_2; [exact Hylookup|set_solver].
      * exfalso.
        apply not_elem_of_dom in Hylookup.
        apply Hylookup.
        rewrite (wfworld_store_dom m σ Hσ).
        set_solver.
  - intros σ v Hσ Heval.
    exists σ. split; [exact Hσ|]. split; [reflexivity|].
    pose proof (expr_result_formula_at_ret_fvar_lookup_eq
      Dsrc x y m σ HsrcD HyD (Hclosed_x σ Hσ) ltac:(
        change (x ∈ dom (storeA_restrict σ ({[x]} : aset) : gmap atom value));
        rewrite storeA_restrict_dom;
        rewrite (wfworld_store_dom m σ Hσ);
        set_solver) Hres Hσ) as Hxy.
    pose proof (tm_eval_in_store_ret_fvar_inv
      (store_restrict σ ({[y]} : aset)) y v) as Hinv.
    assert (Hclosed_yσ : store_closed (store_restrict σ ({[y]} : aset))).
    { exact (Hclosed_y σ Hσ). }
    assert (Hydom :
        y ∈ dom (store_restrict σ ({[y]} : aset) : StoreT)).
    {
      change (y ∈ dom (storeA_restrict σ ({[y]} : aset) : gmap atom value)).
      rewrite storeA_restrict_dom.
      rewrite (wfworld_store_dom m σ Hσ).
      set_solver.
    }
    change (tm_eval_in_store (store_restrict σ ({[y]} : aset))
      (tret (vfvar y)) v) in Heval.
    specialize (Hinv Hclosed_yσ Hydom Heval).
    apply storeA_restrict_lookup_some in Hinv as [_ Hlookup_y].
    rewrite <- Hxy. exact Hlookup_y.
Qed.

Lemma res_restrict_ret_fvar_result_swap_projection
    A D x y (m my : WfWorldT) :
  A ⊆ world_dom (m : WorldT) ->
  x ∈ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  x ∉ A ->
  y ∉ A ->
  tm_lvars (tret (vfvar x)) ⊆ D ->
  LVFree y ∉ D ->
  my ⊨ expr_result_formula_at D (tret (vfvar x)) (LVFree y) ->
  wfworld_closed_on ({[x]} : aset) my ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  res_restrict my (A ∪ {[y]}) =
    res_atom_swap x y (res_restrict m (A ∪ {[x]})).
Proof.
  intros HAm Hxm Hym HxA HyA HD HyD Hres Hclosed_x Hdom_my Hbase.
  apply wfworld_ext. apply world_ext.
  - rewrite res_restrict_dom, world_dom_res_atom_swap, res_restrict_dom.
    rewrite Hdom_my.
    apply set_eq. intros a.
    rewrite elem_of_intersection, elem_of_union.
    rewrite set_swap_elem, elem_of_intersection, elem_of_union.
    unfold swap. repeat destruct decide; set_solver.
  - intros σ. split.
    + intros [σmy [Hσmy Hσeq]]. subst σ.
      set (σm := store_restrict σmy (world_dom (m : WorldT)) : StoreT).
      assert (Hσm : (m : WorldT) σm).
      {
        rewrite <- Hbase.
        subst σm. exists σmy. split; [exact Hσmy|reflexivity].
      }
      exists (store_restrict σm (A ∪ {[x]}) : StoreT). split.
      * exists σm. split; [exact Hσm|reflexivity].
      * apply storeA_map_eq. intros a.
        cbn.
        rewrite !storeA_restrict_lookup.
        destruct (decide (a ∈ A ∪ {[y]})) as [Ha|Ha].
        -- destruct (decide (a = y)) as [->|Hay].
           ++ assert (Hxy : σmy !! y = σmy !! x).
              {
                eapply (expr_result_formula_at_ret_fvar_lookup_eq
                  D x y my σmy);
                  [exact HD|exact HyD|exact (Hclosed_x σmy Hσmy)| |exact Hres|exact Hσmy].
                change (x ∈ dom (storeA_restrict σmy ({[x]} : aset) : gmap atom value)).
                rewrite storeA_restrict_dom.
                rewrite (wfworld_store_dom my σmy Hσmy), Hdom_my.
                set_solver.
              }
              subst σm.
              change ((storeA_swap x y
                (store_restrict (store_restrict σmy (world_dom (m : WorldT)))
                  (A ∪ {[x]}) : StoreT) : gmap atom value) !! y =
                σmy !! y).
              replace y with (swap x y x) by
                (unfold swap; repeat destruct decide; try congruence;
                 exfalso; apply Hym; subst; exact Hxm).
              replace (swap x y x) with (swap x (swap x y x) x) at 1 by
                (unfold swap; repeat destruct decide; try congruence;
                 exfalso; apply Hym; subst; exact Hxm).
              rewrite (storeA_swap_lookup x (swap x y x)
                (store_restrict (store_restrict σmy (world_dom (m : WorldT)))
                  (A ∪ {[x]}) : StoreT) x).
              replace (swap x y x) with y by
                (unfold swap; repeat destruct decide; try congruence;
                 exfalso; apply Hym; subst; exact Hxm).
              rewrite storeA_restrict_lookup.
              rewrite decide_True by set_solver.
              rewrite storeA_restrict_lookup.
              rewrite decide_True by exact Hxm.
              symmetry. exact Hxy.
           ++ assert (HaA : a ∈ A) by set_solver.
              change ((storeA_swap x y
                (store_restrict σm (A ∪ {[x]}) : StoreT)
                : gmap atom value) !! a = σmy !! a).
              replace a with (swap x y a) at 1 by
                (unfold swap; repeat destruct decide; set_solver).
              rewrite (storeA_swap_lookup x y
                (store_restrict σm (A ∪ {[x]}) : StoreT) a).
              rewrite storeA_restrict_lookup.
              rewrite decide_True by set_solver.
              subst σm.
              rewrite storeA_restrict_lookup.
              rewrite decide_True by (apply HAm; exact HaA).
              unfold swap. repeat destruct decide; try congruence.
              reflexivity.
        -- change ((storeA_swap x y
              (store_restrict σm (A ∪ {[x]}) : StoreT)
              : gmap atom value) !! a = None).
           destruct (decide (a = x)) as [->|Hax].
           ++ replace x with (swap x y y) at 1 by
                (unfold swap; repeat destruct decide; try congruence;
                 exfalso; apply Hym; subst; exact Hxm).
              rewrite (storeA_swap_lookup x y
                (store_restrict σm (A ∪ {[x]}) : StoreT) y).
              apply storeA_restrict_lookup_none_r. set_solver.
           ++ replace a with (swap x y a) at 1 by
                (unfold swap; repeat destruct decide; set_solver).
              rewrite (storeA_swap_lookup x y
                (store_restrict σm (A ∪ {[x]}) : StoreT) a).
              apply storeA_restrict_lookup_none_r. set_solver.
    + intros [σr [[σm [Hσm Hσm_eq]] Hσswap]]. subst σr σ.
      assert (Hσm_proj : (res_restrict my (world_dom (m : WorldT)) : WorldT) σm).
      { rewrite Hbase. exact Hσm. }
      destruct Hσm_proj as [σmy [Hσmy Hσmy_base]].
      exists σmy. split; [exact Hσmy|].
      apply storeA_map_eq. intros a.
      cbn.
      rewrite !storeA_restrict_lookup.
      destruct (decide (a ∈ A ∪ {[y]})) as [Ha|Ha].
      * destruct (decide (a = y)) as [->|Hay].
        -- assert (Hxy : σmy !! y = σmy !! x).
           {
             eapply (expr_result_formula_at_ret_fvar_lookup_eq
               D x y my σmy);
	               [exact HD|exact HyD|exact (Hclosed_x σmy Hσmy)| |exact Hres|exact Hσmy].
	             change (x ∈ dom (storeA_restrict σmy ({[x]} : aset) : gmap atom value)).
	             rewrite storeA_restrict_dom.
	             rewrite (wfworld_store_dom my σmy Hσmy), Hdom_my.
	             set_solver.
	           }
	           change (σmy !! y = (storeA_swap x y
	             (store_restrict σm (A ∪ {[x]}) : StoreT)
	             : gmap atom value) !! y).
	           replace y with (swap x y x) at 2 by
	             (unfold swap; repeat destruct decide; try congruence;
	              exfalso; apply Hym; subst; exact Hxm).
	           rewrite (storeA_swap_lookup x y
	             (store_restrict σm (A ∪ {[x]}) : StoreT) x).
	           rewrite storeA_restrict_lookup.
	           rewrite decide_True by set_solver.
	           assert (Hxbase : σm !! x = σmy !! x).
	           {
	             symmetry.
	             eapply store_lookup_eq_of_restrict_eq_full.
             - exact Hxm.
             - exact Hσmy_base.
           }
	           transitivity (σmy !! x); [exact Hxy|].
	           symmetry. exact Hxbase.
	        -- assert (HaA : a ∈ A) by set_solver.
	           change (σmy !! a = (storeA_swap x y
	             (store_restrict σm (A ∪ {[x]}) : StoreT)
	             : gmap atom value) !! a).
	           replace a with (swap x y a) at 2 by
	             (unfold swap; repeat destruct decide; set_solver).
	           rewrite (storeA_swap_lookup x y
	             (store_restrict σm (A ∪ {[x]}) : StoreT) a).
	           rewrite storeA_restrict_lookup.
	           rewrite decide_True by set_solver.
	           assert (Habase : σm !! a = σmy !! a).
	           {
	             symmetry.
	             eapply store_lookup_eq_of_restrict_eq_full.
	             - apply HAm. exact HaA.
	             - exact Hσmy_base.
	           }
	           symmetry. exact Habase.
	      * change (None = (storeA_swap x y
	            (store_restrict σm (A ∪ {[x]}) : StoreT)
	            : gmap atom value) !! a).
	        destruct (decide (a = x)) as [->|Hax].
	        -- replace x with (swap x y y) at 1 by
	             (unfold swap; repeat destruct decide; try congruence;
	              exfalso; apply Hym; subst; exact Hxm).
	           rewrite (storeA_swap_lookup x y
	             (store_restrict σm (A ∪ {[x]}) : StoreT) y).
	           symmetry. apply storeA_restrict_lookup_none_r. set_solver.
	        -- replace a with (swap x y a) at 1 by
	             (unfold swap; repeat destruct decide; set_solver).
	           rewrite (storeA_swap_lookup x y
	             (store_restrict σm (A ∪ {[x]}) : StoreT) a).
	           symmetry. apply storeA_restrict_lookup_none_r. set_solver.
Qed.

Lemma over_open_body_transport_ret_fvar_result
    D φ x y (m my : WfWorldT) :
  qual_dom φ ⊆ world_dom (m : WorldT) ->
  x ∈ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  x ∉ qual_dom φ ->
  y ∉ qual_dom φ ->
  tm_lvars (tret (vfvar x)) ⊆ D ->
  LVFree y ∉ D ->
  my ⊨ expr_result_formula_at D (tret (vfvar x)) (LVFree y) ->
  wfworld_closed_on ({[x]} : aset) my ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ over_open_body φ y ->
  m ⊨ over_open_body φ x.
Proof.
  intros Hφm Hxm Hym Hxφ Hyφ HD HyD Hres Hclosed_x Hdom_my Hbase Hbody_y.
  pose proof (res_restrict_ret_fvar_result_swap_projection
    (qual_dom φ) D x y m my Hφm Hxm Hym Hxφ Hyφ HD HyD Hres
    Hclosed_x Hdom_my Hbase) as Hproj.
  set (Sy := qual_dom φ ∪ {[y]}).
  set (Sx := qual_dom φ ∪ {[x]}).
  assert (Hbody_y_restrict : res_restrict my Sy ⊨ over_open_body φ y).
  {
    pose proof (res_models_minimal_on Sy my (over_open_body φ y)
      ltac:(subst Sy; apply formula_fv_over_open_body_subset)) as Hmin.
    exact (proj1 Hmin Hbody_y).
  }
  change Sy with (qual_dom φ ∪ {[y]}) in Hbody_y_restrict.
  rewrite Hproj in Hbody_y_restrict.
  assert (Hsw :
      res_atom_swap x y (res_restrict m Sx) ⊨
      formula_atom_swap x y (over_open_body φ x)).
  {
    rewrite formula_atom_swap_over_open_body by assumption.
    subst Sx. exact Hbody_y_restrict.
  }
  pose proof (proj1 (res_models_atom_swap (res_restrict m Sx)
    (over_open_body φ x) x y) Hsw) as Hbody_x_restrict.
  pose proof (res_models_minimal_on Sx m (over_open_body φ x)
    ltac:(subst Sx; apply formula_fv_over_open_body_subset)) as Hmin_x.
  exact (proj2 Hmin_x Hbody_x_restrict).
Qed.

Lemma under_open_body_transport_ret_fvar_result
    D φ x y (m my : WfWorldT) :
  qual_dom φ ⊆ world_dom (m : WorldT) ->
  x ∈ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  x ∉ qual_dom φ ->
  y ∉ qual_dom φ ->
  tm_lvars (tret (vfvar x)) ⊆ D ->
  LVFree y ∉ D ->
  my ⊨ expr_result_formula_at D (tret (vfvar x)) (LVFree y) ->
  wfworld_closed_on ({[x]} : aset) my ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ under_open_body φ y ->
  m ⊨ under_open_body φ x.
Proof.
  intros Hφm Hxm Hym Hxφ Hyφ HD HyD Hres Hclosed_x Hdom_my Hbase Hbody_y.
  pose proof (res_restrict_ret_fvar_result_swap_projection
    (qual_dom φ) D x y m my Hφm Hxm Hym Hxφ Hyφ HD HyD Hres
    Hclosed_x Hdom_my Hbase) as Hproj.
  set (Sy := qual_dom φ ∪ {[y]}).
  set (Sx := qual_dom φ ∪ {[x]}).
  assert (Hbody_y_restrict : res_restrict my Sy ⊨ under_open_body φ y).
  {
    pose proof (res_models_minimal_on Sy my (under_open_body φ y)
      ltac:(subst Sy; apply formula_fv_under_open_body_subset)) as Hmin.
    exact (proj1 Hmin Hbody_y).
  }
  change Sy with (qual_dom φ ∪ {[y]}) in Hbody_y_restrict.
  rewrite Hproj in Hbody_y_restrict.
  assert (Hsw :
      res_atom_swap x y (res_restrict m Sx) ⊨
      formula_atom_swap x y (under_open_body φ x)).
  {
    rewrite formula_atom_swap_under_open_body by assumption.
    subst Sx. exact Hbody_y_restrict.
  }
  pose proof (proj1 (res_models_atom_swap (res_restrict m Sx)
    (under_open_body φ x) x y) Hsw) as Hbody_x_restrict.
  pose proof (res_models_minimal_on Sx m (under_open_body φ x)
    ltac:(subst Sx; apply formula_fv_under_open_body_subset)) as Hmin_x.
  exact (proj2 Hmin_x Hbody_x_restrict).
Qed.

Lemma res_restrict_singleton_pullback_ret_fvar_result
    A D x y (m my : WfWorldT) σy :
  A ⊆ world_dom (m : WorldT) ->
  x ∈ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  x ∉ A ->
  y ∉ A ->
  tm_lvars (tret (vfvar x)) ⊆ D ->
  LVFree y ∉ D ->
  my ⊨ expr_result_formula_at D (tret (vfvar x)) (LVFree y) ->
  wfworld_closed_on ({[x]} : aset) my ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  res_restrict my (A ∪ {[y]}) =
    (exist _ (singleton_world σy) (wf_singleton_world σy) : WfWorldT) ->
  exists σx : StoreT,
    dom (σx : StoreT) = A ∪ {[x]} /\
    res_restrict m (A ∪ {[x]}) =
      (exist _ (singleton_world σx) (wf_singleton_world σx) : WfWorldT).
Proof.
  intros HAm Hxm Hym HxA HyA HD HyD Hres Hclosed_x Hdom_my Hbase
    Hsingle_y.
  destruct (wfA_ne _ (worldA_wf m)) as [σ0 Hσ0].
  set (σx := store_restrict σ0 (A ∪ {[x]}) : StoreT).
  exists σx.
  assert (Hdomσx : dom (σx : StoreT) = A ∪ {[x]}).
  {
    subst σx.
    change (dom (storeA_restrict σ0 (A ∪ {[x]}) : gmap atom value) =
      A ∪ {[x]}).
    rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom m σ0 Hσ0).
    apply set_eq. intros a. set_solver.
  }
  split; [exact Hdomσx|].
  apply wfworld_ext. apply world_ext.
  - change (world_dom (res_restrict m (A ∪ {[x]}) : WorldT) =
      dom (σx : StoreT)).
    rewrite res_restrict_dom, Hdomσx.
    apply set_eq. intros a. set_solver.
  - intros σ. split.
    + intros Hσproj.
      destruct Hσproj as [σm [Hσm Hσeq]]. subst σ.
      rewrite <- Hbase in Hσm.
      destruct Hσm as [σmy [Hσmy Hσmy_base]].
      assert (Hσ0proj : (res_restrict my (world_dom (m : WorldT)) : WorldT) σ0).
      { rewrite Hbase. exact Hσ0. }
      destruct Hσ0proj as [σ0my [Hσ0my Hσ0my_base]].
      pose proof (res_restrict_singleton_store_eq
        my (A ∪ {[y]}) σy σmy Hsingle_y Hσmy) as Hσmy_y.
      pose proof (res_restrict_singleton_store_eq
        my (A ∪ {[y]}) σy σ0my Hsingle_y Hσ0my) as Hσ0my_y.
      assert (Hxy_my : σmy !! y = σmy !! x).
      {
        eapply (expr_result_formula_at_ret_fvar_lookup_eq
          D x y my σmy);
          [exact HD|exact HyD|exact (Hclosed_x σmy Hσmy)| |exact Hres|exact Hσmy].
        change (x ∈ dom (storeA_restrict σmy ({[x]} : aset) : gmap atom value)).
        rewrite storeA_restrict_dom.
        rewrite (wfworld_store_dom my σmy Hσmy), Hdom_my.
        set_solver.
      }
      assert (Hxy_0 : σ0my !! y = σ0my !! x).
      {
        eapply (expr_result_formula_at_ret_fvar_lookup_eq
          D x y my σ0my);
          [exact HD|exact HyD|exact (Hclosed_x σ0my Hσ0my)| |exact Hres|exact Hσ0my].
        change (x ∈ dom (storeA_restrict σ0my ({[x]} : aset) : gmap atom value)).
        rewrite storeA_restrict_dom.
        rewrite (wfworld_store_dom my σ0my Hσ0my), Hdom_my.
        set_solver.
      }
      subst σx.
      apply storeA_map_eq. intros a.
      rewrite !storeA_restrict_lookup.
      destruct (decide (a ∈ A ∪ {[x]})) as [Ha|Ha].
      * destruct (decide (a = x)) as [->|Hax].
        -- assert (Hbase_my_x : σmy !! x = σm !! x).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact Hxm.
             - exact Hσmy_base.
           }
           assert (Hbase_0_x : σ0my !! x = σ0 !! x).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact Hxm.
             - exact Hσ0my_base.
           }
           assert (Hy_my : σmy !! y = σy !! y).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_r. apply elem_of_singleton. reflexivity.
             - exact Hσmy_y.
           }
           assert (Hy_0 : σ0my !! y = σy !! y).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_r. apply elem_of_singleton. reflexivity.
             - exact Hσ0my_y.
           }
           change (σm !! x = σ0 !! x).
           rewrite <- Hbase_my_x, <- Hbase_0_x.
           rewrite <- Hxy_my, <- Hxy_0.
           congruence.
        -- assert (HaA : a ∈ A) by set_solver.
           assert (HaDom : a ∈ world_dom (m : WorldT)) by set_solver.
           assert (Hbase_my_a : σmy !! a = σm !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact HaDom.
             - exact Hσmy_base.
           }
           assert (Hbase_0_a : σ0my !! a = σ0 !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact HaDom.
             - exact Hσ0my_base.
           }
           assert (Hy_my_a : σmy !! a = σy !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_l. exact HaA.
             - exact Hσmy_y.
           }
           assert (Hy_0_a : σ0my !! a = σy !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_l. exact HaA.
             - exact Hσ0my_y.
           }
           change (σm !! a = σ0 !! a).
           rewrite <- Hbase_my_a, <- Hbase_0_a.
           congruence.
      * reflexivity.
    + intros Hσ.
      unfold singleton_world in Hσ.
      cbn [raw_world raw_worldA] in Hσ.
      change (σ = store_restrict σ0 (A ∪ {[x]})) in Hσ.
      subst σ.
      exists σ0. split; [exact Hσ0|reflexivity].
Qed.

Lemma res_restrict_singleton_push_ret_fvar_result
    A D x y (m my : WfWorldT) σx :
  A ⊆ world_dom (m : WorldT) ->
  x ∈ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  x ∉ A ->
  y ∉ A ->
  tm_lvars (tret (vfvar x)) ⊆ D ->
  LVFree y ∉ D ->
  my ⊨ expr_result_formula_at D (tret (vfvar x)) (LVFree y) ->
  wfworld_closed_on ({[x]} : aset) my ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  res_restrict m (A ∪ {[x]}) =
    (exist _ (singleton_world σx) (wf_singleton_world σx) : WfWorldT) ->
  exists σy : StoreT,
    dom (σy : StoreT) = A ∪ {[y]} /\
    res_restrict my (A ∪ {[y]}) =
      (exist _ (singleton_world σy) (wf_singleton_world σy) : WfWorldT).
Proof.
  intros HAm Hxm Hym HxA HyA HD HyD Hres Hclosed_x Hdom_my Hbase
    Hsingle_x.
  destruct (wfA_ne _ (worldA_wf my)) as [σ0 Hσ0].
  set (σy := store_restrict σ0 (A ∪ {[y]}) : StoreT).
  exists σy.
  assert (Hdomσy : dom (σy : StoreT) = A ∪ {[y]}).
  {
    subst σy.
    change (dom (storeA_restrict σ0 (A ∪ {[y]}) : gmap atom value) =
      A ∪ {[y]}).
    rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
    apply set_eq. intros a. set_solver.
  }
  split; [exact Hdomσy|].
  apply wfworld_ext. apply world_ext.
  - change (world_dom (res_restrict my (A ∪ {[y]}) : WorldT) =
      dom (σy : StoreT)).
    rewrite res_restrict_dom, Hdomσy.
    apply set_eq. intros a. set_solver.
  - intros σ. split.
    + intros Hσproj.
      destruct Hσproj as [σmy [Hσmy Hσeq]]. subst σ.
      set (σm := store_restrict σmy (world_dom (m : WorldT)) : StoreT).
      assert (Hσm : (m : WorldT) σm).
      {
        rewrite <- Hbase.
        subst σm. exists σmy. split; [exact Hσmy|reflexivity].
      }
      assert (Hσm_base : store_restrict σmy (world_dom (m : WorldT)) = σm)
        by (subst σm; reflexivity).
      assert (Hσ0_base : (res_restrict my (world_dom (m : WorldT)) : WorldT)
          (store_restrict σ0 (world_dom (m : WorldT)))).
      {
        exists σ0. split; [exact Hσ0|reflexivity].
      }
      rewrite Hbase in Hσ0_base.
      pose proof (res_restrict_singleton_store_eq
        m (A ∪ {[x]}) σx σm Hsingle_x Hσm) as Hσm_x.
      pose proof (res_restrict_singleton_store_eq
        m (A ∪ {[x]}) σx
        (store_restrict σ0 (world_dom (m : WorldT)))
        Hsingle_x Hσ0_base) as Hσ0_x.
      assert (Hxy_my : σmy !! y = σmy !! x).
      {
        eapply (expr_result_formula_at_ret_fvar_lookup_eq
          D x y my σmy);
          [exact HD|exact HyD|exact (Hclosed_x σmy Hσmy)| |exact Hres|exact Hσmy].
        change (x ∈ dom (storeA_restrict σmy ({[x]} : aset) : gmap atom value)).
        rewrite storeA_restrict_dom.
        rewrite (wfworld_store_dom my σmy Hσmy), Hdom_my.
        set_solver.
      }
      assert (Hxy_0 : σ0 !! y = σ0 !! x).
      {
        eapply (expr_result_formula_at_ret_fvar_lookup_eq
          D x y my σ0);
          [exact HD|exact HyD|exact (Hclosed_x σ0 Hσ0)| |exact Hres|exact Hσ0].
        change (x ∈ dom (storeA_restrict σ0 ({[x]} : aset) : gmap atom value)).
        rewrite storeA_restrict_dom.
        rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
        set_solver.
      }
      subst σy.
      apply storeA_map_eq. intros a.
      rewrite !storeA_restrict_lookup.
      destruct (decide (a ∈ A ∪ {[y]})) as [Ha|Ha].
      * destruct (decide (a = y)) as [->|Hay].
        -- assert (Hmy_x : σmy !! x = σm !! x).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact Hxm.
             - exact Hσm_base.
           }
           assert (H0_x :
               σ0 !! x = store_restrict σ0 (world_dom (m : WorldT)) !! x).
           {
             destruct (σ0 !! x) as [vx|] eqn:H0look.
             - symmetry.
               change (
                 (storeA_restrict σ0 (world_dom (m : WorldT))
                   : gmap atom value) !! x = Some vx).
               apply storeA_restrict_lookup_some_2; [exact H0look|exact Hxm].
             - exfalso.
               apply not_elem_of_dom in H0look.
               apply H0look.
               rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
               set_solver.
           }
           assert (H0base_x :
               store_restrict σ0 (world_dom (m : WorldT)) !! x =
               σx !! x).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_r. apply elem_of_singleton. reflexivity.
             - exact Hσ0_x.
           }
           assert (Hm_x :
               σm !! x = σx !! x).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_r. apply elem_of_singleton. reflexivity.
             - exact Hσm_x.
           }
           change (σmy !! y = σ0 !! y).
           rewrite Hxy_my, Hxy_0.
           rewrite Hmy_x, H0_x, H0base_x, Hm_x.
           reflexivity.
        -- assert (HaA : a ∈ A) by set_solver.
           assert (HaDom : a ∈ world_dom (m : WorldT)) by set_solver.
           assert (Hmy_a : σmy !! a = σm !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact HaDom.
             - exact Hσm_base.
           }
           assert (H0_a :
               σ0 !! a = store_restrict σ0 (world_dom (m : WorldT)) !! a).
           {
             destruct (σ0 !! a) as [va|] eqn:H0look.
             - symmetry.
               change (
                 (storeA_restrict σ0 (world_dom (m : WorldT))
                   : gmap atom value) !! a = Some va).
               apply storeA_restrict_lookup_some_2; [exact H0look|exact HaDom].
             - exfalso.
               apply not_elem_of_dom in H0look.
               apply H0look.
               rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
               set_solver.
           }
           assert (H0base_a :
               store_restrict σ0 (world_dom (m : WorldT)) !! a =
               σx !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_l. exact HaA.
             - exact Hσ0_x.
           }
           assert (Hm_a : σm !! a = σx !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_l. exact HaA.
             - exact Hσm_x.
           }
           change (σmy !! a = σ0 !! a).
           rewrite Hmy_a, H0_a, H0base_a, Hm_a.
           reflexivity.
      * reflexivity.
    + intros Hσ.
      unfold singleton_world in Hσ.
      cbn [raw_world raw_worldA] in Hσ.
      change (σ = store_restrict σ0 (A ∪ {[y]})) in Hσ.
      subst σ.
      exists σ0. split; [exact Hσ0|reflexivity].
Qed.

End TypePersist.
