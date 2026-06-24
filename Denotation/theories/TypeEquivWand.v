(** * Denotation.TypeEquivWand

    Wand case for term-result-equivalence transport. *)

From Denotation Require Import Notation TypeDenote.
From Denotation Require Import
  TypeEquivCore
  TypeEquivTerm
  TypeEquivFiberTransport
  TypeEquivBody
  TypeEquivArrow.

Section TypeDenote.

Local Ltac wand_union_member :=
  first
    [ assumption
    | apply elem_of_union_l; wand_union_member
    | apply elem_of_union_r; wand_union_member ].

Local Ltac wand_fresh_from_disjoint Hfresh :=
  intros Hy;
  eapply Hfresh;
    [ apply elem_of_union_l; apply elem_of_singleton; reflexivity
    | subst; wand_union_member ].

Local Lemma lty_env_closed_empty : lty_env_closed (∅ : lty_env).
Proof.
  unfold lvar_store_closed, lc_lvars.
  rewrite dom_empty_L.
  intros v Hv. apply not_elem_of_empty in Hv. contradiction.
Qed.

Local Lemma wand_open_world_term_scope
    (Σ : lty_env) τx τr e1 e2 (m my : WfWorldT) y :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (my : WorldT).
Proof.
  intros Hequiv Hdom a Ha.
  rewrite Hdom.
  apply elem_of_union_l.
  exact (typed_total_equiv_term_scope
    Σ (CTWand τx τr) m e1 e2 Hequiv a Ha).
Qed.

Local Lemma wand_open_product_tapp_tgt_scope
    (Σ : lty_env) τx τr e1 e2 (m my n : WfWorldT)
    y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  fv_tm (tapp_tm e2 (vfvar y)) ⊆ world_dom (res_product n my Hc : WorldT).
Proof.
  intros Hequiv Hdom a Ha.
  rewrite fv_tapp_tm in Ha.
  cbn [fv_value] in Ha.
  pose proof (raw_le_dom (my : WorldT)
    (res_product n my Hc : WorldT)
    (res_product_le_r n my Hc)) as Hdom_le.
  apply Hdom_le.
  apply elem_of_union in Ha as [Ha|Ha].
  - eapply wand_open_world_term_scope; [exact Hequiv|exact Hdom|].
    apply elem_of_union_r. exact Ha.
  - apply elem_of_singleton in Ha. subst a.
    rewrite Hdom. apply elem_of_union_r. apply elem_of_singleton. reflexivity.
Qed.

Local Lemma wand_open_world_tapp_apps_scope
    (Σ : lty_env) τx τr e1 e2 (m my : WfWorldT) y :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  fv_tm (tapp_tm e1 (vfvar y)) ∪
  fv_tm (tapp_tm e2 (vfvar y)) ⊆ world_dom (my : WorldT).
Proof.
  intros Hequiv Hdom a Ha.
  apply elem_of_union in Ha as [Ha|Ha];
    rewrite fv_tapp_tm in Ha; cbn [fv_value] in Ha;
    apply elem_of_union in Ha as [Ha|Ha].
  - eapply wand_open_world_term_scope; [exact Hequiv|exact Hdom|].
    apply elem_of_union_l. exact Ha.
  - apply elem_of_singleton in Ha. subst a.
    rewrite Hdom. apply elem_of_union_r. apply elem_of_singleton. reflexivity.
  - eapply wand_open_world_term_scope; [exact Hequiv|exact Hdom|].
    apply elem_of_union_r. exact Ha.
  - apply elem_of_singleton in Ha. subst a.
    rewrite Hdom. apply elem_of_union_r. apply elem_of_singleton. reflexivity.
Qed.

Local Lemma wand_product_tapp_apps_scope
    (Σ : lty_env) τx τr e1 e2 (m n : WfWorldT)
    y (Hc : world_compat n m) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  y ∈ world_dom (n : WorldT) ->
  fv_tm (tapp_tm e1 (vfvar y)) ∪
  fv_tm (tapp_tm e2 (vfvar y)) ⊆
  world_dom (res_product n m Hc : WorldT).
Proof.
  intros Hequiv Hy a Ha.
  pose proof (raw_le_dom (n : WorldT)
    (res_product n m Hc : WorldT)
    (res_product_le_l n m Hc)) as Hdom_l.
  pose proof (raw_le_dom (m : WorldT)
    (res_product n m Hc : WorldT)
    (res_product_le_r n m Hc)) as Hdom_r.
  apply elem_of_union in Ha as [Ha|Ha];
    rewrite fv_tapp_tm in Ha; cbn [fv_value] in Ha;
    apply elem_of_union in Ha as [Ha|Ha].
  - apply Hdom_r.
    eapply typed_total_equiv_term_scope; [exact Hequiv|].
    apply elem_of_union_l. exact Ha.
  - apply elem_of_singleton in Ha. subst a. apply Hdom_l. exact Hy.
  - apply Hdom_r.
    eapply typed_total_equiv_term_scope; [exact Hequiv|].
    apply elem_of_union_r. exact Ha.
  - apply elem_of_singleton in Ha. subst a. apply Hdom_l. exact Hy.
Qed.

Local Lemma wand_tapp_apps_fv_subset e1 e2 y :
  fv_tm (tapp_tm e1 (vfvar y)) ∪
  fv_tm (tapp_tm e2 (vfvar y)) ⊆
  (fv_tm e1 ∪ fv_tm e2) ∪ ({[y]} : aset).
Proof.
  intros a Ha.
  apply elem_of_union in Ha as [Ha|Ha];
    rewrite fv_tapp_tm in Ha; cbn [fv_value] in Ha;
    apply elem_of_union in Ha as [Ha|Ha].
  - apply elem_of_union_l. apply elem_of_union_l. exact Ha.
  - apply elem_of_singleton in Ha. subst a.
    apply elem_of_union_r. apply elem_of_singleton. reflexivity.
  - apply elem_of_union_l. apply elem_of_union_r. exact Ha.
  - apply elem_of_singleton in Ha. subst a.
    apply elem_of_union_r. apply elem_of_singleton. reflexivity.
Qed.

Lemma wand_open_arg_to_inserted_env
    gas (Σ : lty_env) τx τr e
    (m : WfWorldT) y :
  lty_env_closed Σ ->
	  LVFree y ∉ dom Σ ->
	  y ∉ fv_cty τx ->
	  lc_context_ty τx ->
	  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e) (erase_ty τx))) ->
  m ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
	  m ⊨ ty_denote_gas gas
	    (<[LVFree y := erase_ty τx]> Σ)
	    τx (tret (vfvar y)).
Proof.
  intros HΣclosed HfreshΣ Hyτx Hτx_lc Hfresh_arg Harg.
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  assert (Hea_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. better_set_solver. }
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Harg
    by (exact Hfresh_arg || exact Hea_fresh || exact Hτa_fresh).
  change (open_tm 0 (vfvar y) (tret (vbvar 0)))
    with (tret (vfvar y)) in Harg.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))
    (relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y)))
    ltac:(better_set_solver)
    (wand_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e Hyτx)) as Hagree.
  rewrite Hagree in Harg.
	  rewrite typed_lty_env_bind_open_current in Harg
	    by (exact HfreshΣ || exact HΣclosed).
	  rewrite cty_open_shift_from_lc_fresh in Harg.
	  - exact Harg.
	  - exact Hτx_lc.
	  - exact Hyτx.
Qed.

Lemma wand_open_arg_to_inserted_env_normalized
    gas (Σ : lty_env) τx τr e
    (m : WfWorldT) y :
  lty_env_closed Σ ->
  LVFree y ∉ dom Σ ->
  y ∉ fv_cty τx ->
  lc_context_ty τx ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e) (erase_ty τx))) ->
  m ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    τx (tret (vfvar y)).
Proof.
  intros HΣclosed HfreshΣ Hyτx Hlc Hfresh_arg Harg.
  eapply wand_open_arg_to_inserted_env; eauto.
Qed.

Lemma ty_denote_gas_tm_equiv_wand_open_arg
    gas (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
	  y ∉ fv_cty τx ->
	  lc_context_ty τx ->
	  lty_env_closed (relevant_env Σ (CTWand τx τr) e1) ->
	  lty_env_closed (relevant_env Σ (CTWand τx τr) e2) ->
	  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))) ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  n ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    τx (tret (vfvar y)) ->
  n ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e1))
    τx (tret (vfvar y)).
Proof.
  intros _ _ _ Hyτx Hτx_lc Hrel1_closed Hrel2_closed HyΣ1 HyΣ2 Htgt.
  assert (Hyrel1 : LVFree y ∉ dom (relevant_env Σ (CTWand τx τr) e1 : lty_env)).
  {
    intros Hbad. apply HyΣ1. apply lvars_fv_elem.
    rewrite typed_lty_env_bind_dom.
    rewrite (lvars_shift_from_lc_eq 0
      (dom (relevant_env Σ (CTWand τx τr) e1)) Hrel1_closed).
    apply elem_of_union_l. exact Hbad.
  }
  assert (Hyrel2 : LVFree y ∉ dom (relevant_env Σ (CTWand τx τr) e2 : lty_env)).
  {
    intros Hbad. apply HyΣ2. apply lvars_fv_elem.
    rewrite typed_lty_env_bind_dom.
    rewrite (lvars_shift_from_lc_eq 0
      (dom (relevant_env Σ (CTWand τx τr) e2)) Hrel2_closed).
    apply elem_of_union_l. exact Hbad.
  }
  assert (Htgt_raw :
      n ⊨ formula_open 0 y
        (ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e2)
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0)))).
  {
    rewrite (formula_open_ty_denote_gas_singleton 0 y gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))).
    2:{ exact HyΣ2. }
    2:{ cbn [fv_tm fv_value]. set_solver. }
    2:{ rewrite cty_shift_fv. exact Hyτx. }
    change (open_tm 0 (vfvar y) (tret (vbvar 0)))
      with (tret (vfvar y)).
    rewrite typed_lty_env_bind_open_current
      by (exact Hyrel2 || exact Hrel2_closed).
    rewrite cty_open_shift_from_lc_fresh
      by (exact Hτx_lc || exact Hyτx).
    exact Htgt.
  }
  assert (Hsrc_raw :
      n ⊨ formula_open 0 y
        (ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e1)
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0)))).
  {
  set (τa := cty_open 0 y (cty_shift 0 τx)).
  set (ea := tret (vfvar y)).
    rewrite (formula_open_ty_denote_gas_singleton 0 y gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))).
    2:{ exact HyΣ1. }
    2:{ cbn [fv_tm fv_value]. set_solver. }
    2:{ rewrite cty_shift_fv. exact Hyτx. }
    change (open_tm 0 (vfvar y) (tret (vbvar 0)))
      with (tret (vfvar y)).
    rewrite (formula_open_ty_denote_gas_singleton 0 y gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) in Htgt_raw.
    2:{ exact HyΣ2. }
    2:{ cbn [fv_tm fv_value]. set_solver. }
    2:{ rewrite cty_shift_fv. exact Hyτx. }
    change (open_tm 0 (vfvar y) (tret (vbvar 0)))
      with (tret (vfvar y)) in Htgt_raw.
    fold τa ea in Htgt_raw |- *.
	  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    τa ea (relevant_lvars τa ea)
    ltac:(set_solver)
    (wand_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e1 Hyτx)) as Hsrc_mid.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    τa ea (relevant_lvars τa ea)
    ltac:(set_solver)
    (wand_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e2 Hyτx)) as Htgt_mid.
	  rewrite Hsrc_mid.
	  rewrite Htgt_mid in Htgt_raw.
	  exact Htgt_raw.
  }
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Hsrc_raw.
  2:{ exact HyΣ1. }
  2:{ cbn [fv_tm fv_value]. set_solver. }
  2:{ rewrite cty_shift_fv. exact Hyτx. }
  change (open_tm 0 (vfvar y) (tret (vbvar 0)))
    with (tret (vfvar y)) in Hsrc_raw.
  rewrite typed_lty_env_bind_open_current in Hsrc_raw
    by (exact Hyrel1 || exact Hrel1_closed).
  rewrite cty_open_shift_from_lc_fresh in Hsrc_raw
    by (exact Hτx_lc || exact Hyτx).
  exact Hsrc_raw.
Qed.

Lemma ty_denote_gas_tm_equiv_wand_open_arg_fbwand
    gas (Σ : lty_env) τx τr e1 e2
    (m n : WfWorldT) y :
	  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
	  y ∉ fv_cty τx ->
	  lc_context_ty τx ->
	  lty_env_closed (relevant_env Σ (CTWand τx τr) e1) ->
	  lty_env_closed (relevant_env Σ (CTWand τx τr) e2) ->
	  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))) ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  n ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    τx (tret (vfvar y)) ->
  n ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e1))
    τx (tret (vfvar y)).
Proof.
  intros _ Hyτx Hτx_lc Hrel1_closed Hrel2_closed HyΣ1 HyΣ2 Htgt.
  assert (Hyrel1 : LVFree y ∉ dom (relevant_env Σ (CTWand τx τr) e1 : lty_env)).
  {
    intros Hbad. apply HyΣ1. apply lvars_fv_elem.
    rewrite typed_lty_env_bind_dom.
    rewrite (lvars_shift_from_lc_eq 0
      (dom (relevant_env Σ (CTWand τx τr) e1)) Hrel1_closed).
    apply elem_of_union_l. exact Hbad.
  }
  assert (Hyrel2 : LVFree y ∉ dom (relevant_env Σ (CTWand τx τr) e2 : lty_env)).
  {
    intros Hbad. apply HyΣ2. apply lvars_fv_elem.
    rewrite typed_lty_env_bind_dom.
    rewrite (lvars_shift_from_lc_eq 0
      (dom (relevant_env Σ (CTWand τx τr) e2)) Hrel2_closed).
    apply elem_of_union_l. exact Hbad.
  }
  assert (Htgt_raw :
      n ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e2)
            (erase_ty τx)))
        (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))).
  {
    rewrite typed_lty_env_bind_open_current
      by (exact Hyrel2 || exact Hrel2_closed).
    rewrite cty_open_shift_from_lc_fresh
      by (exact Hτx_lc || exact Hyτx).
    exact Htgt.
  }
  assert (Hsrc_raw :
      n ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e1)
            (erase_ty τx)))
        (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))).
  {
  set (τa := cty_open 0 y (cty_shift 0 τx)).
  set (ea := tret (vfvar y)).
    fold τa ea in Htgt_raw |- *.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    τa ea (relevant_lvars τa ea)
    ltac:(set_solver)
    (wand_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e1 Hyτx)) as Hsrc_mid.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    τa ea (relevant_lvars τa ea)
    ltac:(set_solver)
    (wand_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e2 Hyτx)) as Htgt_mid.
  rewrite Hsrc_mid.
  rewrite Htgt_mid in Htgt_raw.
  exact Htgt_raw.
  }
  rewrite typed_lty_env_bind_open_current in Hsrc_raw
    by (exact Hyrel1 || exact Hrel1_closed).
  rewrite cty_open_shift_from_lc_fresh in Hsrc_raw
    by (exact Hτx_lc || exact Hyτx).
  exact Hsrc_raw.
Qed.

Lemma ty_equiv_wand_result_src_mid
    gas (Σ : lty_env) τx τr e1
    (m : WfWorldT) y :
  lc_tm e1 ->
  y ∉ fv_cty τr ->
  m ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e1)
        (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  m ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)).
Proof.
  intros Hlc Hyτr Hsrc.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e1)
        (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y))
    (relevant_lvars (cty_open 0 y τr)
      (tapp_tm e1 (vfvar y)))
    ltac:(set_solver)
    (wand_body_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e1 (tapp_tm e1 (vfvar y))
      Hyτr (tm_lvars_tapp_tm_fvar_without_arg_shift_lc e1 y Hlc)))
    as Hagree.
  rewrite <- Hagree.
  exact Hsrc.
Qed.

Lemma ty_equiv_wand_result_src_mid_inserted
    gas (Σ : lty_env) τx τr e1
    (m : WfWorldT) y :
  lty_env_closed Σ ->
  LVFree y ∉ dom Σ ->
  LVFree y ∉ dom (relevant_env Σ (CTWand τx τr) e1 : lty_env) ->
  lc_tm e1 ->
  y ∉ fv_cty τr ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e1))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)).
Proof.
  intros HΣclosed HyΣ Hyrel Hlc Hyτr Hsrc.
  assert (Hsrc_open :
      m ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e1)
            (erase_ty τx)))
        (cty_open 0 y τr) (tapp_tm e1 (vfvar y))).
  {
    rewrite typed_lty_env_bind_open_current.
    - exact Hsrc.
    - exact Hyrel.
    - apply relevant_env_closed. exact HΣclosed.
  }
  pose proof (ty_equiv_wand_result_src_mid
    gas Σ τx τr e1 m y Hlc Hyτr Hsrc_open) as Hmid.
  rewrite typed_lty_env_bind_open_current in Hmid
    by (exact HyΣ || exact HΣclosed).
  exact Hmid.
Qed.

Lemma ty_equiv_wand_result_tgt_goal
    gas (Σ : lty_env) τx τr e2
    (m : WfWorldT) y :
  lc_tm e2 ->
  y ∉ fv_cty τr ->
  m ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) ->
  m ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hlc Hyτr Hmid.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y))
    (relevant_lvars (cty_open 0 y τr)
      (tapp_tm e2 (vfvar y)))
    ltac:(set_solver)
    (wand_body_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e2 (tapp_tm e2 (vfvar y))
      Hyτr (tm_lvars_tapp_tm_fvar_without_arg_shift_lc e2 y Hlc)))
    as Hagree.
  rewrite Hagree.
  exact Hmid.
Qed.

Lemma wfworld_closed_on_wand_open_result_apps
    (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)) ->
  wfworld_closed_on
    (fv_tm (tapp_tm e1 (vfvar y)) ∪
     fv_tm (tapp_tm e2 (vfvar y)))
    (res_product n my Hc).
Proof.
  intros Hequiv Hdom Hrestrict Hworld.
  pose proof (typed_total_equiv_source_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero1.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero2.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e1 m Hzero1) as Hguard1.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero2) as Hguard2.
  repeat rewrite res_models_and_iff in Hguard1.
  repeat rewrite res_models_and_iff in Hguard2.
  destruct Hguard1 as [_ [Hworld1 [Hbasic1 _]]].
  destruct Hguard2 as [_ [Hworld2 [Hbasic2 _]]].
  assert (Hle : m ⊑ my).
  {
    change (m ⊑ my).
    rewrite <- Hrestrict.
    apply res_restrict_le.
  }
  pose proof (typed_total_equiv_term_scope
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
  assert (Hclosed1 : wfworld_closed_on (fv_tm e1) my).
  {
    eapply wfworld_closed_on_le.
    - intros a Ha. apply Hscope. apply elem_of_union_l. exact Ha.
    - exact Hle.
    - eapply relevant_world_typing_closed_on_term.
      + exact Hworld1.
      + exact Hbasic1.
  }
  assert (Hclosed2 : wfworld_closed_on (fv_tm e2) my).
  {
    eapply wfworld_closed_on_le.
    - intros a Ha. apply Hscope. apply elem_of_union_r. exact Ha.
    - exact Hle.
    - eapply relevant_world_typing_closed_on_term.
      + exact Hworld2.
      + exact Hbasic2.
  }
  assert (Hworld_y :
      my ⊨ basic_world_formula
        (<[LVFree y := erase_ty τx]> (∅ : lty_env))).
	  {
	    change (<[LVBound 0 := erase_ty τx]> (∅ : gmap logic_var ty))
	      with (typed_lty_env_bind (∅ : lty_env) (erase_ty τx)) in Hworld.
	    rewrite formula_open_basic_world_bind0 in Hworld.
	    - exact Hworld.
	    - rewrite dom_empty_L. apply not_elem_of_empty.
	    - exact lty_env_closed_empty.
	  }
  assert (Hclosed_y : wfworld_closed_on ({[y]} : aset) my).
  { eapply basic_world_formula_singleton_free_closed_on. exact Hworld_y. }
  assert (Hclosed_my :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y))) my).
  {
    eapply (wfworld_closed_on_mono _
      ((fv_tm e1 ∪ fv_tm e2) ∪ ({[y]} : aset)) my).
    - apply wand_tapp_apps_fv_subset.
    - apply (wfworld_closed_on_union (fv_tm e1 ∪ fv_tm e2) ({[y]} : aset)).
      + apply (wfworld_closed_on_union (fv_tm e1) (fv_tm e2));
          [exact Hclosed1|exact Hclosed2].
      + exact Hclosed_y.
  }
  eapply wfworld_closed_on_le.
  - eapply wand_open_world_tapp_apps_scope; eauto.
  - apply res_product_le_r.
  - exact Hclosed_my.
Qed.

Lemma wand_result_source_world
    (Σ : lty_env) τx τr e1 e2 (m my : WfWorldT) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ basic_world_formula (relevant_env Σ (CTWand τx τr) e2).
Proof.
  intros Hequiv Hrestrict.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_top_tgt as [_ [Hworld_top_tgt _]].
  assert (Hle : m ⊑ my).
  { rewrite <- Hrestrict. apply res_restrict_le. }
  eapply res_models_kripke; [exact Hle|exact Hworld_top_tgt].
Qed.

Lemma basic_world_formula_wand_open_result_big
    (Σ : lty_env) τx τr e1 e2 (m my : WfWorldT) y :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  my ⊨ basic_world_formula (relevant_env Σ (CTWand τx τr) e2) ->
  my ⊨ basic_world_formula
    ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env) ->
  my ⊨ basic_world_formula
    (relevant_env
      (<[LVFree y := erase_ty τx]>
        (relevant_env Σ (CTWand τx τr) e2))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y))).
Proof.
  intros Hequiv Hyτx Hyτr Hye Hworld_src Hworld_y.
  pose proof Hworld_src as Hworld_src_parts.
  apply basic_world_formula_models_iff in Hworld_src_parts as [Hlc_rel [_ _]].
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_top_tgt as [Hwf_top_tgt _].
  apply context_ty_wf_formula_models_iff in Hwf_top_tgt
    as [_ [_ Hbasic_wand]].
  eapply wand_body_world_from_source_arg.
  - exact Hlc_rel.
  - eapply relevant_env_wand_fresh_free.
    + exact Hyτx.
    + exact Hyτr.
    + set_solver.
  - exact Hbasic_wand.
  - apply tm_lvars_tapp_tm_fvar_without_arg.
  - rewrite relevant_env_idemp. exact Hworld_src.
  - exact Hworld_y.
Qed.

Lemma basic_world_formula_wand_open_result_subenv
    (Σ : lty_env) τx τr e1 e2 (m : WfWorldT) y :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  forall v T,
    relevant_env
      (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) !! v = Some T ->
    relevant_env
      (<[LVFree y := erase_ty τx]>
        (relevant_env Σ (CTWand τx τr) e2))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) !! v = Some T.
Proof.
  intros Hequiv Hyτx Hyτr Hye v T Hlook.
  pose proof (typed_total_equiv_term_lc
    Σ (CTWand τx τr) m e1 e2 Hequiv) as [_ Hlc2].
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_top_tgt as [Hwf_top_tgt _].
  apply context_ty_wf_formula_models_iff in Hwf_top_tgt
    as [Hlc_rel _].
  assert (Hy_rel :
      LVFree y ∉ dom (relevant_env Σ (CTWand τx τr) e2 : lty_env)).
  {
    eapply relevant_env_wand_fresh_free.
    - exact Hyτx.
    - exact Hyτr.
    - set_solver.
  }
  pose proof (wand_body_relevant_env_agree_open_one_core
    Σ (erase_ty τx) y τx τr e2 (tapp_tm e2 (vfvar y))
    Hyτr (tm_lvars_tapp_tm_fvar_without_arg_shift_lc e2 y Hlc2)) as Hagree.
  change ((lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (relevant_lvars (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
    : lty_env) !! v = Some T) in Hlook.
  rewrite <- Hagree in Hlook.
  rewrite typed_lty_env_bind_open_current in Hlook by
    (exact Hy_rel || exact Hlc_rel).
  change ((lty_env_restrict_lvars
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    (relevant_lvars (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
    : lty_env) !! v = Some T).
  exact Hlook.
Qed.

Lemma basic_world_formula_wand_open_result_target
    gas (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)) ->
  res_product n my Hc ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  n ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  res_product n my Hc ⊨ basic_world_formula
    (relevant_env
      (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y))).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hworld Hres_mid Harg.
  pose proof (wand_result_source_world
    Σ τx τr e1 e2 m my Hequiv Hrestrict) as Hworld_src_my.
  assert (Hworld_src_prod :
      res_product n my Hc ⊨
        basic_world_formula (relevant_env Σ (CTWand τx τr) e2)).
  { eapply res_models_kripke; [apply res_product_le_r|exact Hworld_src_my]. }
  pose proof (basic_world_formula_opened_arg_world (erase_ty τx) my y Hworld)
    as Hworld_y_my.
  assert (Hworld_y_prod :
      res_product n my Hc ⊨ basic_world_formula
        ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env)).
  { eapply res_models_kripke; [apply res_product_le_r|exact Hworld_y_my]. }
  pose proof (basic_world_formula_wand_open_result_big
    Σ τx τr e1 e2 m (res_product n my Hc) y
    Hequiv Hyτx Hyτr Hye Hworld_src_prod Hworld_y_prod) as Hworld_big.
  eapply basic_world_formula_subenv; [|exact Hworld_big].
  eapply basic_world_formula_wand_open_result_subenv; eauto.
Qed.

Lemma wand_result_target_typing
    gas (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)) ->
  res_product n my Hc ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  n ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  res_product n my Hc ⊨ expr_basic_typing_formula
    (relevant_env
      (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
    (tapp_tm e2 (vfvar y)) (erase_ty (cty_open 0 y τr)).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hworld Hres_mid Harg.
  pose proof (basic_world_formula_wand_open_result_target
    gas Σ τx τr e1 e2 m my n y Hc Hequiv Hdom Hrestrict
    Hyτx Hyτr Hye Hworld Hres_mid Harg) as Hworld_tgt.
  apply expr_basic_typing_formula_models_iff.
  apply basic_world_formula_models_iff in Hworld_tgt
    as [Hlc_tgt [Hscope_tgt _]].
  split; [exact Hlc_tgt|].
  split; [exact Hscope_tgt|].
  rewrite cty_open_preserves_erasure.
  eapply basic_tm_has_ltype_tapp_tm_lvar.
  - exact Hlc_tgt.
  - eapply (basic_tm_has_ltype_open_result_target_fun
      Σ (CTWand τx τr) τx τr e1 e2 m y); eauto.
  - apply basic_value_has_ltype_open_result_target_arg.
Qed.

Lemma ty_denote_gas_zero_wand_open_result_target
    gas (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)) ->
  res_product n my Hc ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  n ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  res_product n my Hc ⊨ ty_denote_gas 0
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hworld Hres_mid Harg.
  pose proof (ty_denote_gas_guard gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y))
    (res_product n my Hc) Hres_mid) as Hguard_res_src.
  pose proof (ty_denote_gas_guard gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) n Harg)
    as Hguard_arg.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  repeat rewrite res_models_and_iff in Hguard_res_src.
  repeat rewrite res_models_and_iff in Hguard_arg.
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_res_src as [Hwf_res_src [Hworld_res_src
    [Hbasic_res_src Htotal_res_src]]].
  destruct Hguard_arg as [Hwf_arg [Hworld_arg [Hbasic_arg Htotal_arg]]].
  destruct Hguard_top_tgt as [Hwf_top_tgt [Hworld_top_tgt
    [Hbasic_top_tgt Htotal_top_tgt]]].
  assert (Hclosed_apps :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y)))
        (res_product n my Hc)).
  {
    eapply wfworld_closed_on_wand_open_result_apps; eauto.
  }
  assert (Heq_apps :
      tm_equiv_on (res_product n my Hc)
        (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y))).
  {
    pose proof (typed_total_equiv_term_lc
      Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
    eapply tm_equiv_tapp_fvar.
    - exact Hclosed_apps.
    - exact Hlc1.
    - exact Hlc2.
    - eapply tm_equiv_res_product_right.
      + pose proof (typed_total_equiv_term_scope
          Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
        destruct Hequiv as [Heq_base _].
        eapply tm_equiv_full_world_extend_fresh.
        * exact Heq_base.
        * exact Hscope.
        * exact Hye.
        * exact Hdom.
        * exact Hrestrict.
      + pose proof (typed_total_equiv_term_scope
          Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
        eapply wand_open_world_term_scope; eauto.
  }
  assert (Htotal_tgt :
      res_product n my Hc ⊨ expr_total_formula (tapp_tm e2 (vfvar y))).
  {
    pose proof (typed_total_equiv_term_lc
      Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
    pose proof (typed_total_equiv_term_scope
      Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
    assert (Htotal_base_my : tm_total_equiv_on my e1 e2).
    {
      eapply tm_total_equiv_full_world_extend_fresh.
      - eapply typed_total_equiv_total_equiv. exact Hequiv.
      - exact Hlc1.
      - exact Hlc2.
      - exact Hscope.
      - exact Hye.
      - exact Hdom.
      - exact Hrestrict.
    }
    assert (Htotal_base_product :
        tm_total_equiv_on (res_product n my Hc) e1 e2).
    {
      eapply tm_total_equiv_res_product_right.
      - exact Htotal_base_my.
      - exact Hlc1.
      - exact Hlc2.
      - eapply wand_open_world_term_scope; eauto.
    }
    assert (Heq_base_product :
        tm_equiv_on (res_product n my Hc) e1 e2).
    {
      eapply tm_equiv_res_product_right.
      - eapply tm_equiv_full_world_extend_fresh.
        + eapply typed_total_equiv_tm_equiv. exact Hequiv.
        + exact Hscope.
        + exact Hye.
        + exact Hdom.
        + exact Hrestrict.
      - eapply wand_open_world_term_scope; eauto.
    }
    assert (Htotal_apps :
        tm_total_equiv_on (res_product n my Hc)
          (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y))).
    {
      eapply tm_total_equiv_tapp_fvar.
      - exact Hclosed_apps.
      - exact Hlc1.
      - exact Hlc2.
      - exact Heq_base_product.
      - exact Htotal_base_product.
    }
    eapply tm_equiv_total.
    - exact Htotal_apps.
    - apply lc_tapp_tm; [exact Hlc2|constructor].
    - eapply wand_open_product_tapp_tgt_scope; eauto.
    - exact Htotal_res_src.
  }
  assert (Hworld_tgt :
      res_product n my Hc ⊨ basic_world_formula
        (relevant_env
          (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
          (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))).
  {
    eapply basic_world_formula_wand_open_result_target; eauto.
  }
  assert (Hwf_tgt :
      res_product n my Hc ⊨ context_ty_wf_formula
        (relevant_env
          (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
          (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
        (cty_open 0 y τr)).
  {
    eapply context_ty_wf_formula_relevant_env_change_term.
    - exact Hworld_tgt.
    - exact Hwf_res_src.
  }
  assert (Hbasic_tgt :
      res_product n my Hc ⊨ expr_basic_typing_formula
        (relevant_env
          (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
          (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
        (tapp_tm e2 (vfvar y)) (erase_ty (cty_open 0 y τr))).
  {
    eapply wand_result_target_typing; eauto.
  }
  apply ty_denote_gas_zero_of_guard.
  repeat rewrite res_models_and_iff.
  split.
  - exact Hwf_tgt.
  - split.
    + exact Hworld_tgt.
    + split.
      * exact Hbasic_tgt.
      * exact Htotal_tgt.
Qed.

Lemma typed_total_equiv_wand_open_result_mid
    gas (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)) ->
  res_product n my Hc ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  n ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  typed_total_equiv_on
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (res_product n my Hc)
    (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hworld Hres_mid Harg.
  pose proof (typed_total_equiv_term_lc
    Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  assert (Hclosed_apps :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y)))
        (res_product n my Hc)).
  {
    eapply (wfworld_closed_on_wand_open_result_apps
      Σ τx τr e1 e2 m my n y Hc); eauto.
  }
  pose proof (typed_total_equiv_term_scope
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
  assert (Heq_base_product :
      tm_equiv_on (res_product n my Hc) e1 e2).
  {
    eapply tm_equiv_res_product_right.
    - eapply tm_equiv_full_world_extend_fresh.
      + eapply typed_total_equiv_tm_equiv. exact Hequiv.
      + exact Hscope.
      + exact Hye.
      + exact Hdom.
      + exact Hrestrict.
    - eapply wand_open_world_term_scope; eauto.
  }
  assert (Htotal_base_my : tm_total_equiv_on my e1 e2).
  {
    eapply tm_total_equiv_full_world_extend_fresh.
    - eapply typed_total_equiv_total_equiv. exact Hequiv.
    - exact Hlc1.
    - exact Hlc2.
    - exact Hscope.
    - exact Hye.
    - exact Hdom.
    - exact Hrestrict.
  }
  assert (Htotal_base_product :
      tm_total_equiv_on (res_product n my Hc) e1 e2).
  {
    eapply tm_total_equiv_res_product_right.
    - exact Htotal_base_my.
    - exact Hlc1.
    - exact Hlc2.
    - eapply wand_open_world_term_scope; eauto.
  }
  split.
  - eapply tm_equiv_tapp_fvar.
    + exact Hclosed_apps.
    + exact Hlc1.
    + exact Hlc2.
    + exact Heq_base_product.
  - split.
    + eapply tm_total_equiv_tapp_fvar.
      * exact Hclosed_apps.
      * exact Hlc1.
      * exact Hlc2.
      * exact Heq_base_product.
      * exact Htotal_base_product.
    + split.
      * apply ty_denote_gas_zero_of_guard.
        eapply ty_denote_gas_guard. exact Hres_mid.
      * eapply (ty_denote_gas_zero_wand_open_result_target
        gas Σ τx τr e1 e2 m my n y Hc); eauto.
Qed.

Lemma ty_denote_gas_tm_equiv_wand_open_result
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))) ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)) ->
  n ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  res_product n my Hc ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e1)
        (erase_ty τx))
      τr (tapp_tm (tm_shift 0 e1) (vbvar 0))) ->
  res_product n my Hc ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx))
      τr (tapp_tm (tm_shift 0 e2) (vbvar 0))).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye HyΣ1 HyΣ2 Hworld Harg Hres.
  pose proof (typed_total_equiv_term_lc
    Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  assert (Harg_tm_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. set_solver. }
	  assert (Hsrc_tm_fresh :
	      y ∉ fv_tm (tapp_tm (tm_shift 0 e1) (vbvar 0))).
	  {
	    rewrite fv_tapp_tm, tm_shift_fv.
	    cbn [fv_value].
	    intros Hy.
	    apply elem_of_union in Hy as [Hy|Hy].
	    - apply Hye. apply elem_of_union_l. exact Hy.
	    - apply not_elem_of_empty in Hy. contradiction.
	  }
	  assert (Htgt_tm_fresh :
	      y ∉ fv_tm (tapp_tm (tm_shift 0 e2) (vbvar 0))).
	  {
	    rewrite fv_tapp_tm, tm_shift_fv.
	    cbn [fv_value].
	    intros Hy.
	    apply elem_of_union in Hy as [Hy|Hy].
	    - apply Hye. apply elem_of_union_r. exact Hy.
	    - apply not_elem_of_empty in Hy. contradiction.
	  }
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))
    τr (tapp_tm (tm_shift 0 e1) (vbvar 0))) in Hres
    by (exact HyΣ1 || exact Hsrc_tm_fresh || exact Hyτr).
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))
    τr (tapp_tm (tm_shift 0 e2) (vbvar 0)))
    by (exact HyΣ2 || exact Htgt_tm_fresh || exact Hyτr).
  rewrite open_tapp_tm_shift_bvar0_lc in Hres by exact Hlc1.
  rewrite open_tapp_tm_shift_bvar0_lc by exact Hlc2.
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Harg
    by (exact HyΣ2 || exact Harg_tm_fresh || exact Hτa_fresh).
  replace (open_tm 0 (vfvar y) (tret (vbvar 0))) with
      (tret (vfvar y)) in Harg
    by (cbn [open_tm open_value]; rewrite decide_True by lia; reflexivity).
  set (τres := cty_open 0 y τr).
  set (esrc := tapp_tm e1 (vfvar y)).
  set (etgt := tapp_tm e2 (vfvar y)).
  fold τres esrc etgt in Hres |- *.
  assert (Hres_mid :
      res_product n my Hc ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
        τres esrc).
  {
    unfold τres, esrc.
    eapply ty_equiv_wand_result_src_mid;
      eauto.
  }
  assert (Htgt_mid_to_goal :
      res_product n my Hc ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
        τres etgt ->
      res_product n my Hc ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e2)
            (erase_ty τx)))
        τres etgt).
  {
    unfold τres, etgt.
    eapply ty_equiv_wand_result_tgt_goal;
      eauto.
  }
  apply Htgt_mid_to_goal.
  eapply IH.
  - unfold τres, esrc, etgt in *.
    eapply typed_total_equiv_wand_open_result_mid; eauto.
  - exact Hres_mid.
Qed.

Lemma wfworld_closed_on_wand_open_result_apps_product
    gas (Σ : lty_env) τx τr e1 e2
    (m n : WfWorldT) y (Hc : world_compat n m) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  y ∉ fv_cty τx ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  n ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  wfworld_closed_on
    (fv_tm (tapp_tm e1 (vfvar y)) ∪
     fv_tm (tapp_tm e2 (vfvar y)))
    (res_product n m Hc).
Proof.
  intros Hequiv Hyτx Hye HyΣ2 Harg.
  pose proof (typed_total_equiv_source_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero1.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero2.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e1 m Hzero1) as Hguard1.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero2) as Hguard2.
  repeat rewrite res_models_and_iff in Hguard1.
  repeat rewrite res_models_and_iff in Hguard2.
  destruct Hguard1 as [_ [Hworld1 [Hbasic1 _]]].
  destruct Hguard2 as [_ [Hworld2 [Hbasic2 _]]].
  pose proof (typed_total_equiv_term_scope
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
  assert (Hclosed1 : wfworld_closed_on (fv_tm e1) m).
  {
    eapply relevant_world_typing_closed_on_term.
    - exact Hworld1.
    - exact Hbasic1.
  }
  assert (Hclosed2 : wfworld_closed_on (fv_tm e2) m).
  {
    eapply relevant_world_typing_closed_on_term.
    - exact Hworld2.
    - exact Hbasic2.
  }
  assert (Hclosed_fun :
      wfworld_closed_on (fv_tm e1 ∪ fv_tm e2) (res_product n m Hc)).
  {
    eapply wfworld_closed_on_le.
    - intros a Ha. apply Hscope. exact Ha.
    - apply res_product_le_r.
    - apply (wfworld_closed_on_union (fv_tm e1) (fv_tm e2));
        [exact Hclosed1|exact Hclosed2].
  }
  assert (Hworld_y_open :
      n ⊨ formula_open 0 y
        (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))).
  {
    eapply basic_world_formula_opened_arg_from_denotation; eauto.
	  }
	  pose proof (basic_world_formula_opened_arg_world
	    (erase_ty τx) n y Hworld_y_open) as Hworld_y.
	  assert (Hy_n : ({[y]} : aset) ⊆ world_dom (n : WorldT)).
	  {
	    apply basic_world_formula_models_iff in Hworld_y as [_ [Hdom_y _]].
	    rewrite dom_insert_L, dom_empty_L in Hdom_y.
	    rewrite lvars_fv_union, lvars_fv_empty,
	      lvars_fv_singleton_free in Hdom_y.
	    intros a Ha. apply Hdom_y.
	    apply elem_of_union_l. exact Ha.
	  }
	  assert (Hclosed_y :
	      wfworld_closed_on ({[y]} : aset) (res_product n m Hc)).
	  {
	    eapply wfworld_closed_on_le.
	    - exact Hy_n.
	    - apply res_product_le_l.
	    - eapply basic_world_formula_singleton_free_closed_on.
	      eapply basic_world_formula_opened_arg_world.
	      exact Hworld_y_open.
	  }
  eapply (wfworld_closed_on_mono _
    ((fv_tm e1 ∪ fv_tm e2) ∪ ({[y]} : aset))).
  - apply wand_tapp_apps_fv_subset.
  - apply (wfworld_closed_on_union (fv_tm e1 ∪ fv_tm e2)
      ({[y]} : aset)); [exact Hclosed_fun|exact Hclosed_y].
Qed.

Lemma basic_world_formula_wand_open_result_target_product
    gas (Σ : lty_env) τx τr e1 e2
    (m n : WfWorldT) y (Hc : world_compat n m) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  res_product n m Hc ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  n ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  res_product n m Hc ⊨ basic_world_formula
    (relevant_env
      (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y))).
Proof.
  intros Hequiv Hyτx Hyτr Hye HyΣ2 Hres_mid Harg.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_top_tgt as [_ [Hworld_top_tgt _]].
  assert (Hworld_src_prod :
      res_product n m Hc ⊨
        basic_world_formula (relevant_env Σ (CTWand τx τr) e2)).
  { eapply res_models_kripke; [apply res_product_le_r|exact Hworld_top_tgt]. }
  assert (Hworld_y_open :
      n ⊨ formula_open 0 y
        (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))).
  {
    eapply basic_world_formula_opened_arg_from_denotation; eauto.
  }
  pose proof (basic_world_formula_opened_arg_world
    (erase_ty τx) n y Hworld_y_open) as Hworld_y_n.
  assert (Hworld_y_prod :
      res_product n m Hc ⊨ basic_world_formula
        ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env)).
  { eapply res_models_kripke; [apply res_product_le_l|exact Hworld_y_n]. }
  pose proof (basic_world_formula_wand_open_result_big
    Σ τx τr e1 e2 m (res_product n m Hc) y
    Hequiv Hyτx Hyτr Hye Hworld_src_prod Hworld_y_prod) as Hworld_big.
  eapply basic_world_formula_subenv; [|exact Hworld_big].
  eapply basic_world_formula_wand_open_result_subenv; eauto.
Qed.

Lemma ty_denote_gas_zero_wand_open_result_target_product
    gas (Σ : lty_env) τx τr e1 e2
    (m n : WfWorldT) y (Hc : world_compat n m) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  res_product n m Hc ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  n ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  res_product n m Hc ⊨ ty_denote_gas 0
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hyτx Hyτr Hye HyΣ2 Hres_mid Harg.
  pose proof (ty_denote_gas_guard gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y))
    (res_product n m Hc) Hres_mid) as Hguard_res_src.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  repeat rewrite res_models_and_iff in Hguard_res_src.
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_res_src as [Hwf_res_src [Hworld_res_src
    [Hbasic_res_src Htotal_res_src]]].
  destruct Hguard_top_tgt as [Hwf_top_tgt [Hworld_top_tgt
    [Hbasic_top_tgt Htotal_top_tgt]]].
  pose proof (typed_total_equiv_term_lc
    Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  assert (Hclosed_apps :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y)))
        (res_product n m Hc)).
  {
    eapply wfworld_closed_on_wand_open_result_apps_product; eauto.
  }
  assert (Heq_apps :
      tm_equiv_on (res_product n m Hc)
        (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y))).
  {
    eapply tm_equiv_tapp_fvar.
    - exact Hclosed_apps.
    - exact Hlc1.
    - exact Hlc2.
    - eapply tm_equiv_res_product_right.
      + eapply typed_total_equiv_tm_equiv. exact Hequiv.
      + eapply typed_total_equiv_term_scope. exact Hequiv.
  }
  assert (Htotal_base_product :
      tm_total_equiv_on (res_product n m Hc) e1 e2).
  {
    eapply tm_total_equiv_res_product_right.
    - eapply typed_total_equiv_total_equiv. exact Hequiv.
    - exact Hlc1.
    - exact Hlc2.
    - eapply typed_total_equiv_term_scope. exact Hequiv.
  }
  assert (Heq_base_product :
      tm_equiv_on (res_product n m Hc) e1 e2).
  {
    eapply tm_equiv_res_product_right.
    - eapply typed_total_equiv_tm_equiv. exact Hequiv.
    - eapply typed_total_equiv_term_scope. exact Hequiv.
  }
  assert (Htotal_apps :
      tm_total_equiv_on (res_product n m Hc)
        (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y))).
  {
    eapply tm_total_equiv_tapp_fvar.
    - exact Hclosed_apps.
    - exact Hlc1.
    - exact Hlc2.
    - exact Heq_base_product.
    - exact Htotal_base_product.
  }
	  assert (Htotal_tgt :
	      res_product n m Hc ⊨ expr_total_formula (tapp_tm e2 (vfvar y))).
	  {
	    eapply tm_equiv_total.
    - exact Htotal_apps.
    - apply lc_tapp_tm; [exact Hlc2|constructor].
    - rewrite fv_tapp_tm. cbn [fv_value].
      pose proof (typed_total_equiv_term_scope
        Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
      pose proof (raw_le_dom (n : WorldT)
        (res_product n m Hc : WorldT)
        (res_product_le_l n m Hc)) as Hdom_l.
	      pose proof (raw_le_dom (m : WorldT)
	        (res_product n m Hc : WorldT)
	        (res_product_le_r n m Hc)) as Hdom_r.
	      assert (Hy_prod : y ∈ world_dom (res_product n m Hc : WorldT)).
	      {
	        apply Hdom_l.
	        pose proof (basic_world_formula_opened_arg_from_denotation
	          gas
	          (typed_lty_env_bind
	            (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))
	          τx n y Hyτx HyΣ2 Harg) as Hworld_y_open.
	        pose proof (basic_world_formula_opened_arg_world
	          (erase_ty τx) n y Hworld_y_open) as Hworld_y.
		        apply basic_world_formula_models_iff in Hworld_y
		          as [_ [Hdom_y _]].
		        rewrite dom_insert_L, dom_empty_L in Hdom_y.
		        rewrite lvars_fv_union, lvars_fv_empty,
		          lvars_fv_singleton_free in Hdom_y.
		        apply Hdom_y.
		        apply elem_of_union_l. apply elem_of_singleton. reflexivity.
		      }
		      intros a Ha.
		      apply elem_of_union in Ha as [Ha|Ha].
		      + apply Hdom_r. apply Hscope.
		        apply elem_of_union_r. exact Ha.
		      + apply elem_of_singleton in Ha. subst a. exact Hy_prod.
		    - exact Htotal_res_src.
		  }
  assert (Hworld_tgt :
      res_product n m Hc ⊨ basic_world_formula
        (relevant_env
          (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
          (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))).
  {
    eapply basic_world_formula_wand_open_result_target_product; eauto.
  }
  assert (Hwf_tgt :
      res_product n m Hc ⊨ context_ty_wf_formula
        (relevant_env
          (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
          (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
        (cty_open 0 y τr)).
  {
    eapply context_ty_wf_formula_relevant_env_change_term.
    - exact Hworld_tgt.
    - exact Hwf_res_src.
  }
  assert (Hbasic_tgt :
      res_product n m Hc ⊨ expr_basic_typing_formula
        (relevant_env
          (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
          (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
        (tapp_tm e2 (vfvar y)) (erase_ty (cty_open 0 y τr))).
  {
    apply expr_basic_typing_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld_tgt
      as [Hlc_tgt [Hscope_tgt _]].
    split; [exact Hlc_tgt|].
    split; [exact Hscope_tgt|].
    rewrite cty_open_preserves_erasure.
    eapply basic_tm_has_ltype_tapp_tm_lvar.
    - exact Hlc_tgt.
    - eapply (basic_tm_has_ltype_open_result_target_fun
        Σ (CTWand τx τr) τx τr e1 e2 m y); eauto.
    - apply basic_value_has_ltype_open_result_target_arg.
  }
  apply ty_denote_gas_zero_of_guard.
  repeat rewrite res_models_and_iff.
  split.
  - exact Hwf_tgt.
  - split.
    + exact Hworld_tgt.
    + split.
      * exact Hbasic_tgt.
      * exact Htotal_tgt.
Qed.

Lemma typed_total_equiv_wand_open_result_mid_product
    gas (Σ : lty_env) τx τr e1 e2
    (m n : WfWorldT) y (Hc : world_compat n m) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  res_product n m Hc ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  n ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  typed_total_equiv_on
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (res_product n m Hc)
    (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hyτx Hyτr Hye HyΣ2 Hres_mid Harg.
  pose proof (typed_total_equiv_term_lc
    Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  pose proof (typed_total_equiv_term_scope
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
  assert (Hclosed_apps :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y)))
        (res_product n m Hc)).
  {
    eapply wfworld_closed_on_wand_open_result_apps_product; eauto.
  }
  assert (Heq_base_product :
      tm_equiv_on (res_product n m Hc) e1 e2).
  {
    eapply tm_equiv_res_product_right.
    - eapply typed_total_equiv_tm_equiv. exact Hequiv.
    - exact Hscope.
  }
  assert (Htotal_base_product :
      tm_total_equiv_on (res_product n m Hc) e1 e2).
  {
    eapply tm_total_equiv_res_product_right.
    - eapply typed_total_equiv_total_equiv. exact Hequiv.
    - exact Hlc1.
    - exact Hlc2.
    - exact Hscope.
  }
  split.
  - eapply tm_equiv_tapp_fvar.
    + exact Hclosed_apps.
    + exact Hlc1.
    + exact Hlc2.
    + exact Heq_base_product.
  - split.
    + eapply tm_total_equiv_tapp_fvar.
      * exact Hclosed_apps.
      * exact Hlc1.
      * exact Hlc2.
      * exact Heq_base_product.
      * exact Htotal_base_product.
    + split.
      * apply ty_denote_gas_zero_of_guard.
        eapply ty_denote_gas_guard. exact Hres_mid.
      * eapply ty_denote_gas_zero_wand_open_result_target_product; eauto.
Qed.

Lemma ty_denote_gas_tm_equiv_wand_frame_step
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τx τr e1 e2 (m n : WfWorldT)
    (Hc : world_compat n m) y :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))) ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  world_dom (res_product n m Hc : WorldT) =
    world_dom (m : WorldT) ∪ ({[y]} : aset) ->
  n ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  res_product n m Hc ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e1)
        (erase_ty τx))
      τr (tapp_tm (tm_shift 0 e1) (vbvar 0))) ->
  res_product n m Hc ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx))
      τr (tapp_tm (tm_shift 0 e2) (vbvar 0))).
Proof.
  intros Hequiv Hyτx Hyτr Hye HyΣ1 HyΣ2 _Hdom Harg Hres.
  pose proof Harg as Harg_open.
  pose proof (typed_total_equiv_term_lc
    Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
	  assert (Hsrc_tm_fresh :
	      y ∉ fv_tm (tapp_tm (tm_shift 0 e1) (vbvar 0))).
	  {
	    rewrite fv_tapp_tm, tm_shift_fv.
	    cbn [fv_value].
	    intros Hy.
	    apply elem_of_union in Hy as [Hy|Hy].
	    - apply Hye. apply elem_of_union_l. exact Hy.
	    - apply not_elem_of_empty in Hy. contradiction.
	  }
	  assert (Htgt_tm_fresh :
	      y ∉ fv_tm (tapp_tm (tm_shift 0 e2) (vbvar 0))).
	  {
	    rewrite fv_tapp_tm, tm_shift_fv.
	    cbn [fv_value].
	    intros Hy.
	    apply elem_of_union in Hy as [Hy|Hy].
	    - apply Hye. apply elem_of_union_r. exact Hy.
	    - apply not_elem_of_empty in Hy. contradiction.
	  }
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))
    τr (tapp_tm (tm_shift 0 e1) (vbvar 0))) in Hres
    by (exact HyΣ1 || exact Hsrc_tm_fresh || exact Hyτr).
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))
    τr (tapp_tm (tm_shift 0 e2) (vbvar 0)))
    by (exact HyΣ2 || exact Htgt_tm_fresh || exact Hyτr).
  rewrite open_tapp_tm_shift_bvar0_lc in Hres by exact Hlc1.
  rewrite open_tapp_tm_shift_bvar0_lc by exact Hlc2.
  set (τres := cty_open 0 y τr).
  set (esrc := tapp_tm e1 (vfvar y)).
  set (etgt := tapp_tm e2 (vfvar y)).
  fold τres esrc etgt in Hres |- *.
  assert (Hres_mid :
      res_product n m Hc ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
        τres esrc).
  {
    unfold τres, esrc.
    eapply ty_equiv_wand_result_src_mid; eauto.
  }
  assert (Htgt_mid_to_goal :
      res_product n m Hc ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
        τres etgt ->
      res_product n m Hc ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e2)
            (erase_ty τx)))
        τres etgt).
  {
    unfold τres, etgt.
    eapply ty_equiv_wand_result_tgt_goal; eauto.
  }
  apply Htgt_mid_to_goal.
  eapply IH.
  - unfold τres, esrc, etgt in *.
    eapply typed_total_equiv_wand_open_result_mid_product; eauto.
  - exact Hres_mid.
Qed.

End TypeDenote.
