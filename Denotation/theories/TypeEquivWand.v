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

Lemma wand_open_arg_to_inserted_env
    gas (Σ : lty_env) τx τr e
    (m : WfWorldT) y :
  lty_env_closed Σ ->
  LVFree y ∉ dom Σ ->
  y ∉ fv_cty τx ->
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
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)).
Proof.
  intros HΣclosed HfreshΣ Hyτx Hfresh_arg Harg.
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
  exact Harg.
Qed.

Lemma ty_denote_gas_tm_equiv_wand_open_arg
    gas (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))) ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  n ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  n ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e1)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))).
Proof.
  intros _ _ _ Hyτx HyΣ1 HyΣ2 Htgt.
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  assert (Hea_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. set_solver. }
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Htgt
    by (exact HyΣ2 || exact Hea_fresh || exact Hτa_fresh).
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0)))
    by (exact HyΣ1 || exact Hea_fresh || exact Hτa_fresh).
  replace (open_tm 0 (vfvar y) (tret (vbvar 0))) with
      (tret (vfvar y)) in *
    by (cbn [open_tm open_value]; rewrite decide_True by lia; reflexivity).
  set (τa := cty_open 0 y (cty_shift 0 τx)).
  set (ea := tret (vfvar y)).
  fold τa ea in Htgt |- *.
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
  rewrite Htgt_mid in Htgt.
  exact Htgt.
Qed.

Lemma ty_denote_gas_tm_equiv_wand_open_arg_fbwand
    gas (Σ : lty_env) τx τr e1 e2
    (m n : WfWorldT) y :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  y ∉ fv_cty τx ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))) ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  n ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  n ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e1)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))).
Proof.
  intros _ Hyτx HyΣ1 HyΣ2 Htgt.
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  assert (Hea_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. set_solver. }
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Htgt
    by (exact HyΣ2 || exact Hea_fresh || exact Hτa_fresh).
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0)))
    by (exact HyΣ1 || exact Hea_fresh || exact Hτa_fresh).
  replace (open_tm 0 (vfvar y) (tret (vbvar 0))) with
      (tret (vfvar y)) in *
    by (cbn [open_tm open_value]; rewrite decide_True by lia; reflexivity).
  set (τa := cty_open 0 y (cty_shift 0 τx)).
  set (ea := tret (vfvar y)).
  fold τa ea in Htgt |- *.
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
  rewrite Htgt_mid in Htgt.
  exact Htgt.
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
Admitted.

Lemma wand_result_source_world
    (Σ : lty_env) τx τr e1 e2 (m my : WfWorldT) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ basic_world_formula (relevant_env Σ (CTWand τx τr) e2).
Proof.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma ty_denote_gas_tm_equiv_wand_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τx τr e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
	  m ⊨
	    FBWand 1
      (ty_denote_gas gas
        (typed_lty_env_bind
          (relevant_env Σ (CTWand τx τr) e1)
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))
      (ty_denote_gas gas
        (typed_lty_env_bind
          (relevant_env Σ (CTWand τx τr) e1)
          (erase_ty τx))
        τr (tapp_tm (tm_shift 0 e1) (vbvar 0))) ->
  m ⊨
    FBWand 1
      (ty_denote_gas gas
        (typed_lty_env_bind
          (relevant_env Σ (CTWand τx τr) e2)
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))
      (ty_denote_gas gas
	        (typed_lty_env_bind
	          (relevant_env Σ (CTWand τx τr) e2)
	          (erase_ty τx))
	        τr (tapp_tm (tm_shift 0 e2) (vbvar 0))).
Proof.
Admitted.
End TypeDenote.
