(** * ChoiceTyping.TLetReductionFuelSupport

    Fuel-level and model-level reduction lemmas for the [tlet] soundness case.
    The final semantic wrappers stay in [TLetDenotation]. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps StrongNormalization Sugar.
From ChoiceTyping Require Export TLetTotal RegularDenotation.
From ChoiceTyping Require Import Naming ResultWorldBridge ResultWorldFreshForall.
From ChoiceType Require Import BasicStore LocallyNamelessProps DenotationRefinement.

Import Tactics.

(** Resource/totality and [denot_ty_fuel] obligation helpers for the [tlet] reduction proof. *)
Local Lemma dom_insert_inter_fv_tm_fresh
    (Σ : gmap atom ty) T e x :
  x ∉ fv_tm e →
  dom Σ ∩ fv_tm e = dom (<[x := T]> Σ) ∩ fv_tm e.
Proof.
  intros Hx.
  rewrite dom_insert_L.
  apply set_eq. intros z.
  rewrite !elem_of_intersection, elem_of_union, elem_of_singleton.
  split.
  - intros [HzΣ Hze]. split; [right; exact HzΣ | exact Hze].
  - intros [[Hzx | HzΣ] Hze]; [subst; exfalso; eauto |].
    split; [exact HzΣ | exact Hze].
Qed.

Local Lemma dom_insert_inter_fv_tm_fresh_restrict
    (Σ : gmap atom ty) T e x :
  x ∉ dom Σ ∪ fv_tm e →
  fv_tm e ⊆ dom (<[x := T]> Σ) →
  dom Σ ∩ (dom Σ ∩ fv_tm e) = dom (<[x := T]> Σ) ∩ fv_tm e.
Proof.
  intros Hx Hfv.
  rewrite not_elem_of_union in Hx.
  destruct Hx as [HxΣ Hxfv].
  rewrite dom_insert_L.
  apply set_eq. intros z.
  rewrite !elem_of_intersection, elem_of_union, elem_of_singleton.
  split.
  - intros [HzΣ [_ Hzfv]]. split; [right; exact HzΣ | exact Hzfv].
  - intros [[Hzx | HzΣ] Hzfv].
    + subst. exfalso. apply Hxfv. exact Hzfv.
    + split; [exact HzΣ | split; [exact HzΣ | exact Hzfv]].
Qed.

Local Lemma subset_dom_insert_union_singleton
    (Σ : gmap atom ty) T X ν :
  X ⊆ dom Σ ∪ {[ν]} →
  X ⊆ dom (<[ν := T]> Σ) ∪ {[ν]}.
Proof.
  intros HX z Hz.
  apply HX in Hz.
  rewrite dom_insert_L.
  apply elem_of_union in Hz as [HzΣ | Hzν].
  - apply elem_of_union. left. apply elem_of_union. right. exact HzΣ.
  - apply elem_of_union. right. exact Hzν.
Qed.

Lemma expr_total_on_restrict_insert_fresh
    (Σ : gmap atom ty) T e x (m : WfWorld) :
  x ∉ dom Σ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := T]> Σ) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  expr_total_on (dom Σ) e (res_restrict m (dom Σ)).
Proof.
  intros Hx Hdom Hclosed [Hfv Htotal].
  split; [set_solver |].
  intros σ Hσ.
  destruct Hσ as [σm [Hσm Hrestrict]].
  destruct (Htotal σm Hσm) as [vx Hsteps].
  exists vx.
  replace (subst_map (store_restrict σ (dom Σ)) e)
    with (subst_map (store_restrict σm (dom (<[x := T]> Σ))) e).
  - exact Hsteps.
  - symmetry.
    eapply subst_map_eq_on_fv.
	    + apply closed_env_restrict. exact (proj1 (Hclosed σm Hσm)).
	    + rewrite !store_restrict_restrict.
	      rewrite <- Hrestrict.
	      rewrite !store_restrict_restrict.
		      f_equal. eapply dom_insert_inter_fv_tm_fresh_restrict; eauto.
Qed.

Lemma expr_total_on_restrict_self X e (m : WfWorld) :
  expr_total_on X e m →
  expr_total_on X e (res_restrict m X).
Proof.
  intros [Hfv Htotal]. split; [exact Hfv |].
  intros σ Hσ.
  destruct Hσ as [σm [Hσm <-]].
  rewrite store_restrict_restrict.
  replace (X ∩ X) with X by set_solver.
  apply Htotal. exact Hσm.
Qed.

Lemma world_store_closed_on_restrict_insert_fresh
    (Σ : gmap atom ty) T x (m : WfWorld) :
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  world_store_closed_on (dom Σ) (res_restrict m (dom Σ)).
Proof.
  intros Hclosed σ Hσ.
  destruct Hσ as [σm [Hσm <-]].
  rewrite store_restrict_restrict.
  replace (dom Σ ∩ dom Σ) with (dom Σ) by set_solver.
  replace (store_restrict σm (dom Σ))
    with (store_restrict (store_restrict σm (dom (<[x := T]> Σ))) (dom Σ)).
  - apply store_closed_restrict.
    exact (Hclosed σm Hσm).
  - rewrite store_restrict_restrict.
    f_equal. rewrite dom_insert_L. set_solver.
Qed.

Lemma FExprContIn_insert_fresh_env_irrel
    (Σ : gmap atom ty) T Tx e x (P : atom → FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  x ∉ dom Σ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := Tx]> Σ) →
  world_store_closed_on (dom (<[x := Tx]> Σ)) m →
  expr_total_on (dom (<[x := Tx]> Σ)) e m →
  (∀ ν, formula_fv (P ν) ⊆ dom Σ ∪ {[ν]}) →
  formula_family_rename_stable_on (dom Σ) P →
  res_restrict m (dom Σ) ⊨ FExprContIn Σ e P →
  m ⊨ FExprContIn (<[x := Tx]> Σ) e P.
Proof.
  intros Hty Hx Hdom Hclosed Htotal HPfv HPrename Hcont.
  assert (Hdom_restrict :
    world_dom (res_restrict m (dom Σ) : World) = dom Σ).
  { simpl. rewrite Hdom, dom_insert_L. set_solver. }
  assert (Hclosed_restrict :
    world_store_closed_on (dom Σ) (res_restrict m (dom Σ))).
  { eapply world_store_closed_on_restrict_insert_fresh; eauto. }
  assert (Htotal_restrict :
    expr_total_on (dom Σ) e (res_restrict m (dom Σ))).
  {
    eapply (expr_total_on_restrict_insert_fresh Σ Tx e x m); eauto.
  }
  assert (Hty_insert : <[x := Tx]> Σ ⊢ₑ e ⋮ T).
  {
    eapply basic_typing_weaken_insert_tm.
    - set_solver.
    - exact Hty.
  }
	  assert (HPfv_insert :
	    ∀ ν, formula_fv (P ν) ⊆ dom (<[x := Tx]> Σ) ∪ {[ν]}).
	  {
	    intros ν z Hz.
	    specialize (HPfv ν z Hz) as HzP.
	    rewrite dom_insert_L.
	    apply elem_of_union in HzP as [HzΣ | Hzν].
	    - apply elem_of_union. left. apply elem_of_union. right. exact HzΣ.
	    - apply elem_of_union. right. exact Hzν.
	  }
  assert (HPrename_insert :
    formula_family_rename_stable_on (dom (<[x := Tx]> Σ)) P).
  {
    unfold formula_family_rename_stable_on in *.
    intros a b n Ha Hb.
    apply HPrename; rewrite dom_insert_L in *; set_solver.
  }
  pose proof (proj1
    (FExprContIn_iff_let_result_world_on_exact_domain
      Σ T e P (res_restrict m (dom Σ))
      Hty Hdom_restrict Hclosed_restrict Htotal_restrict HPfv HPrename)
    Hcont) as [L [HL Hbody]].
  apply (proj2
    (FExprContIn_iff_let_result_world_on_exact_domain
      (<[x := Tx]> Σ) T e P m
      Hty_insert Hdom Hclosed Htotal HPfv_insert HPrename_insert)).
	  exists (L ∪ dom (<[x := Tx]> Σ) ∪ fv_tm e).
	  split; [set_solver |].
	  intros ν Hν Hfresh Hresult.
	  rewrite !not_elem_of_union in Hν.
	  destruct Hν as [[HνL HνΣx] Hνe].
	  rewrite dom_insert_L, not_elem_of_union, not_elem_of_singleton in HνΣx.
	  destruct HνΣx as [Hνx HνΣ].
	  assert (Hfresh_restrict :
	    ν ∉ world_dom (res_restrict m (dom Σ) : World)).
	  { rewrite Hdom_restrict. exact HνΣ. }
	  assert (Hresult_restrict :
	    ∀ σ, (res_restrict m (dom Σ) : World) σ →
	      ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx).
	  {
	    eapply expr_total_on_to_fv_result; eauto.
	  }
	  pose proof (Hbody ν HνL Hfresh_restrict Hresult_restrict)
	    as Hsmall.
  pose proof (proj2 (res_models_minimal_on
    (dom Σ ∪ {[ν]})
    (let_result_world_on e ν m Hfresh Hresult)
    (P ν) (HPfv ν))) as Hminimal.
  apply Hminimal.
  rewrite (let_result_world_on_restrict_input
    (dom Σ) e ν m Hfresh Hresult Hfresh_restrict Hresult_restrict).
  - exact Hsmall.
	  - destruct Htotal as [Hfv _].
	    rewrite dom_insert_L in Hfv.
	    pose proof Hx as Hx_fv.
	    rewrite not_elem_of_union in Hx_fv.
	    destruct Hx_fv as [_ Hx_fv].
	    intros z Hz0. pose proof Hz0 as Hz. apply Hfv in Hz.
	    apply elem_of_union in Hz as [Hzx | HzΣ]; [| exact HzΣ].
	    apply elem_of_singleton in Hzx.
	    exfalso. apply Hx_fv. rewrite <- Hzx. exact Hz0.
	  - rewrite Hdom, dom_insert_L. set_solver.
	  - exact HνΣ.
Qed.

Lemma FExprContIn_restrict_insert_fresh_env_irrel
    (Σ : gmap atom ty) T Tx e x (P : atom → FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  x ∉ dom Σ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := Tx]> Σ) →
  world_store_closed_on (dom (<[x := Tx]> Σ)) m →
  expr_total_on (dom (<[x := Tx]> Σ)) e m →
  (∀ ν, formula_fv (P ν) ⊆ dom Σ ∪ {[ν]}) →
  formula_family_rename_stable_on (dom Σ) P →
  m ⊨ FExprContIn (<[x := Tx]> Σ) e P →
  res_restrict m (dom Σ) ⊨ FExprContIn Σ e P.
Proof.
  intros Hty Hx Hdom Hclosed Htotal HPfv HPrename Hcont.
  assert (Hdom_restrict :
    world_dom (res_restrict m (dom Σ) : World) = dom Σ).
  { simpl. rewrite Hdom, dom_insert_L. set_solver. }
  assert (Hclosed_restrict :
    world_store_closed_on (dom Σ) (res_restrict m (dom Σ))).
  { eapply world_store_closed_on_restrict_insert_fresh; eauto. }
  assert (Htotal_restrict :
    expr_total_on (dom Σ) e (res_restrict m (dom Σ))).
  {
    eapply (expr_total_on_restrict_insert_fresh Σ Tx e x m); eauto.
  }
  assert (Hty_insert : <[x := Tx]> Σ ⊢ₑ e ⋮ T).
  {
    eapply basic_typing_weaken_insert_tm.
    - set_solver.
    - exact Hty.
  }
	  assert (HPfv_insert :
	    ∀ ν, formula_fv (P ν) ⊆ dom (<[x := Tx]> Σ) ∪ {[ν]}).
	  {
	    intros ν z Hz.
	    specialize (HPfv ν z Hz) as HzP.
	    rewrite dom_insert_L.
	    apply elem_of_union in HzP as [HzΣ | Hzν].
	    - apply elem_of_union. left. apply elem_of_union. right. exact HzΣ.
	    - apply elem_of_union. right. exact Hzν.
	  }
  assert (HPrename_insert :
    formula_family_rename_stable_on (dom (<[x := Tx]> Σ)) P).
  {
    unfold formula_family_rename_stable_on in *.
    intros a b n Ha Hb.
    apply HPrename; rewrite dom_insert_L in *; set_solver.
  }
  pose proof (proj1
    (FExprContIn_iff_let_result_world_on_exact_domain
      (<[x := Tx]> Σ) T e P m
      Hty_insert Hdom Hclosed Htotal HPfv_insert HPrename_insert)
    Hcont) as [L [HL Hbody]].
  apply (proj2
    (FExprContIn_iff_let_result_world_on_exact_domain
      Σ T e P (res_restrict m (dom Σ))
      Hty Hdom_restrict Hclosed_restrict Htotal_restrict HPfv HPrename)).
	  exists (L ∪ dom (<[x := Tx]> Σ) ∪ fv_tm e).
	  split; [set_solver |].
	  intros ν Hν Hfresh_restrict Hresult_restrict.
	  rewrite !not_elem_of_union in Hν.
	  destruct Hν as [[HνL HνΣx] Hνe].
	  rewrite dom_insert_L, not_elem_of_union, not_elem_of_singleton in HνΣx.
	  destruct HνΣx as [Hνx HνΣ].
	  assert (Hfresh : ν ∉ world_dom (m : World)).
	  { rewrite Hdom, dom_insert_L. set_solver. }
	  assert (Hresult :
	    ∀ σ, (m : World) σ →
	      ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx).
	  {
	    eapply expr_total_on_to_fv_result; eauto.
	  }
	  pose proof (Hbody ν HνL Hfresh Hresult) as Hfull.
  pose proof (proj1 (res_models_minimal_on
    (dom Σ ∪ {[ν]})
    (let_result_world_on e ν m Hfresh Hresult)
    (P ν) (HPfv ν))) as Hminimal.
  rewrite <- (let_result_world_on_restrict_input
    (dom Σ) e ν m Hfresh Hresult Hfresh_restrict Hresult_restrict).
  - apply Hminimal. exact Hfull.
	  - destruct Htotal as [Hfv _].
	    rewrite dom_insert_L in Hfv.
	    pose proof Hx as Hx_fv.
	    rewrite not_elem_of_union in Hx_fv.
	    destruct Hx_fv as [_ Hx_fv].
	    intros z Hz0. pose proof Hz0 as Hz. apply Hfv in Hz.
	    apply elem_of_union in Hz as [Hzx | HzΣ]; [| exact HzΣ].
	    apply elem_of_singleton in Hzx.
	    exfalso. apply Hx_fv. rewrite <- Hzx. exact Hz0.
	  - rewrite Hdom, dom_insert_L. set_solver.
	  - exact HνΣ.
Qed.

Lemma FExprContIn_insert_fresh_env_irrel_iff
    (Σ : gmap atom ty) T Tx e x (P : atom → FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  x ∉ dom Σ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := Tx]> Σ) →
  world_store_closed_on (dom (<[x := Tx]> Σ)) m →
  expr_total_on (dom (<[x := Tx]> Σ)) e m →
  (∀ ν, formula_fv (P ν) ⊆ dom Σ ∪ {[ν]}) →
  formula_family_rename_stable_on (dom Σ) P →
  m ⊨ FExprContIn (<[x := Tx]> Σ) e P <->
  res_restrict m (dom Σ) ⊨ FExprContIn Σ e P.
Proof.
  intros Hty Hx Hdom Hclosed Htotal HPfv HPrename.
  split.
  - eapply FExprContIn_restrict_insert_fresh_env_irrel; eauto.
  - eapply FExprContIn_insert_fresh_env_irrel; eauto.
Qed.

Lemma denot_ty_fuel_intro gas Σ τ e m :
  basic_choice_ty (dom Σ) τ →
  Σ ⊢ₑ e ⋮ erase_ty τ →
  world_closed_on (dom Σ) m →
  expr_total_on (dom Σ) e m →
  m ⊨ denot_ty_fuel_body gas Σ τ e →
  dom Σ ⊆ world_dom (m : World) →
  m ⊨ denot_ty_fuel gas Σ τ e.
Proof.
  intros Hbasic Htyped Hclosed Htotal Hbody Hdom.
  rewrite denot_ty_fuel_unfold.
  unfold denot_ty_obligations.
  apply res_models_and_intro_from_models.
  - unfold FBasicTypingIn, res_models.
    eapply res_models_with_store_store_resource_atom_vars_intro.
    + unfold formula_scoped_in_world.
	      rewrite formula_fv_FStoreResourceAtomVars.
	      rewrite !atom_env_to_lty_env_dom.
	      rewrite lvars_fv_union, !lvars_fv_of_atoms.
      rewrite dom_empty_L. set_solver.
    + rewrite lty_env_open_atom_env_empty, open_cty_env_empty, open_tm_env_empty.
      split; assumption.
  - apply res_models_and_intro_from_models.
    + unfold FClosedResourceIn, res_models.
      eapply res_models_with_store_resource_atom_vars_intro.
      * unfold formula_scoped_in_world.
        rewrite formula_fv_FResourceAtomVars.
        rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
        rewrite dom_empty_L. set_solver.
      * rewrite atom_env_to_lty_env_atom_dom.
        eapply world_closed_on_le.
        -- apply res_restrict_le.
        -- exact Hclosed.
    + apply res_models_and_intro_from_models.
      * unfold FStrongTotalIn, res_models.
        eapply res_models_with_store_store_resource_atom_vars_intro.
        -- unfold formula_scoped_in_world.
           rewrite formula_fv_FStoreResourceAtomVars.
           rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
           rewrite dom_empty_L. set_solver.
        -- rewrite atom_env_to_lty_env_atom_dom.
           rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
           rewrite store_restrict_empty, open_tm_env_empty.
           eapply expr_total_with_store_empty_restrict; eauto.
      * exact Hbody.
Qed.

Lemma denot_ty_fuel_body_of_formula gas Σ τ e m :
  m ⊨ denot_ty_fuel gas Σ τ e →
  m ⊨ denot_ty_fuel_body gas Σ τ e.
Proof.
  intros Hm.
  rewrite denot_ty_fuel_unfold in Hm.
  unfold denot_ty_obligations in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  exact Hm.
Qed.

Lemma denot_ty_fuel_basic_of_formula gas Σ τ e m :
  m ⊨ denot_ty_fuel gas Σ τ e →
  basic_choice_ty (dom Σ) τ ∧ Σ ⊢ₑ e ⋮ erase_ty τ.
Proof.
  intros Hm.
  rewrite denot_ty_fuel_unfold in Hm.
  unfold denot_ty_obligations, FBasicTypingIn in Hm.
  apply res_models_with_store_and_elim_l in Hm.
  destruct (res_models_with_store_store_resource_atom_vars_elim _ _ _ _ Hm)
    as [_ [_ [Hbasic _]]].
  rewrite lty_env_open_atom_env_empty, open_cty_env_empty, open_tm_env_empty in Hbasic.
  exact Hbasic.
Qed.

Lemma world_closed_on_extend X (m n : WfWorld) :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  world_closed_on X m →
  world_closed_on X n.
Proof.
  intros HXm Hle Hclosed σ Hσ.
  pose proof (res_restrict_eq_of_le m n Hle) as Hrestrict.
  assert ((res_restrict n (world_dom (m : World)) : World)
    (store_restrict σ (world_dom (m : World)))) as Hσm.
  { exists σ. split; [exact Hσ | reflexivity]. }
  rewrite Hrestrict in Hσm.
  replace (store_restrict σ X) with
    (store_restrict (store_restrict σ (world_dom (m : World))) X).
  - exact (Hclosed _ Hσm).
  - store_norm. reflexivity.
Qed.

Lemma denot_ty_fuel_world_closed_on_of_formula gas Σ τ e m :
  m ⊨ denot_ty_fuel gas Σ τ e →
  world_closed_on (dom Σ) m.
Proof.
  intros Hm.
  rewrite denot_ty_fuel_unfold in Hm.
  unfold denot_ty_obligations, FClosedResourceIn in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  apply res_models_with_store_and_elim_l in Hm.
	  destruct (res_models_with_store_resource_atom_vars_elim ∅ m
	    (dom (atom_env_to_lty_env Σ))
	    (world_closed_on (lty_env_atom_dom (atom_env_to_lty_env Σ))) Hm)
	    as [m0 [Hscope [Hclosed Hle]]].
	  rewrite atom_env_to_lty_env_atom_dom in Hclosed.
	  rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms in Hclosed.
  eapply (world_closed_on_extend (dom Σ)
    (res_restrict m0 (dom Σ)) m).
  - simpl. intros z Hz. apply elem_of_intersection. split; [| exact Hz].
    unfold formula_scoped_in_world in Hscope.
    rewrite dom_empty_L in Hscope.
    apply Hscope. apply elem_of_union. right.
    rewrite formula_fv_FResourceAtomVars.
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms. exact Hz.
  - etrans; [apply res_restrict_le | exact Hle].
  - exact Hclosed.
Qed.

Lemma denot_ty_fuel_expr_total_on_of_formula gas Σ τ e m :
  m ⊨ denot_ty_fuel gas Σ τ e →
  expr_total_on (dom Σ) e m.
Proof.
  intros Hm.
  pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hm)
    as [_ Htyped].
  split.
  - eauto using basic_typing_contains_fv_tm.
  - rewrite denot_ty_fuel_unfold in Hm.
    unfold denot_ty_obligations, FStrongTotalIn in Hm.
    apply res_models_with_store_and_elim_r in Hm.
    apply res_models_with_store_and_elim_r in Hm.
    apply res_models_with_store_and_elim_l in Hm.
    destruct (res_models_with_store_store_resource_atom_vars_elim ∅ m
      (dom (atom_env_to_lty_env Σ))
      (fun η ρ m =>
        expr_total_with_store (lty_env_atom_dom (atom_env_to_lty_env Σ))
          (open_tm_env η e) ρ m) Hm)
      as [m0 [Hscope [Htotal Hle]]].
    rewrite atom_env_to_lty_env_atom_dom in Htotal.
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms in Htotal.
    rewrite store_restrict_empty, open_tm_env_empty in Htotal.
    destruct Htotal as [_ Htotal].
    intros σ Hσ.
    pose proof (res_restrict_eq_of_le m0 m Hle) as Hrestrict.
    assert (Hσm0 :
      (m0 : World) (store_restrict σ (world_dom (m0 : World)))).
    { assert ((res_restrict m (world_dom (m0 : World)) : World)
        (store_restrict σ (world_dom (m0 : World)))) as Hraw.
      { exists σ. split; [exact Hσ | reflexivity]. }
      rewrite Hrestrict in Hraw. exact Hraw. }
    assert (HdomΣ : dom Σ ⊆ world_dom (m0 : World)).
    { unfold formula_scoped_in_world in Hscope.
      rewrite dom_empty_L in Hscope.
      intros z Hz. apply Hscope. apply elem_of_union. right.
      rewrite formula_fv_FStoreResourceAtomVars.
      rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms. exact Hz. }
    assert (HσD :
      (res_restrict m0 (dom Σ) : World) (store_restrict σ (dom Σ))).
    { exists (store_restrict σ (world_dom (m0 : World))).
      split; [exact Hσm0 |].
      rewrite store_restrict_restrict.
      replace (world_dom (m0 : World) ∩ dom Σ) with (dom Σ)
        by set_solver.
      reflexivity. }
    specialize (Htotal _ HσD) as [vx Hsteps].
    exists vx.
    rewrite map_empty_union in Hsteps.
    rewrite store_restrict_restrict in Hsteps.
    replace (dom Σ ∩ dom Σ) with (dom Σ) in Hsteps by set_solver.
    exact Hsteps.
Qed.
