(** * ChoiceTyping.TLetReductionFuelSupport

    Model-level reduction lemmas for the [tlet] soundness case.
    The final semantic wrappers stay in [TLetDenotation]. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps StrongNormalization Sugar.
From ChoiceTyping Require Import TLetTotal RegularDenotation
  Naming ResultWorldBridge.
From ChoiceType Require Import BasicStore LocallyNamelessProps DenotationRefinement.

Import Tactics.

(** Resource/totality and type-denotation obligation helpers for the [tlet]
    reduction proof. *)
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

Lemma denot_ty_intro Σ τ e m :
  basic_choice_ty (dom Σ) τ →
  Σ ⊢ₑ e ⋮ erase_ty τ →
  world_closed_on (dom Σ) m →
  expr_total_on (dom Σ) e m →
  m ⊨ denot_ty_body Σ τ e →
  dom Σ ⊆ world_dom (m : World) →
  m ⊨ denot_ty_on Σ τ e.
Proof.
  intros Hbasic Htyped Hclosed Htotal Hbody Hdom.
  unfold denot_ty_on, denot_ty_body.
  unfold denot_ty_obligations.
  apply res_models_and_intro_from_models.
  - unfold FBasicTypingIn, res_models.
    eapply res_models_with_store_store_resource_atom_vars_intro.
    + unfold formula_scoped_in_world.
	      rewrite formula_fv_FStoreResourceAtom_lvars.
	      rewrite !atom_env_to_lty_env_dom.
	      rewrite lvars_fv_union, !lvars_fv_of_atoms.
      rewrite dom_empty_L. set_solver.
    + rewrite lty_env_open_atom_env, open_cty_env_empty, open_tm_env_empty.
      split; assumption.
  - apply res_models_and_intro_from_models.
    + unfold FClosedResourceIn, res_models.
      eapply res_models_with_store_resource_atom_vars_intro.
      * unfold formula_scoped_in_world.
        rewrite formula_fv_FResourceAtom_lvars.
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
           rewrite formula_fv_FStoreResourceAtom_lvars.
           rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
           rewrite dom_empty_L. set_solver.
        -- rewrite atom_env_to_lty_env_atom_dom.
           rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
           rewrite store_restrict_empty, open_tm_env_empty.
           eapply expr_total_with_store_empty_restrict; eauto.
      * exact Hbody.
Qed.

Lemma denot_ty_body_of_formula Σ τ e m :
  m ⊨ denot_ty_on Σ τ e →
  m ⊨ denot_ty_body Σ τ e.
Proof.
  intros Hm.
  unfold denot_ty_on, denot_ty_body in Hm.
  unfold denot_ty_obligations in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  exact Hm.
Qed.

Lemma denot_ty_basic_of_formula Σ τ e m :
  m ⊨ denot_ty_on Σ τ e →
  basic_choice_ty (dom Σ) τ ∧ Σ ⊢ₑ e ⋮ erase_ty τ.
Proof.
  intros Hm.
  unfold denot_ty_on in Hm.
  unfold denot_ty_obligations, FBasicTypingIn in Hm.
  apply res_models_with_store_and_elim_l in Hm.
  destruct (res_models_with_store_store_resource_atom_vars_elim _ _ _ _ Hm)
    as [_ [_ [Hbasic _]]].
  rewrite lty_env_open_atom_env, open_cty_env_empty, open_tm_env_empty in Hbasic.
  exact Hbasic.
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
  apply denot_ty_intro.
Qed.

Lemma denot_ty_fuel_body_of_formula gas Σ τ e m :
  m ⊨ denot_ty_fuel gas Σ τ e →
  m ⊨ denot_ty_fuel_body gas Σ τ e.
Proof.
  apply denot_ty_body_of_formula.
Qed.

Lemma denot_ty_fuel_basic_of_formula gas Σ τ e m :
  m ⊨ denot_ty_fuel gas Σ τ e →
  basic_choice_ty (dom Σ) τ ∧ Σ ⊢ₑ e ⋮ erase_ty τ.
Proof.
  apply denot_ty_basic_of_formula.
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

Lemma denot_ty_world_closed_on_of_formula Σ τ e m :
  m ⊨ denot_ty_on Σ τ e →
  world_closed_on (dom Σ) m.
Proof.
  intros Hm.
  unfold denot_ty_on in Hm.
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
    rewrite formula_fv_FResourceAtom_lvars.
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms. exact Hz.
  - etrans; [apply res_restrict_le | exact Hle].
  - exact Hclosed.
Qed.

Lemma denot_ty_expr_total_on_of_formula Σ τ e m :
  m ⊨ denot_ty_on Σ τ e →
  expr_total_on (dom Σ) e m.
Proof.
  intros Hm.
  pose proof (denot_ty_basic_of_formula _ _ _ _ Hm)
    as [_ Htyped].
  split.
  - eauto using basic_typing_contains_fv_tm.
  - unfold denot_ty_on in Hm.
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
      rewrite formula_fv_FStoreResourceAtom_lvars.
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

Lemma denot_ty_fuel_world_closed_on_of_formula gas Σ τ e m :
  m ⊨ denot_ty_fuel gas Σ τ e →
  world_closed_on (dom Σ) m.
Proof.
  apply denot_ty_world_closed_on_of_formula.
Qed.

Lemma denot_ty_fuel_expr_total_on_of_formula gas Σ τ e m :
  m ⊨ denot_ty_fuel gas Σ τ e →
  expr_total_on (dom Σ) e m.
Proof.
  apply denot_ty_expr_total_on_of_formula.
Qed.
