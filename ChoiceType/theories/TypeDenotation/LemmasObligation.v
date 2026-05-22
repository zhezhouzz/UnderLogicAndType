(** * ChoiceType.TypeDenotation.LemmasObligation

    Obligation-facing introduction, elimination, and transport helpers. *)

From Stdlib Require Import Logic.FunctionalExtensionality
  Logic.PropExtensionality Lia.
From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps BasicTypingProps
  Sugar.
From ChoiceLogic Require Import FormulaDerived FormulaWorldExtension.
From ChoiceType Require Export TypeDenotation.LemmasFormula.
From ChoiceType Require Import BasicStore BasicTyping LocallyNamelessProps
  TypeDenotation.FormulaEquiv.

Local Notation FQ := FormulaQ.

Lemma basic_qualifier_lvar_body_of_lvars_at_depth1 D φ :
  lvars_at_depth 1 (qual_vars φ) ⊆ D ->
  basic_qualifier_lvar_body D φ.
Proof.
  intros Hsub u Hu.
  destruct u as [n|x].
  - destruct n as [|n].
    + apply elem_of_union_r. set_solver.
    + apply elem_of_union_l.
      unfold lvars_shift. apply elem_of_map.
      exists (LVBound n). split; [reflexivity |].
      apply Hsub.
      apply lvars_at_depth_elem.
      exists (LVBound (S n)). split; [exact Hu |].
      cbn [logic_var_at_depth].
      destruct (decide (1 <= S n)) as [_|Hbad]; [|lia].
      replace (S n - 1) with n by lia. reflexivity.
  - apply elem_of_union_l.
    unfold lvars_shift. apply elem_of_map.
    exists (LVFree x). split; [reflexivity |].
    apply Hsub.
    apply lvars_at_depth_elem.
    exists (LVFree x). split; [exact Hu | reflexivity].
Qed.

Lemma basic_choice_ty_lvar_of_lvars_subset D τ :
  choice_ty_lvars τ ⊆ D ->
  basic_choice_ty_lvar D τ.
Proof.
  revert D.
  induction τ; intros D Hsub; cbn [choice_ty_lvars choice_ty_lvars_at] in Hsub.
  - constructor. eapply basic_qualifier_lvar_body_of_lvars_at_depth1. exact Hsub.
  - constructor. eapply basic_qualifier_lvar_body_of_lvars_at_depth1. exact Hsub.
  - constructor; [apply IHτ1 | apply IHτ2]; set_solver.
  - constructor; [apply IHτ1 | apply IHτ2]; set_solver.
  - constructor; [apply IHτ1 | apply IHτ2]; set_solver.
  - constructor.
    + apply IHτ1. set_solver.
    + apply IHτ2.
      apply choice_ty_lvars_body_subset.
      set_solver.
  - constructor.
    + apply IHτ1. set_solver.
    + apply IHτ2.
      apply choice_ty_lvars_body_subset.
      set_solver.
Qed.

Lemma basic_qualifier_lvar_body_mono D E φ :
  D ⊆ E ->
  basic_qualifier_lvar_body D φ ->
  basic_qualifier_lvar_body E φ.
Proof.
  unfold basic_qualifier_lvar_body.
  intros Hsub Hφ.
  etransitivity; [exact Hφ |].
  assert (Hshift : lvars_shift D ⊆ lvars_shift E).
  { apply lvars_shift_mono. exact Hsub. }
  set_solver.
Qed.

Lemma basic_choice_ty_lvar_mono D E τ :
  D ⊆ E ->
  basic_choice_ty_lvar D τ ->
  basic_choice_ty_lvar E τ.
Proof.
  intros Hsub Hbasic.
  revert E Hsub.
  induction Hbasic; intros E Hsub.
  - constructor. eapply basic_qualifier_lvar_body_mono; eauto.
  - constructor. eapply basic_qualifier_lvar_body_mono; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor.
    + eapply IHHbasic1. exact Hsub.
    + eapply IHHbasic2.
      assert (Hshift : lvars_shift D ⊆ lvars_shift E).
      { apply lvars_shift_mono. exact Hsub. }
      set_solver.
  - econstructor.
    + eapply IHHbasic1. exact Hsub.
    + eapply IHHbasic2.
      assert (Hshift : lvars_shift D ⊆ lvars_shift E).
      { apply lvars_shift_mono. exact Hsub. }
      set_solver.
Qed.

Lemma lvars_to_atoms_empty_union D1 D2 :
  lvars_to_atoms ∅ (D1 ∪ D2) =
  lvars_to_atoms ∅ D1 ∪ lvars_to_atoms ∅ D2.
Proof.
  apply set_eq. intros x.
  rewrite !lvars_to_atoms_elem.
  split.
  - intros [v [Hv Hatom]].
    apply elem_of_union in Hv as [Hv|Hv].
    + apply elem_of_union. left.
      apply lvars_to_atoms_elem. exists v. eauto.
    + apply elem_of_union. right.
      apply lvars_to_atoms_elem. exists v. eauto.
  - intros Hx.
    apply elem_of_union in Hx as [Hx|Hx].
    + apply lvars_to_atoms_elem in Hx as [v [Hv Hatom]].
      exists v; split; [set_solver | exact Hatom].
    + apply lvars_to_atoms_elem in Hx as [v [Hv Hatom]].
      exists v; split; [set_solver | exact Hatom].
Qed.

Lemma lvars_to_atoms_empty_eq_fv D :
  lvars_to_atoms ∅ D = lvars_fv D.
Proof.
  apply set_eq. intros x. split.
  - apply lvars_to_atoms_empty_subset.
  - intros Hx.
    apply lvars_to_atoms_elem.
    exists (LVFree x). split.
    + apply lvars_fv_elem. exact Hx.
    + reflexivity.
Qed.

Lemma store_restrict_union_restrict_subset
    (ρ σ : gmap atom value) D X :
  X ⊆ D ->
  store_restrict
    ((store_restrict ρ D : gmap atom value) ∪
     (store_restrict σ D : gmap atom value)) X =
  store_restrict ((ρ : gmap atom value) ∪ (σ : gmap atom value)) X.
Proof.
  intros HXD.
  apply (map_eq (M:=gmap atom)). intros z.
  rewrite !store_restrict_lookup.
  destruct (decide (z ∈ X)) as [HzX|HzX]; [|reflexivity].
  assert (HzD : z ∈ D) by set_solver.
  destruct (ρ !! z) as [v|] eqn:Hρz.
  - rewrite (@lookup_union_l' atom (gmap atom) _ _ _ _ _ _ _ _ _
      value (store_restrict ρ D) (store_restrict σ D) z).
    2:{ exists v. rewrite store_restrict_lookup.
        destruct (decide (z ∈ D)); [exact Hρz | contradiction]. }
    rewrite (@lookup_union_l' atom (gmap atom) _ _ _ _ _ _ _ _ _
      value ρ σ z) by eauto.
    rewrite store_restrict_lookup.
    destruct (decide (z ∈ D)); [reflexivity | contradiction].
  - assert (HρDz : store_restrict ρ D !! z = None).
    { rewrite store_restrict_lookup.
      destruct (decide (z ∈ D)); [exact Hρz | reflexivity]. }
    rewrite (@lookup_union_r atom (gmap atom) _ _ _ _ _ _ _ _ _
      value (store_restrict ρ D) (store_restrict σ D) z)
      by exact HρDz.
    rewrite (@lookup_union_r atom (gmap atom) _ _ _ _ _ _ _ _ _
      value ρ σ z) by exact Hρz.
    rewrite store_restrict_lookup.
    destruct (decide (z ∈ D)); [reflexivity | contradiction].
Qed.

Lemma FDenotObligationIn_with_store_parts Σ τ e ρ m :
  res_models_with_store ρ m (FDenotObligationIn Σ τ e) ->
  ∃ m0,
    denot_obligation_parts Σ τ e ∅
      (store_restrict ρ (lvars_fv (dom Σ)))
      (res_restrict m0 (lvars_fv (dom Σ))) ∧
    m0 ⊑ m.
Proof.
  intros Hm.
  unfold FDenotObligationIn in Hm.
  destruct (res_models_with_store_store_resource_atom_vars_elim ρ m
    (dom Σ) (denot_obligation_parts Σ τ e) Hm)
    as [m0 [_ [Hparts Hle]]].
  eauto.
Qed.

Lemma FDenotObligationIn_basic_choice Σ τ e ρ m :
  res_models_with_store ρ m (FDenotObligationIn Σ τ e) ->
  basic_choice_ty_lvar
    (dom (lty_env_open_lvars ∅ Σ)) (open_cty_env ∅ τ).
Proof.
  intros Hm.
  destruct (FDenotObligationIn_with_store_parts Σ τ e ρ m Hm)
    as [? [Hparts _]].
  exact (proj1 Hparts).
Qed.

Lemma FDenotObligationIn_basic_typing Σ τ e ρ m :
  res_models_with_store ρ m (FDenotObligationIn Σ τ e) ->
  basic_typing_lvar
    (lty_env_open_lvars ∅ Σ) (open_tm_env ∅ e)
    (erase_ty (open_cty_env ∅ τ)).
Proof.
  intros Hm.
  destruct (FDenotObligationIn_with_store_parts Σ τ e ρ m Hm)
    as [? [Hparts _]].
  exact (proj1 (proj2 Hparts)).
Qed.

Lemma FDenotObligationIn_closed_resource Σ τ e ρ m :
  res_models_with_store ρ m (FDenotObligationIn Σ τ e) ->
  closed_resource_lvar Σ ∅ m.
Proof.
  intros Hm.
  unfold FDenotObligationIn in Hm.
  destruct (res_models_with_store_store_resource_atom_vars_elim ρ m
    (dom Σ) (denot_obligation_parts Σ τ e) Hm)
    as [m0 [Hscope [Hparts Hle]]].
  destruct Hparts as [_ [_ [Hclosed _]]].
  unfold closed_resource_lvar in Hclosed |- *.
  eapply (world_closed_on_extend (lvars_to_atoms ∅ (dom Σ))
    (res_restrict m0 (lvars_fv (dom Σ))) m).
  - simpl. intros z Hz.
    apply elem_of_intersection. split.
    + unfold formula_scoped_in_world in Hscope.
      apply Hscope.
      rewrite formula_fv_FStoreResourceAtom_lvars.
      pose proof (lvars_to_atoms_empty_subset (dom Σ) z Hz).
      set_solver.
    + exact (lvars_to_atoms_empty_subset (dom Σ) z Hz).
  - etrans; [apply res_restrict_le | exact Hle].
  - exact Hclosed.
Qed.

Lemma expr_total_lvar_obligation_extend Σ e ρ (m0 m : WfWorld) :
  lvars_to_atoms ∅ (tm_lvars e) ⊆ lvars_fv (dom Σ) ->
  lvars_fv (dom Σ) ⊆ world_dom (m0 : World) ->
  m0 ⊑ m ->
  expr_total_lvar Σ e ∅
    (store_restrict ρ (lvars_fv (dom Σ)))
    (res_restrict m0 (lvars_fv (dom Σ))) ->
  expr_total_lvar Σ e ∅ ρ m.
Proof.
  intros Hfv HDm0 Hle Htotal.
  unfold expr_total_lvar, expr_total_with_store in *.
  set (D := lvars_fv (dom Σ)).
  set (X := lvars_to_atoms ∅ (dom Σ ∪ tm_lvars e)).
  assert (HX : X ⊆ D).
  {
    subst X D.
    rewrite lvars_to_atoms_empty_union.
    pose proof (lvars_to_atoms_empty_subset (dom Σ)).
    set_solver.
  }
  destruct Htotal as [Hclosed Hsteps].
  assert (Hpull :
    ∀ σ, (m : World) σ →
      (res_restrict m0 D : World) (store_restrict σ D)).
  {
    intros σ Hσ.
    pose proof (res_restrict_eq_of_le m0 m Hle) as Hm0.
    assert ((res_restrict m (world_dom (m0 : World)) : World)
      (store_restrict σ (world_dom (m0 : World)))) as Hσm0.
    { exists σ. split; [exact Hσ | reflexivity]. }
    rewrite Hm0 in Hσm0.
    exists (store_restrict σ (world_dom (m0 : World))).
    split; [exact Hσm0 |].
    subst D.
    rewrite store_restrict_twice_subset by exact HDm0.
    reflexivity.
  }
  split.
  - intros σ Hσ.
    pose proof (Hpull σ Hσ) as HσD.
    specialize (Hclosed _ HσD).
    rewrite <- (store_restrict_union_restrict_subset ρ σ D X HX).
    exact Hclosed.
  - intros σ Hσ.
    pose proof (Hpull σ Hσ) as HσD.
    specialize (Hsteps _ HσD).
    rewrite <- (store_restrict_union_restrict_subset ρ σ D X HX).
    exact Hsteps.
Qed.

Lemma FClosedResourceIn_closed_resource Σ ρ m :
  res_models_with_store ρ m (FClosedResourceIn Σ) ->
  closed_resource_lvar Σ ∅ m.
Proof.
  intros Hm.
  unfold FClosedResourceIn in Hm.
  destruct (res_models_with_store_store_resource_atom_vars_elim ρ m
    (dom Σ) (fun η _ m => closed_resource_lvar Σ η m) Hm)
    as [m0 [Hscope [Hclosed Hle]]].
  unfold closed_resource_lvar in Hclosed |- *.
  eapply (world_closed_on_extend (lvars_to_atoms ∅ (dom Σ))
    (res_restrict m0 (lvars_fv (dom Σ))) m).
  - simpl. intros z Hz.
    apply elem_of_intersection. split.
    + unfold formula_scoped_in_world in Hscope.
      apply Hscope.
      rewrite formula_fv_FStoreResourceAtom_lvars.
      pose proof (lvars_to_atoms_empty_subset (dom Σ) z Hz).
      set_solver.
    + exact (lvars_to_atoms_empty_subset (dom Σ) z Hz).
  - etrans; [apply res_restrict_le | exact Hle].
  - exact Hclosed.
Qed.

Lemma closed_resource_lvar_restrict_self Σ η m :
  closed_resource_lvar Σ η m ->
  closed_resource_lvar Σ η (res_restrict m (lvars_fv (dom Σ))).
Proof.
  intros Hclosed.
  eapply world_closed_on_le; [apply res_restrict_le | exact Hclosed].
Qed.

Lemma FClosedResourceIn_intro_lvar Σ (m : WfWorld) :
  lvars_fv (dom Σ) ⊆ world_dom (m : World) ->
  closed_resource_lvar Σ ∅ m ->
  m ⊨ FClosedResourceIn Σ.
Proof.
  intros Hscope Hclosed.
  unfold res_models, FClosedResourceIn.
  eapply res_models_with_store_store_resource_atom_vars_intro.
  - unfold formula_scoped_in_world.
    rewrite dom_empty_L, formula_fv_FStoreResourceAtom_lvars.
    set_solver.
  - apply closed_resource_lvar_restrict_self. exact Hclosed.
Qed.

Lemma FClosedResourceIn_insert_fresh_atom_env
    (Δ : gmap atom ty) x T (m : WfWorld) :
  x ∉ dom Δ ->
  m ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Δ)) ->
  m ⊨ FClosedResourceIn (atom_env_to_lty_env Δ).
Proof.
  intros Hx Hclosed_new.
  pose proof (res_models_with_store_fuel_scoped _ ∅ m _
    Hclosed_new) as Hscope_new.
  pose proof (FClosedResourceIn_closed_resource _ _ _ Hclosed_new)
    as Hclosed_new_cr.
  eapply FClosedResourceIn_intro_lvar.
  - unfold formula_scoped_in_world in Hscope_new.
    unfold FClosedResourceIn in Hscope_new.
    rewrite dom_empty_L, formula_fv_FStoreResourceAtom_lvars in Hscope_new.
    rewrite !atom_env_to_lty_env_dom in *.
    rewrite !lvars_fv_of_atoms in *.
    rewrite dom_insert_L in Hscope_new.
    set_solver.
  - unfold closed_resource_lvar in *.
    rewrite !lvars_to_atoms_empty_eq_fv in *.
    rewrite !atom_env_to_lty_env_dom in *.
    rewrite dom_insert_L in Hclosed_new_cr.
    rewrite !lvars_fv_of_atoms in Hclosed_new_cr.
    intros σ Hσ.
    pose proof (Hclosed_new_cr σ Hσ) as Hclosed_big.
    rewrite lvars_fv_of_atoms.
    change (store_closed (store_restrict σ (dom Δ))).
    rewrite <- (store_restrict_twice_subset
      σ ({[x]} ∪ dom Δ) (dom Δ)) by set_solver.
    apply store_closed_restrict. exact Hclosed_big.
Qed.

Lemma FClosedResourceIn_typed_bind_insert_fresh_atom_env
    (Δ : gmap atom ty) x Tx Ty (m : WfWorld) :
  x ∉ dom Δ ->
  m ⊨ FClosedResourceIn
    (typed_lty_env_bind (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty) ->
  m ⊨ FClosedResourceIn
    (typed_lty_env_bind (atom_env_to_lty_env Δ) Ty).
Proof.
  intros Hx Hclosed_new.
  pose proof (res_models_with_store_fuel_scoped _ ∅ m _
    Hclosed_new) as Hscope_new.
  pose proof (FClosedResourceIn_closed_resource _ _ _ Hclosed_new)
    as Hclosed_new_cr.
  eapply FClosedResourceIn_intro_lvar.
  - unfold formula_scoped_in_world in Hscope_new.
    unfold FClosedResourceIn in Hscope_new.
    rewrite dom_empty_L, formula_fv_FStoreResourceAtom_lvars in Hscope_new.
    rewrite !typed_lty_env_bind_lvars_fv_dom in *.
    rewrite !atom_env_to_lty_env_dom in *.
    rewrite !lvars_fv_of_atoms in *.
    rewrite dom_insert_L in Hscope_new.
    set_solver.
  - unfold closed_resource_lvar in *.
    rewrite !lvars_to_atoms_empty_eq_fv in *.
    rewrite !typed_lty_env_bind_lvars_fv_dom in *.
    rewrite !atom_env_to_lty_env_dom in *.
    rewrite dom_insert_L in Hclosed_new_cr.
    rewrite !lvars_fv_of_atoms in Hclosed_new_cr.
    intros σ Hσ.
    pose proof (Hclosed_new_cr σ Hσ) as Hclosed_big.
    rewrite lvars_fv_of_atoms.
    change (store_closed (store_restrict σ (dom Δ))).
    rewrite <- (store_restrict_twice_subset
      σ ({[x]} ∪ dom Δ) (dom Δ)) by set_solver.
    apply store_closed_restrict. exact Hclosed_big.
Qed.

Lemma FClosedResourceIn_atom_env_intro (Δ : gmap atom ty) (m : WfWorld) :
  dom Δ ⊆ world_dom (m : World) ->
  world_closed_on (dom Δ) m ->
  m ⊨ FClosedResourceIn (atom_env_to_lty_env Δ).
Proof.
  intros Hdom Hclosed.
  unfold res_models, FClosedResourceIn.
  eapply res_models_with_store_store_resource_atom_vars_intro.
  - unfold formula_scoped_in_world.
    rewrite dom_empty_L, formula_fv_FStoreResourceAtom_lvars.
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
    set_solver.
  - rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
    unfold closed_resource_lvar.
    rewrite atom_env_to_lty_env_dom, lvars_to_atoms_of_atoms.
    eapply world_closed_on_le; [apply res_restrict_le |].
    exact Hclosed.
Qed.

Lemma world_closed_on_forall_extension
    (Δ : gmap atom ty) T y (my : WfWorld) :
  y ∉ dom Δ ->
  my ⊨ formula_open 0 y
    (FClosedResourceIn
      (typed_lty_env_bind (atom_env_to_lty_env Δ) T)) ->
  world_closed_on (dom (<[y := T]> Δ)) my.
Proof.
  intros Hy Hclosed.
  rewrite formula_open_FClosedResourceIn in Hclosed.
  rewrite lty_env_open_typed_bind_atom_env in Hclosed by exact Hy.
  pose proof (FClosedResourceIn_closed_resource
    (atom_env_to_lty_env (<[y := T]> Δ)) ∅ my Hclosed) as Hcr.
  unfold closed_resource_lvar in Hcr.
  rewrite atom_env_to_lty_env_dom in Hcr.
  rewrite lvars_to_atoms_of_atoms in Hcr.
  exact Hcr.
Qed.

Lemma FForallTypedBody_insert_fresh_atom_env
    (Δ : gmap atom ty) x Tx Ty Q Q' (m : WfWorld) :
  x ∉ dom Δ ->
  formula_scoped_in_world ∅ m
    (FForallTypedBody (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty Q') ->
  (m ⊨ FClosedResourceIn
      (typed_lty_env_bind (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty) ->
    m ⊨ Q (typed_lty_env_bind (atom_env_to_lty_env Δ) Ty) ->
    m ⊨ Q' (typed_lty_env_bind
      (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty)) ->
  m ⊨ FForallTypedBody (atom_env_to_lty_env Δ) Ty Q ->
  m ⊨ FForallTypedBody
    (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty Q'.
Proof.
  intros Hx Hscope Hpost Hbody.
  unfold FForallTypedBody in Hbody |- *.
  eapply res_models_impl_intro; [exact Hscope |].
  intros Hclosed_new.
  apply Hpost; [exact Hclosed_new |].
  eapply res_models_impl_elim.
  - exact Hbody.
  - eapply FClosedResourceIn_typed_bind_insert_fresh_atom_env; eauto.
Qed.

Lemma FForallTypedBind_insert_fresh_atom_env_map
    (Δ : gmap atom ty) x Tx Ty Q Q' (m : WfWorld) :
  formula_scoped_in_world ∅ m
    (FForallTypedBind (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty Q') ->
  (∃ L : aset,
    world_dom (m : World) ⊆ L ∧
    ∀ y F my,
      y ∉ L ->
      forall_extension_shape (world_dom (m : World)) y F ->
      m #> F ~~> my ->
      my ⊨ formula_open 0 y
        (FForallTypedBody (atom_env_to_lty_env Δ) Ty Q) ->
      my ⊨ formula_open 0 y
        (FForallTypedBody (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty Q')) ->
  m ⊨ FForallTypedBind (atom_env_to_lty_env Δ) Ty Q ->
  m ⊨ FForallTypedBind (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty Q'.
Proof.
  intros Hscope Hmap Hforall.
  unfold FForallTypedBind in *.
  pose proof (res_models_with_store_fuel_scoped _ ∅ m
    (FForall (FForallTypedBody (atom_env_to_lty_env Δ) Ty Q))
    Hforall) as Hscope_old.
  eapply res_models_forall_by_extension_map; eauto.
Qed.

Lemma FForallTypedBody_insert_fresh_atom_env_map_opened
    (Δ : gmap atom ty) x Tx Ty Q Q' y (m : WfWorld) :
  x ∉ dom Δ ->
  y ∉ dom Δ ->
  x <> y ->
  formula_scoped_in_world ∅ m
    (formula_open 0 y
      (FForallTypedBody
        (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty Q')) ->
  (m ⊨ formula_open 0 y
      (Q (typed_lty_env_bind (atom_env_to_lty_env Δ) Ty)) ->
    m ⊨ formula_open 0 y
      (Q' (typed_lty_env_bind
        (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty))) ->
  m ⊨ formula_open 0 y
    (FForallTypedBody (atom_env_to_lty_env Δ) Ty Q) ->
  m ⊨ formula_open 0 y
    (FForallTypedBody
      (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty Q').
Proof.
  intros Hx Hy Hxy Hscope Hpost Hbody.
  unfold FForallTypedBody in Hbody |- *.
  rewrite !formula_open_impl in Hbody |- *.
  eapply res_models_impl_intro; [exact Hscope |].
  intros Hclosed_new.
  assert (Hclosed_old :
    m ⊨ formula_open 0 y
      (FClosedResourceIn
        (typed_lty_env_bind (atom_env_to_lty_env Δ) Ty))).
  {
    rewrite formula_open_FClosedResourceIn in Hclosed_new |- *.
    rewrite lty_env_open_typed_bind_atom_env by exact Hy.
    rewrite lty_env_open_typed_bind_atom_env in Hclosed_new.
    2:{ rewrite dom_insert_L. set_solver. }
    eapply FClosedResourceIn_insert_fresh_atom_env.
    - rewrite dom_insert_L.
      intros Hin.
      apply elem_of_union in Hin as [Hin|Hin].
      + apply elem_of_singleton in Hin. exact (Hxy Hin).
      + exact (Hx Hin).
    - assert (<[y := Ty]> (<[x := Tx]> Δ) =
              <[x := Tx]> (<[y := Ty]> Δ)) as Hperm.
      {
        apply map_eq. intros z.
        rewrite !lookup_insert.
        repeat case_decide; subst; try congruence; reflexivity.
      }
      rewrite <- Hperm. exact Hclosed_new.
  }
  apply Hpost.
  eapply res_models_impl_elim; [exact Hbody | exact Hclosed_old].
Qed.

Lemma formula_scoped_FExprContBody_inner Σ T e Q (m : WfWorld) :
  formula_scoped_in_world ∅ m (FExprContBody Σ T e Q) ->
  formula_scoped_in_world ∅ m
    (FImpl
      (FExprResultAtLvar (dom (typed_lty_env_bind Σ T))
        (↑[0] e) (LVBound 0))
      (Q (typed_lty_env_bind Σ T))).
Proof.
  unfold formula_scoped_in_world, FExprContBody, FForallTypedBody.
  cbn [formula_fv]. set_solver.
Qed.

Lemma FExprContBody_insert_fresh_atom_env_map
    (Δ : gmap atom ty) x Tx Ty e Q Q' (m : WfWorld) :
  x ∉ dom Δ ->
  formula_scoped_in_world ∅ m
    (FExprContBody (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty e Q') ->
  (m ⊨ FExprResultAtLvar
      (dom (typed_lty_env_bind
        (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty))
      (↑[0] e) (LVBound 0) ->
    m ⊨ FExprResultAtLvar
      (dom (typed_lty_env_bind (atom_env_to_lty_env Δ) Ty))
      (↑[0] e) (LVBound 0)) ->
  (m ⊨ Q (typed_lty_env_bind (atom_env_to_lty_env Δ) Ty) ->
    m ⊨ Q' (typed_lty_env_bind
      (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty)) ->
  m ⊨ FExprContBody (atom_env_to_lty_env Δ) Ty e Q ->
  m ⊨ FExprContBody
    (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty e Q'.
Proof.
  intros Hx Hscope Hante Hpost Hbody.
  unfold FExprContBody.
  eapply FForallTypedBody_insert_fresh_atom_env; [exact Hx | exact Hscope | | exact Hbody].
  intros Hclosed_new Himpl_old.
  eapply res_models_impl_map.
  - apply formula_scoped_FExprContBody_inner. exact Hscope.
  - exact Hante.
  - exact Hpost.
  - exact Himpl_old.
Qed.

Lemma FExprContIn_insert_fresh_atom_env_map
    (Δ : gmap atom ty) x Tx Ty e Q Q' (m : WfWorld) :
  formula_scoped_in_world ∅ m
    (FExprContIn (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty e Q') ->
  (∃ L : aset,
    world_dom (m : World) ⊆ L ∧
    ∀ y F my,
      y ∉ L ->
      forall_extension_shape (world_dom (m : World)) y F ->
      m #> F ~~> my ->
      my ⊨ formula_open 0 y
        (FExprContBody (atom_env_to_lty_env Δ) Ty e Q) ->
      my ⊨ formula_open 0 y
        (FExprContBody (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty e Q')) ->
  m ⊨ FExprContIn (atom_env_to_lty_env Δ) Ty e Q ->
  m ⊨ FExprContIn (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty e Q'.
Proof.
  intros Hscope Hmap Hforall.
  unfold FExprContIn in *.
  pose proof (res_models_with_store_fuel_scoped _ ∅ m
    (FForall (FExprContBody (atom_env_to_lty_env Δ) Ty e Q))
    Hforall) as Hscope_old.
  eapply res_models_forall_by_extension_map; eauto.
Qed.

Lemma FExprContIn_insert_fresh_atom_env_const
    (Δ : gmap atom ty) x Tx Ty e φ (m : WfWorld) :
  x ∉ dom Δ ->
  x ∉ fv_tm e ->
  m ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := Tx]> Δ)) ->
  m ⊨ FExprContIn (atom_env_to_lty_env Δ) Ty e (fun _ => φ) ->
  m ⊨ FExprContIn
    (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty e (fun _ => φ).
Proof.
  (* Constant-continuation insert for the CTOver/CTUnder branches of the
     denotation induction.  The old opened/drop-result derivation has been
     moved to [LemmasObligationExprCont.legacy.v]; the current main line only
     needs this bridge as an interface while the TLet route is being shaped. *)
Admitted.

Lemma lvars_to_atoms_empty_empty :
  lvars_to_atoms ∅ (∅ : lvset) = ∅.
Proof.
  apply set_eq. intros x.
  rewrite lvars_to_atoms_elem. set_solver.
Qed.

Lemma lvars_to_atoms_empty_singleton_free x :
  lvars_to_atoms ∅ ({[LVFree x]} : lvset) = {[x]}.
Proof.
  apply set_eq. intros y.
  rewrite lvars_to_atoms_elem.
  split.
  - intros [[k|z] [Hv Hatom]]; cbn [logic_var_to_atom] in Hatom.
    + rewrite lookup_empty in Hatom. discriminate.
    + apply elem_of_singleton in Hv. inversion Hv. subst.
      inversion Hatom. set_solver.
  - intros Hy.
    apply elem_of_singleton in Hy. subst y.
    exists (LVFree x). split; [set_solver | reflexivity].
Qed.

Lemma lvars_to_atoms_empty_singleton_bound k :
  lvars_to_atoms ∅ ({[LVBound k]} : lvset) = ∅.
Proof.
  apply set_eq. intros x.
  rewrite lvars_to_atoms_elem.
  split; [| set_solver].
  intros [[j|y] [Hv Hatom]]; cbn [logic_var_to_atom] in Hatom.
  - rewrite lookup_empty in Hatom. discriminate.
  - apply elem_of_singleton in Hv. discriminate.
Qed.

Lemma lty_env_insert_free_lvars_fv (Γ : lty_env) x (T : ty) :
  lvars_fv (dom (<[LVFree x := T]> Γ)) =
  lvars_fv (dom Γ) ∪ {[x]}.
Proof.
  rewrite (dom_insert_L (M:=gmap logic_var) (A:=ty) Γ (LVFree x) T).
  rewrite lvars_fv_union, lvars_fv_singleton_free.
  set_solver.
Qed.

Lemma lvars_to_atoms_empty_open_superset k x D :
  lvars_to_atoms ∅ D ⊆ lvars_to_atoms ∅ (lvars_open k x D).
Proof.
  intros a Ha.
  apply lvars_to_atoms_elem in Ha as [[n|y] [Hv Hatom]];
    cbn [logic_var_to_atom] in Hatom.
  - rewrite lookup_empty in Hatom. discriminate.
  - inversion Hatom. subst y.
    apply lvars_to_atoms_elem.
    exists (LVFree a). split.
    + unfold lvars_open. apply elem_of_map.
      exists (LVFree a). split; [reflexivity | exact Hv].
    + reflexivity.
Qed.

Lemma value_tm_lvars_at_succ_atoms_subset :
  (∀ v d,
    lvars_to_atoms ∅ (value_lvars_at (S d) v) ⊆
    lvars_to_atoms ∅ (value_lvars_at d v)) *
  (∀ e d,
    lvars_to_atoms ∅ (tm_lvars_at (S d) e) ⊆
    lvars_to_atoms ∅ (tm_lvars_at d e)).
Proof.
  apply value_tm_mutind; cbn [value_lvars_at tm_lvars_at]; intros.
  - set_solver.
  - set_solver.
  - cbn [logic_var_at_depth].
    destruct (decide (S d <= n)) as [Hsn|Hsn];
      destruct (decide (d <= n)) as [Hdn|Hdn];
      rewrite ?lvars_to_atoms_empty_singleton_bound; set_solver.
  - apply H.
  - apply H.
  - apply H.
  - pose proof (H d) as H1.
    pose proof (H0 (S d)) as H2.
    rewrite !lvars_to_atoms_empty_union.
    set_solver.
  - apply H.
  - pose proof (H d) as H1.
    pose proof (H0 d) as H2.
    rewrite !lvars_to_atoms_empty_union.
    set_solver.
  - pose proof (H d) as H2.
    pose proof (H0 d) as H3.
    pose proof (H1 d) as H4.
    rewrite !lvars_to_atoms_empty_union.
    set_solver.
Qed.

Lemma value_lvars_body_open_atoms_subset x v :
  lvars_to_atoms ∅ (value_lvars_at 1 v) ⊆
  lvars_to_atoms ∅ (value_lvars (v ^^ x)).
Proof.
  unfold value_lvars.
  change (v ^^ x) with ({0 ~> x} v).
  change (value_lvars_at 0 ({0 ~> x} v))
    with (value_lvars_at 0 ({0 + 0 ~> x} v)).
  rewrite value_lvars_at_open.
  etransitivity.
  - exact (fst value_tm_lvars_at_succ_atoms_subset v 0).
  - apply lvars_to_atoms_empty_open_superset.
Qed.

Lemma tm_lvars_body_open_atoms_subset x e :
  lvars_to_atoms ∅ (tm_lvars_at 1 e) ⊆
  lvars_to_atoms ∅ (tm_lvars (e ^^ x)).
Proof.
  unfold tm_lvars.
  change (e ^^ x) with ({0 ~> x} e).
  change (tm_lvars_at 0 ({0 ~> x} e))
    with (tm_lvars_at 0 ({0 + 0 ~> x} e)).
  rewrite tm_lvars_at_open.
  etransitivity.
  - exact (snd value_tm_lvars_at_succ_atoms_subset e 0).
  - apply lvars_to_atoms_empty_open_superset.
Qed.

Scheme basic_value_lvar_ind' := Induction for basic_value_lvar Sort Prop
with basic_typing_lvar_ind' := Induction for basic_typing_lvar Sort Prop.
Combined Scheme basic_lvar_mutind
  from basic_value_lvar_ind', basic_typing_lvar_ind'.

Lemma value_swap_atom_open_fresh_to x y v :
  x ∉ fv_value v ->
  y ∉ fv_value v ->
  x <> y ->
  value_swap_atom y x (v ^^ y) = v ^^ x.
Proof.
  intros Hx Hy Hxy.
  symmetry.
  change (v ^^ x) with (open_value 0 (vfvar x) v).
  rewrite <- (value_swap_atom_fresh y x v Hy Hx) at 1.
  rewrite open_value_swap_atom.
  replace (atom_swap y x x) with y by
    (unfold atom_swap; repeat destruct decide; congruence).
  reflexivity.
Qed.

Lemma tm_swap_atom_open_fresh_to x y e :
  x ∉ fv_tm e ->
  y ∉ fv_tm e ->
  x <> y ->
  tm_swap_atom y x (e ^^ y) = e ^^ x.
Proof.
  intros Hx Hy Hxy.
  symmetry.
  change (e ^^ x) with (open_tm 0 (vfvar x) e).
  rewrite <- (tm_swap_atom_fresh y x e Hy Hx) at 1.
  rewrite open_tm_swap_atom.
  replace (atom_swap y x x) with y by
    (unfold atom_swap; repeat destruct decide; congruence).
  reflexivity.
Qed.

Lemma basic_value_typing_lvar_swap :
  (∀ Γ v T x y,
    basic_value_lvar Γ v T ->
    basic_value_lvar (lty_env_swap x y Γ) (value_swap_atom x y v) T) /\
  (∀ Γ e T x y,
    basic_typing_lvar Γ e T ->
    basic_typing_lvar (lty_env_swap x y Γ) (tm_swap_atom x y e) T).
Proof.
  assert (Hmut :
    (∀ Γ v T,
      basic_value_lvar Γ v T ->
      ∀ x y,
        basic_value_lvar (lty_env_swap x y Γ) (value_swap_atom x y v) T) /\
    (∀ Γ e T,
      basic_typing_lvar Γ e T ->
      ∀ x y,
        basic_typing_lvar (lty_env_swap x y Γ) (tm_swap_atom x y e) T)).
  2:{
    split; intros Γ a T x y Hder; [eapply (proj1 Hmut) | eapply (proj2 Hmut)];
      exact Hder.
  }
  apply basic_lvar_mutind; intros; cbn [value_swap_atom tm_swap_atom].
  - constructor.
  - econstructor.
    match goal with
    | |- lty_env_swap ?sx ?sy ?Γ0 !! LVFree (atom_swap ?sx ?sy ?z) = Some _ =>
        change (LVFree (atom_swap sx sy z)) with
          (logic_var_swap sx sy (LVFree z));
        rewrite lty_env_swap_lookup
    end.
    assumption.
  - econstructor.
    match goal with
    | |- lty_env_swap ?sx ?sy ?Γ0 !! LVBound ?k = Some _ =>
        change (LVBound k) with (logic_var_swap sx sy (LVBound k));
        rewrite lty_env_swap_lookup
    end.
    assumption.
  - eapply BasicLV_Lam. intros z Hz.
    change (basic_typing_lvar (<[LVFree z:=Tx]> (lty_env_swap x y Γ))
      (open_tm 0 (vfvar z) (tm_swap_atom x y e)) T).
    rewrite open_tm_swap_atom.
    replace (<[LVFree z:=Tx]> (lty_env_swap x y Γ))
      with (lty_env_swap x y
        (<[LVFree (atom_swap x y z):=Tx]> Γ)).
    + apply H.
      rewrite lty_env_swap_atom_dom in Hz.
      intros Hbad. apply Hz.
      rewrite elem_of_aset_swap.
      exact Hbad.
    + rewrite lty_env_swap_insert.
      replace (logic_var_swap x y (LVFree (atom_swap x y z)))
        with (LVFree z).
      * reflexivity.
      * cbn [logic_var_swap]. f_equal.
        unfold atom_swap. repeat destruct decide; congruence.
  - lazymatch goal with
    | Hbody : ∀ z, z ∉ ?Lbody -> _ |- _ =>
        eapply BasicLV_Fix with (L := aset_swap x y Lbody)
    end.
    intros z Hz.
    change (basic_value_lvar (<[LVFree z:=sx]> (lty_env_swap x y Γ))
      (open_value 0 (vfvar z) (value_swap_atom x y vf))
      ((sx →ₜ T) →ₜ T)).
    rewrite open_value_swap_atom.
    replace (<[LVFree z:=sx]> (lty_env_swap x y Γ))
      with (lty_env_swap x y
        (<[LVFree (atom_swap x y z):=sx]> Γ)).
    + apply H. intros Hbad. apply Hz.
      rewrite elem_of_aset_swap. exact Hbad.
    + rewrite lty_env_swap_insert.
      replace (logic_var_swap x y (LVFree (atom_swap x y z)))
        with (LVFree z).
      * reflexivity.
      * cbn [logic_var_swap]. f_equal.
        unfold atom_swap. repeat destruct decide; congruence.
  - econstructor. apply H.
  - eapply BasicLT_Let.
    + apply H.
    + intros z Hz.
      change (basic_typing_lvar (<[LVFree z:=T1]> (lty_env_swap x y Γ))
        (open_tm 0 (vfvar z) (tm_swap_atom x y e2)) T2).
      rewrite open_tm_swap_atom.
      replace (<[LVFree z:=T1]> (lty_env_swap x y Γ))
        with (lty_env_swap x y
          (<[LVFree (atom_swap x y z):=T1]> Γ)).
      * apply H0.
        rewrite lty_env_swap_atom_dom in Hz.
        intros Hbad. apply Hz.
        rewrite elem_of_aset_swap.
        exact Hbad.
      * rewrite lty_env_swap_insert.
        replace (logic_var_swap x y (LVFree (atom_swap x y z)))
          with (LVFree z).
        -- reflexivity.
        -- cbn [logic_var_swap]. f_equal.
           unfold atom_swap. repeat destruct decide; congruence.
  - econstructor; eauto; set_solver.
  - econstructor; eauto; set_solver.
  - econstructor; eauto.
Qed.

Lemma basic_value_lvar_swap Γ v T x y :
  basic_value_lvar Γ v T ->
  basic_value_lvar (lty_env_swap x y Γ) (value_swap_atom x y v) T.
Proof.
  exact (proj1 basic_value_typing_lvar_swap Γ v T x y).
Qed.

Lemma basic_typing_lvar_swap Γ e T x y :
  basic_typing_lvar Γ e T ->
  basic_typing_lvar (lty_env_swap x y Γ) (tm_swap_atom x y e) T.
Proof.
  exact (proj2 basic_value_typing_lvar_swap Γ e T x y).
Qed.

Lemma basic_value_typing_lvar_weaken_free :
  (∀ Γ v T x Tx,
    x ∉ lty_env_atom_dom Γ ->
    basic_value_lvar Γ v T ->
    basic_value_lvar (<[LVFree x := Tx]> Γ) v T) /\
  (∀ Γ e T x Tx,
    x ∉ lty_env_atom_dom Γ ->
    basic_typing_lvar Γ e T ->
    basic_typing_lvar (<[LVFree x := Tx]> Γ) e T).
Proof.
  assert (Hmut :
    (∀ Γ v T,
      basic_value_lvar Γ v T ->
      ∀ x Tx, x ∉ lty_env_atom_dom Γ ->
        basic_value_lvar (<[LVFree x := Tx]> Γ) v T) /\
    (∀ Γ e T,
      basic_typing_lvar Γ e T ->
      ∀ x Tx, x ∉ lty_env_atom_dom Γ ->
        basic_typing_lvar (<[LVFree x := Tx]> Γ) e T)).
  2:{
    split; intros Γ a T x Tx Hfresh Hder;
      [eapply (proj1 Hmut) | eapply (proj2 Hmut)]; eauto.
  }
  apply basic_lvar_mutind; intros.
  - constructor.
  - econstructor.
    match goal with
    | Hlookup : ?Γ !! LVFree ?y = Some ?T,
      Hfresh : ?x ∉ lty_env_atom_dom ?Γ
      |- <[LVFree ?x := _]> ?Γ !! LVFree ?y = Some ?T =>
        destruct (decide (x = y)) as [-> | Hne]
    end.
    + exfalso.
      match goal with
      | Hlookup : Γ !! LVFree ?y = Some _,
        Hfresh : ?y ∉ lty_env_atom_dom Γ |- _ =>
          apply Hfresh; unfold lty_env_atom_dom;
          apply lvars_fv_elem; apply elem_of_dom; eexists; exact Hlookup
      end.
    + match goal with
      | Hlookup : ?Γ !! LVFree ?y = Some ?T,
        Hne : ?x <> ?y |- <[LVFree ?x := ?Tx]> ?Γ !! LVFree ?y = Some ?T =>
          rewrite (lookup_insert_ne Γ (LVFree x) (LVFree y) Tx) by congruence;
          exact Hlookup
      end.
  - econstructor.
    match goal with
    | Hlookup : ?Γ !! LVBound ?k = Some ?T
      |- <[LVFree ?x := ?Tx]> ?Γ !! LVBound ?k = Some ?T =>
        rewrite (lookup_insert_ne Γ (LVFree x) (LVBound k) Tx) by congruence;
        exact Hlookup
    end.
  - eapply BasicLV_Lam. intros z Hz.
    replace (<[LVFree z := Tx]> (<[LVFree x := Tx0]> Γ))
      with (<[LVFree x := Tx0]> (<[LVFree z := Tx]> Γ)).
    + apply H.
      * unfold lty_env_atom_dom in *.
        rewrite lty_env_insert_free_lvars_fv in Hz. set_solver.
      * unfold lty_env_atom_dom in *.
        rewrite lty_env_insert_free_lvars_fv in Hz.
        rewrite lty_env_insert_free_lvars_fv. set_solver.
    + symmetry. apply lty_env_insert_free_comm.
      intros ->. apply Hz.
      unfold lty_env_atom_dom.
      rewrite lty_env_insert_free_lvars_fv. set_solver.
  - eapply BasicLV_Fix with (L := L ∪ {[x]}).
    intros z Hz.
    replace (<[LVFree z := sx]> (<[LVFree x := Tx]> Γ))
      with (<[LVFree x := Tx]> (<[LVFree z := sx]> Γ)).
    + apply H.
      * set_solver.
      * unfold lty_env_atom_dom in *.
        rewrite lty_env_insert_free_lvars_fv.
        set_solver.
    + symmetry. apply lty_env_insert_free_comm.
      intros ->. apply Hz. set_solver.
  - econstructor. eauto.
  - eapply BasicLT_Let.
    + eauto.
    + intros z Hz.
      replace (<[LVFree z := T1]> (<[LVFree x := Tx]> Γ))
        with (<[LVFree x := Tx]> (<[LVFree z := T1]> Γ)).
      * apply H0.
        -- unfold lty_env_atom_dom in *.
           rewrite lty_env_insert_free_lvars_fv in Hz. set_solver.
        -- unfold lty_env_atom_dom in *.
           rewrite lty_env_insert_free_lvars_fv in Hz.
           rewrite lty_env_insert_free_lvars_fv. set_solver.
      * symmetry. apply lty_env_insert_free_comm.
        intros ->. apply Hz.
        unfold lty_env_atom_dom.
        rewrite lty_env_insert_free_lvars_fv. set_solver.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma basic_typing_lvar_weaken_free Γ e T x Tx :
  x ∉ lty_env_atom_dom Γ ->
  basic_typing_lvar Γ e T ->
  basic_typing_lvar (<[LVFree x := Tx]> Γ) e T.
Proof.
  exact (proj2 basic_value_typing_lvar_weaken_free Γ e T x Tx).
Qed.

Lemma basic_choice_ty_lvar_drop_insert_fresh_free D x τ :
  x ∉ fv_cty τ ->
  basic_choice_ty_lvar (D ∪ {[LVFree x]}) τ ->
  basic_choice_ty_lvar D τ.
Proof.
  revert D x.
  induction τ; intros D x Hfresh Hbasic;
    inversion Hbasic; subst; cbn [fv_cty] in Hfresh.
  - constructor.
    destruct φ as [Dφ pφ]; cbn [qual_dom qual_vars] in *.
    unfold basic_qualifier_lvar_body in *.
    match goal with
    | Hq : qual_vars _ ⊆ _ |- _ =>
        rewrite lvars_shift_union_free_singleton in Hq;
        intros u Hu;
        specialize (Hq u Hu);
        repeat rewrite elem_of_union in Hq;
        destruct Hq as [[HuD | Hux] | Hu0]
    end.
    + set_solver.
    + apply elem_of_singleton in Hux. subst.
      exfalso. apply Hfresh.
      rewrite lvars_fv_elem. exact Hu.
    + set_solver.
  - constructor.
    destruct φ as [Dφ pφ]; cbn [qual_dom qual_vars] in *.
    unfold basic_qualifier_lvar_body in *.
    match goal with
    | Hq : qual_vars _ ⊆ _ |- _ =>
        rewrite lvars_shift_union_free_singleton in Hq;
        intros u Hu;
        specialize (Hq u Hu);
        repeat rewrite elem_of_union in Hq;
        destruct Hq as [[HuD | Hux] | Hu0]
    end.
    + set_solver.
    + apply elem_of_singleton in Hux. subst.
      exfalso. apply Hfresh.
      rewrite lvars_fv_elem. exact Hu.
    + set_solver.
  - apply not_elem_of_union in Hfresh as [Hfresh1 Hfresh2].
    econstructor; eauto.
  - apply not_elem_of_union in Hfresh as [Hfresh1 Hfresh2].
    econstructor; eauto.
  - apply not_elem_of_union in Hfresh as [Hfresh1 Hfresh2].
    econstructor; eauto.
  - apply not_elem_of_union in Hfresh as [Hfreshx Hfreshbody].
    econstructor.
    + eapply IHτ1; eauto.
    + eapply IHτ2 with (D := lvars_shift D ∪ {[LVBound 0]})
        (x := x).
      * exact Hfreshbody.
      * eapply basic_choice_ty_lvar_mono.
        2:{ eassumption. }
        rewrite lvars_shift_union_free_singleton.
        set_solver.
  - apply not_elem_of_union in Hfresh as [Hfreshx Hfreshbody].
    econstructor.
    + eapply IHτ1; eauto.
    + eapply IHτ2 with (D := lvars_shift D ∪ {[LVBound 0]})
        (x := x).
      * exact Hfreshbody.
      * eapply basic_choice_ty_lvar_mono.
        2:{ eassumption. }
        rewrite lvars_shift_union_free_singleton.
        set_solver.
Qed.

Lemma basic_choice_ty_lvar_drop_insert_fresh_atom_env
    (Δ : gmap atom ty) x T τ :
  x ∉ dom Δ ->
  x ∉ fv_cty τ ->
  basic_choice_ty_lvar (dom (atom_env_to_lty_env (<[x := T]> Δ))) τ ->
  basic_choice_ty_lvar (dom (atom_env_to_lty_env Δ)) τ.
Proof.
  intros Hx_dom Hxτ Hbasic.
  rewrite !atom_env_to_lty_env_dom in *.
  rewrite dom_insert_L in Hbasic.
  replace (lvars_of_atoms ({[x]} ∪ dom Δ))
    with (lvars_of_atoms (dom Δ) ∪ {[LVFree x]}) in Hbasic.
  - eapply basic_choice_ty_lvar_drop_insert_fresh_free; eauto.
  - unfold lvars_of_atoms.
    rewrite set_map_union_L, set_map_singleton_L.
    set_solver.
Qed.

Lemma basic_value_typing_lvar_drop_insert_fresh_free :
  (∀ Γ v T x Tx,
    x ∉ lty_env_atom_dom Γ ->
    x ∉ fv_value v ->
    basic_value_lvar (<[LVFree x := Tx]> Γ) v T ->
    basic_value_lvar Γ v T) /\
  (∀ Γ e T x Tx,
    x ∉ lty_env_atom_dom Γ ->
    x ∉ fv_tm e ->
    basic_typing_lvar (<[LVFree x := Tx]> Γ) e T ->
    basic_typing_lvar Γ e T).
Proof.
  assert (Hmut :
    (∀ Γx v T,
      basic_value_lvar Γx v T ->
      ∀ Γ x Tx,
        Γx = <[LVFree x := Tx]> Γ ->
        x ∉ lty_env_atom_dom Γ ->
        x ∉ fv_value v ->
        basic_value_lvar Γ v T) /\
    (∀ Γx e T,
      basic_typing_lvar Γx e T ->
      ∀ Γ x Tx,
        Γx = <[LVFree x := Tx]> Γ ->
        x ∉ lty_env_atom_dom Γ ->
        x ∉ fv_tm e ->
        basic_typing_lvar Γ e T)).
  2:{
    split; intros Γ a T x Tx Hfresh Hnotin Hder;
      [eapply (proj1 Hmut) | eapply (proj2 Hmut)];
      eauto.
  }
  apply basic_lvar_mutind; intros; subst; cbn [fv_value fv_tm] in *.
  - constructor.
  - eapply BasicLV_FVar.
    match goal with
    | Hlookup : (<[?k := ?Tx]> ?Γ) !! ?v = Some ?T |- ?Γ !! ?v = Some ?T =>
        rewrite (lookup_insert_ne Γ k v Tx) in Hlookup by
          (intros Heq; inversion Heq; subst; set_solver);
        exact Hlookup
    end.
  - eapply BasicLV_BVar.
    match goal with
    | Hlookup : (<[?k := ?Tx]> ?Γ) !! ?v = Some ?T |- ?Γ !! ?v = Some ?T =>
        rewrite (lookup_insert_ne Γ k v Tx) in Hlookup by congruence;
        exact Hlookup
    end.
  - eapply BasicLV_Lam. intros z Hz.
    destruct (decide (z = x)) as [->|Hzx].
    + pose (y := fresh_for
        (lty_env_atom_dom Γ0 ∪ fv_tm e ∪ {[x]})).
      assert (Hy : y ∉ lty_env_atom_dom Γ0 ∪ fv_tm e ∪ {[x]})
        by (subst y; apply fresh_for_not_in).
      assert (Hy_src : y ∉ lty_env_atom_dom (<[LVFree x := Tx0]> Γ0)).
      {
        unfold lty_env_atom_dom in *.
        rewrite lty_env_insert_free_lvars_fv. set_solver.
      }
      match goal with
      | Hsrc : ∀ z0 : atom,
          z0 ∉ lty_env_atom_dom (<[LVFree x := Tx0]> Γ0) ->
          basic_typing_lvar
            (<[LVFree z0 := Tx]> (<[LVFree x := Tx0]> Γ0))
            (e ^^ z0) T
        |- _ =>
          pose proof (Hsrc y Hy_src) as Hybody
      end.
      match goal with
      | IH : ∀ z0 : atom,
          z0 ∉ lty_env_atom_dom (<[LVFree x := Tx0]> Γ0) ->
          ∀ Γ' x' Tx',
            <[LVFree z0 := Tx]> (<[LVFree x := Tx0]> Γ0) =
            <[LVFree x' := Tx']> Γ' ->
            x' ∉ lty_env_atom_dom Γ' ->
            x' ∉ fv_tm (e ^^ z0) ->
            basic_typing_lvar Γ' (e ^^ z0) T
        |- _ =>
          pose proof (IH y Hy_src (<[LVFree y := Tx]> Γ0) x Tx0) as Hdrop
      end.
      assert (<[LVFree y := Tx]> (<[LVFree x := Tx0]> Γ0) =
        <[LVFree x := Tx0]> (<[LVFree y := Tx]> Γ0)) as Henv.
      {
        symmetry. apply lty_env_insert_free_comm. set_solver.
      }
      specialize (Hdrop Henv).
      assert (Hx_fresh_y : x ∉ lty_env_atom_dom (<[LVFree y := Tx]> Γ0)).
      {
        unfold lty_env_atom_dom in *.
        rewrite lty_env_insert_free_lvars_fv. set_solver.
      }
      specialize (Hdrop Hx_fresh_y).
      assert (Hx_body_y : x ∉ fv_tm (e ^^ y)).
      {
        pose proof (open_fv_tm e (vfvar y) 0) as Hopen.
        cbn [fv_value] in Hopen. set_solver.
      }
      specialize (Hdrop Hx_body_y).
      pose proof (basic_typing_lvar_swap
        (<[LVFree y := Tx]> Γ0) (e ^^ y) T y x Hdrop) as Hswap.
      rewrite lty_env_swap_insert_fresh_to in Hswap by set_solver.
      rewrite (tm_swap_atom_open_fresh_to x y e) in Hswap by set_solver.
      exact Hswap.
    + assert (Hz_src : z ∉ lty_env_atom_dom (<[LVFree x := Tx0]> Γ0)).
      {
        unfold lty_env_atom_dom in *.
        rewrite lty_env_insert_free_lvars_fv. set_solver.
      }
      match goal with
      | Hsrc : ∀ z0 : atom,
          z0 ∉ lty_env_atom_dom (<[LVFree x := Tx0]> Γ0) ->
          basic_typing_lvar
            (<[LVFree z0 := Tx]> (<[LVFree x := Tx0]> Γ0))
            (e ^^ z0) T
        |- _ =>
          pose proof (Hsrc z Hz_src) as Hzbody
      end.
      match goal with
      | IH : ∀ z0 : atom,
          z0 ∉ lty_env_atom_dom (<[LVFree x := Tx0]> Γ0) ->
          ∀ Γ' x' Tx',
            <[LVFree z0 := Tx]> (<[LVFree x := Tx0]> Γ0) =
            <[LVFree x' := Tx']> Γ' ->
            x' ∉ lty_env_atom_dom Γ' ->
            x' ∉ fv_tm (e ^^ z0) ->
            basic_typing_lvar Γ' (e ^^ z0) T
        |- _ =>
          pose proof (IH z Hz_src (<[LVFree z := Tx]> Γ0) x Tx0) as Hdrop
      end.
      assert (<[LVFree z := Tx]> (<[LVFree x := Tx0]> Γ0) =
        <[LVFree x := Tx0]> (<[LVFree z := Tx]> Γ0)) as Henv.
      {
        symmetry. apply lty_env_insert_free_comm. set_solver.
      }
      specialize (Hdrop Henv).
      assert (Hx_fresh_z : x ∉ lty_env_atom_dom (<[LVFree z := Tx]> Γ0)).
      {
        unfold lty_env_atom_dom in *.
        rewrite lty_env_insert_free_lvars_fv. set_solver.
      }
      specialize (Hdrop Hx_fresh_z).
      assert (Hx_body_z : x ∉ fv_tm (e ^^ z)).
      {
        pose proof (open_fv_tm e (vfvar z) 0) as Hopen.
        cbn [fv_value] in Hopen. set_solver.
      }
      exact (Hdrop Hx_body_z).
  - eapply BasicLV_Fix with (L := L ∪ {[x]}). intros z Hz.
    match goal with
    | Hsrc : ∀ z0 : atom,
        z0 ∉ L ->
        basic_value_lvar
          (<[LVFree z0 := sx]> (<[LVFree x := Tx]> Γ0))
          (vf ^^ z0) ((sx →ₜ T) →ₜ T)
      |- _ =>
        pose proof (Hsrc z ltac:(set_solver)) as Hzbody
    end.
    match goal with
    | IH : ∀ z0 : atom,
        z0 ∉ L ->
        ∀ Γ' x' Tx',
          <[LVFree z0 := sx]> (<[LVFree x := Tx]> Γ0) =
          <[LVFree x' := Tx']> Γ' ->
          x' ∉ lty_env_atom_dom Γ' ->
          x' ∉ fv_value (vf ^^ z0) ->
          basic_value_lvar Γ' (vf ^^ z0) ((sx →ₜ T) →ₜ T)
      |- _ =>
        pose proof (IH z ltac:(set_solver) (<[LVFree z := sx]> Γ0) x Tx) as Hdrop
    end.
    assert (<[LVFree z := sx]> (<[LVFree x := Tx]> Γ0) =
      <[LVFree x := Tx]> (<[LVFree z := sx]> Γ0)) as Henv.
    {
      symmetry. apply lty_env_insert_free_comm. set_solver.
    }
    specialize (Hdrop Henv).
    assert (Hx_fresh_z : x ∉ lty_env_atom_dom (<[LVFree z := sx]> Γ0)).
    {
      unfold lty_env_atom_dom in *.
      rewrite lty_env_insert_free_lvars_fv. set_solver.
    }
    specialize (Hdrop Hx_fresh_z).
    assert (Hx_body_z : x ∉ fv_value (vf ^^ z)).
    {
      pose proof (open_fv_value vf (vfvar z) 0) as Hopen.
      cbn [fv_value] in Hopen. set_solver.
    }
    exact (Hdrop Hx_body_z).
  - econstructor. eapply H; eauto.
  - eapply BasicLT_Let.
    + eapply H; eauto. set_solver.
    + intros z Hz.
      destruct (decide (z = x)) as [->|Hzx].
      * pose (y := fresh_for
          (lty_env_atom_dom Γ0 ∪ fv_tm e2 ∪ {[x]})).
        assert (Hy : y ∉ lty_env_atom_dom Γ0 ∪ fv_tm e2 ∪ {[x]})
          by (subst y; apply fresh_for_not_in).
        assert (Hy_src : y ∉ lty_env_atom_dom (<[LVFree x := Tx]> Γ0)).
        {
          unfold lty_env_atom_dom in *.
          rewrite lty_env_insert_free_lvars_fv. set_solver.
        }
        match goal with
        | Hsrc : ∀ z0 : atom,
            z0 ∉ lty_env_atom_dom (<[LVFree x := Tx]> Γ0) ->
            basic_typing_lvar
              (<[LVFree z0 := T1]> (<[LVFree x := Tx]> Γ0))
              (e2 ^^ z0) T2
          |- _ =>
            pose proof (Hsrc y Hy_src) as Hybody
        end.
        match goal with
        | IH : ∀ z0 : atom,
            z0 ∉ lty_env_atom_dom (<[LVFree x := Tx]> Γ0) ->
            ∀ Γ' x' Tx',
              <[LVFree z0 := T1]> (<[LVFree x := Tx]> Γ0) =
              <[LVFree x' := Tx']> Γ' ->
              x' ∉ lty_env_atom_dom Γ' ->
              x' ∉ fv_tm (e2 ^^ z0) ->
              basic_typing_lvar Γ' (e2 ^^ z0) T2
          |- _ =>
            pose proof (IH y Hy_src (<[LVFree y := T1]> Γ0) x Tx) as Hdrop
        end.
        assert (<[LVFree y := T1]> (<[LVFree x := Tx]> Γ0) =
          <[LVFree x := Tx]> (<[LVFree y := T1]> Γ0)) as Henv.
        {
          symmetry. apply lty_env_insert_free_comm. set_solver.
        }
        specialize (Hdrop Henv).
        assert (Hx_fresh_y : x ∉ lty_env_atom_dom (<[LVFree y := T1]> Γ0)).
        {
          unfold lty_env_atom_dom in *.
          rewrite lty_env_insert_free_lvars_fv. set_solver.
        }
        specialize (Hdrop Hx_fresh_y).
        assert (Hx_body_y : x ∉ fv_tm (e2 ^^ y)).
        {
          pose proof (open_fv_tm e2 (vfvar y) 0) as Hopen.
          cbn [fv_value] in Hopen. set_solver.
        }
        specialize (Hdrop Hx_body_y).
        pose proof (basic_typing_lvar_swap
          (<[LVFree y := T1]> Γ0) (e2 ^^ y) T2 y x Hdrop) as Hswap.
        rewrite lty_env_swap_insert_fresh_to in Hswap by set_solver.
        rewrite (tm_swap_atom_open_fresh_to x y e2) in Hswap by set_solver.
        exact Hswap.
      * assert (Hz_src : z ∉ lty_env_atom_dom (<[LVFree x := Tx]> Γ0)).
        {
          unfold lty_env_atom_dom in *.
          rewrite lty_env_insert_free_lvars_fv. set_solver.
        }
        match goal with
        | Hsrc : ∀ z0 : atom,
            z0 ∉ lty_env_atom_dom (<[LVFree x := Tx]> Γ0) ->
            basic_typing_lvar
              (<[LVFree z0 := T1]> (<[LVFree x := Tx]> Γ0))
              (e2 ^^ z0) T2
          |- _ =>
            pose proof (Hsrc z Hz_src) as Hzbody
        end.
        match goal with
        | IH : ∀ z0 : atom,
            z0 ∉ lty_env_atom_dom (<[LVFree x := Tx]> Γ0) ->
            ∀ Γ' x' Tx',
              <[LVFree z0 := T1]> (<[LVFree x := Tx]> Γ0) =
              <[LVFree x' := Tx']> Γ' ->
              x' ∉ lty_env_atom_dom Γ' ->
              x' ∉ fv_tm (e2 ^^ z0) ->
              basic_typing_lvar Γ' (e2 ^^ z0) T2
          |- _ =>
            pose proof (IH z Hz_src (<[LVFree z := T1]> Γ0) x Tx) as Hdrop
        end.
        assert (<[LVFree z := T1]> (<[LVFree x := Tx]> Γ0) =
          <[LVFree x := Tx]> (<[LVFree z := T1]> Γ0)) as Henv.
        {
          symmetry. apply lty_env_insert_free_comm. set_solver.
        }
        specialize (Hdrop Henv).
        assert (Hx_fresh_z : x ∉ lty_env_atom_dom (<[LVFree z := T1]> Γ0)).
        {
          unfold lty_env_atom_dom in *.
          rewrite lty_env_insert_free_lvars_fv. set_solver.
        }
        specialize (Hdrop Hx_fresh_z).
        assert (Hx_body_z : x ∉ fv_tm (e2 ^^ z)).
        {
          pose proof (open_fv_tm e2 (vfvar z) 0) as Hopen.
          cbn [fv_value] in Hopen. set_solver.
        }
        exact (Hdrop Hx_body_z).
  - econstructor.
    + eassumption.
    + match goal with
      | IH : ∀ Γ' x' Tx',
          <[LVFree ?x := ?Tx]> ?Γ = <[LVFree x' := Tx']> Γ' ->
          x' ∉ lty_env_atom_dom Γ' ->
          x' ∉ fv_value ?v ->
          basic_value_lvar Γ' ?v _ |- basic_value_lvar ?Γ ?v _ =>
          eapply IH; [reflexivity | eassumption | set_solver]
      end.
  - econstructor.
    + match goal with
      | IH : ∀ Γ' x' Tx',
          <[LVFree ?x := ?Tx]> ?Γ = <[LVFree x' := Tx']> Γ' ->
          x' ∉ lty_env_atom_dom Γ' ->
          x' ∉ fv_value ?v ->
          basic_value_lvar Γ' ?v _ |- basic_value_lvar ?Γ ?v _ =>
          eapply IH; [reflexivity | eassumption | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ' x' Tx',
          <[LVFree ?x := ?Tx]> ?Γ = <[LVFree x' := Tx']> Γ' ->
          x' ∉ lty_env_atom_dom Γ' ->
          x' ∉ fv_value ?v ->
          basic_value_lvar Γ' ?v _ |- basic_value_lvar ?Γ ?v _ =>
          eapply IH; [reflexivity | eassumption | set_solver]
      end.
  - econstructor.
    + match goal with
      | IH : ∀ Γ' x' Tx',
          <[LVFree ?x := ?Tx]> ?Γ = <[LVFree x' := Tx']> Γ' ->
          x' ∉ lty_env_atom_dom Γ' ->
          x' ∉ fv_value ?v ->
          basic_value_lvar Γ' ?v _ |- basic_value_lvar ?Γ ?v _ =>
          eapply IH; [reflexivity | eassumption | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ' x' Tx',
          <[LVFree ?x := ?Tx]> ?Γ = <[LVFree x' := Tx']> Γ' ->
          x' ∉ lty_env_atom_dom Γ' ->
          x' ∉ fv_tm ?e ->
          basic_typing_lvar Γ' ?e _ |- basic_typing_lvar ?Γ ?e _ =>
          eapply IH; [reflexivity | eassumption | set_solver]
      end.
    + match goal with
      | IH : ∀ Γ' x' Tx',
          <[LVFree ?x := ?Tx]> ?Γ = <[LVFree x' := Tx']> Γ' ->
          x' ∉ lty_env_atom_dom Γ' ->
          x' ∉ fv_tm ?e ->
          basic_typing_lvar Γ' ?e _ |- basic_typing_lvar ?Γ ?e _ =>
          eapply IH; [reflexivity | eassumption | set_solver]
      end.
Qed.

Lemma basic_typing_lvar_drop_insert_fresh_free Γ x Tx e T :
  x ∉ lty_env_atom_dom Γ ->
  x ∉ fv_tm e ->
  basic_typing_lvar (<[LVFree x := Tx]> Γ) e T ->
  basic_typing_lvar Γ e T.
Proof.
  exact (proj2 basic_value_typing_lvar_drop_insert_fresh_free Γ e T x Tx).
Qed.

Lemma basic_typing_lvar_drop_insert_fresh_atom_env
    (Δ : gmap atom ty) x Tx e T :
  x ∉ dom Δ ->
  x ∉ fv_tm e ->
  basic_typing_lvar (atom_env_to_lty_env (<[x := Tx]> Δ)) e T ->
  basic_typing_lvar (atom_env_to_lty_env Δ) e T.
Proof.
  intros Hx_dom Hx_e Htyping.
  rewrite atom_env_to_lty_env_insert in Htyping by exact Hx_dom.
  eapply basic_typing_lvar_drop_insert_fresh_free.
  - unfold lty_env_atom_dom.
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
    exact Hx_dom.
  - exact Hx_e.
  - exact Htyping.
Qed.

Lemma basic_choice_ty_lvar_atom_env_of_basic
    (Δ : gmap atom ty) τ :
  basic_choice_ty (dom Δ) τ ->
  basic_choice_ty_lvar (dom (atom_env_to_lty_env Δ)) τ.
Proof.
  intros Hbasic.
  apply basic_choice_ty_lvar_of_lvars_subset.
  rewrite atom_env_to_lty_env_dom.
  intros u Hu.
  apply (lvars_of_atoms_mono _ _ ltac:(
    eapply basic_choice_ty_fv_subset; exact Hbasic)).
  apply lc_choice_ty_lvars_subset_atoms; [| exact Hu].
  eapply basic_choice_ty_lc. exact Hbasic.
Qed.

Lemma basic_choice_ty_open_arrow_body_cofinite
    (Δ : gmap atom ty) τx τ (L0 : gset atom) :
  basic_choice_ty (dom Δ) (CTArrow τx τ) ->
  ∃ L,
    L0 ⊆ L ∧
    ∀ y,
      y ∉ L ->
      basic_choice_ty (dom (<[y := erase_ty τx]> Δ)) ({0 ~> y} τ).
Proof.
  intros Hbasic.
  inversion Hbasic as [| | | | |D τx' τ' L Hτx Hbody|]; subst.
  exists (L0 ∪ L). split; [set_solver |].
  intros y Hy.
  replace (dom (<[y := erase_ty τx]> Δ)) with (dom Δ ∪ {[y]}).
  - apply Hbody. set_solver.
  - rewrite dom_insert_L. set_solver.
Qed.

Lemma basic_typing_lvar_atom_env_of_basic
    (Δ : gmap atom ty) e T :
  Δ ⊢ₑ e ⋮ T ->
  basic_typing_lvar (atom_env_to_lty_env Δ) e T.
Proof.
  assert (Hmut :
    (∀ Δ v T,
      Δ ⊢ᵥ v ⋮ T ->
      basic_value_lvar (atom_env_to_lty_env Δ) v T) /\
    (∀ Δ e T,
      Δ ⊢ₑ e ⋮ T ->
      basic_typing_lvar (atom_env_to_lty_env Δ) e T)).
  2:{ intros Htyped. exact (proj2 Hmut Δ e T Htyped). }
  apply has_type_mutind; intros.
  - constructor.
  - econstructor. rewrite atom_env_to_lty_env_lookup_free. assumption.
  - eapply BasicLV_Lam. intros x Hx.
    pose (y := fresh_for (L ∪ lty_env_atom_dom (atom_env_to_lty_env Γ)
      ∪ fv_tm e0 ∪ {[x]})).
    assert (Hyfresh :
      y ∉ L ∪ lty_env_atom_dom (atom_env_to_lty_env Γ) ∪ fv_tm e0 ∪ {[x]})
      by (subst y; apply fresh_for_not_in).
    assert (HxΓ : x ∉ dom Γ).
    { rewrite <- atom_env_to_lty_env_atom_dom. exact Hx. }
    assert (HyΓ : y ∉ dom Γ).
    { rewrite <- atom_env_to_lty_env_atom_dom. set_solver. }
    assert (Hxy : x <> y) by set_solver.
    pose proof (H y ltac:(set_solver)) as Hybody.
    pose proof (basic_typing_lvar_swap
      (atom_env_to_lty_env (<[y := s]> Γ)) (e0 ^^ y) T0 y x Hybody)
      as Hswap.
    rewrite lty_env_swap_atom_env_insert_fresh in Hswap by assumption.
    assert (Hxfv : x ∉ fv_tm e0).
    {
      intros Hbad.
      match goal with
      | Hopen : ∀ z : atom, z ∉ L -> <[z := s]> Γ ⊢ₑ e0 ^^ z ⋮ T0 |- _ =>
          pose proof (basic_typing_contains_fv_tm _ _ _ (Hopen y ltac:(set_solver)))
            as Hfvbody
      end.
      pose proof (open_fv_tm' e0 (vfvar y) 0) as Hopenfv.
      simpl in Hopenfv. rewrite dom_insert_L in Hfvbody.
      set_solver.
    }
    assert (Hswap_tm : tm_swap_atom y x (e0 ^^ y) = e0 ^^ x).
    { apply tm_swap_atom_open_fresh_to; set_solver. }
    rewrite Hswap_tm in Hswap.
    exact Hswap.
  - eapply BasicLV_Fix with (L := L ∪ lty_env_atom_dom (atom_env_to_lty_env Γ)).
    intros x Hx.
    pose proof (H x ltac:(set_solver)) as Hbody.
    rewrite atom_env_to_lty_env_insert in Hbody.
    + exact Hbody.
    + rewrite <- atom_env_to_lty_env_atom_dom. set_solver.
  - econstructor. apply H.
  - eapply BasicLT_Let.
    + apply H.
    + intros x Hx.
      pose (y := fresh_for (L ∪ lty_env_atom_dom (atom_env_to_lty_env Γ)
        ∪ fv_tm e2 ∪ {[x]})).
      assert (Hyfresh :
        y ∉ L ∪ lty_env_atom_dom (atom_env_to_lty_env Γ) ∪ fv_tm e2 ∪ {[x]})
        by (subst y; apply fresh_for_not_in).
      assert (HxΓ : x ∉ dom Γ).
      { rewrite <- atom_env_to_lty_env_atom_dom. exact Hx. }
      assert (HyΓ : y ∉ dom Γ).
      { rewrite <- atom_env_to_lty_env_atom_dom. set_solver. }
      assert (Hxy : x <> y) by set_solver.
      pose proof (H0 y ltac:(set_solver)) as Hybody.
      pose proof (basic_typing_lvar_swap
        (atom_env_to_lty_env (<[y := T1]> Γ)) (e2 ^^ y) T2 y x Hybody)
        as Hswap.
      rewrite lty_env_swap_atom_env_insert_fresh in Hswap by assumption.
      assert (Hxfv : x ∉ fv_tm e2).
      {
        intros Hbad.
        match goal with
        | Hopen : ∀ z : atom, z ∉ L -> <[z := T1]> Γ ⊢ₑ e2 ^^ z ⋮ T2 |- _ =>
            pose proof (basic_typing_contains_fv_tm _ _ _ (Hopen y ltac:(set_solver)))
              as Hfvbody
        end.
        pose proof (open_fv_tm' e2 (vfvar y) 0) as Hopenfv.
        simpl in Hopenfv. rewrite dom_insert_L in Hfvbody.
        set_solver.
      }
      assert (Hswap_tm : tm_swap_atom y x (e2 ^^ y) = e2 ^^ x).
      { apply tm_swap_atom_open_fresh_to; set_solver. }
      rewrite Hswap_tm in Hswap.
      exact Hswap.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma expr_total_lvar_insert_fresh_atom_env
    (Δ : gmap atom ty) x T e (m : WfWorld) :
  x ∉ dom Δ ∪ fv_tm e ->
  closed_resource_lvar (atom_env_to_lty_env (<[x := T]> Δ)) ∅ m ->
  expr_total_lvar (atom_env_to_lty_env Δ) e ∅ ∅ m ->
  expr_total_lvar (atom_env_to_lty_env (<[x := T]> Δ)) e ∅ ∅ m.
Proof.
  intros Hfresh Hclosed_big Htotal.
  unfold expr_total_lvar, expr_total_with_store in *.
  rewrite !lvars_to_atoms_empty_union.
  rewrite !atom_env_to_lty_env_dom, !lvars_to_atoms_of_atoms.
  rewrite dom_insert_L.
  destruct Htotal as [Hclosed Hsteps].
  unfold closed_resource_lvar in Hclosed_big.
  rewrite atom_env_to_lty_env_dom, lvars_to_atoms_of_atoms in Hclosed_big.
  rewrite dom_insert_L in Hclosed_big.
  assert (Hclosed_old_atoms :
    ∀ σ, (m : World) σ ->
      store_closed (store_restrict σ
        (dom Δ ∪ lvars_to_atoms ∅ (tm_lvars e)))).
  {
    intros σ Hσ.
    pose proof (Hclosed σ Hσ) as Hc.
    rewrite map_empty_union in Hc.
    rewrite lvars_to_atoms_empty_union in Hc.
    rewrite atom_env_to_lty_env_dom, lvars_to_atoms_of_atoms in Hc.
    exact Hc.
  }
  assert (Hclosed_old_fv :
    ∀ σ, (m : World) σ ->
      store_closed (store_restrict σ (dom Δ ∪ fv_tm e))).
  {
    intros σ Hσ.
    pose proof (Hclosed_old_atoms σ Hσ) as Hc.
    rewrite lvars_to_atoms_empty_eq_fv, tm_lvars_fv in Hc.
    exact Hc.
  }
  split.
  - intros σ Hσ.
    rewrite map_empty_union.
    replace (({[x]} ∪ dom Δ) ∪ lvars_to_atoms ∅ (tm_lvars e))
      with (({[x]} ∪ dom Δ) ∪
        (dom Δ ∪ lvars_to_atoms ∅ (tm_lvars e))) by set_solver.
    eapply store_closed_restrict_union_sets.
    + exact (Hclosed_big σ Hσ).
    + exact (Hclosed_old_atoms σ Hσ).
  - intros σ Hσ.
    destruct (Hsteps σ Hσ) as [vx Hvx].
    exists vx.
    rewrite map_empty_union in *.
    rewrite !open_tm_env_empty in *.
    rewrite lvars_to_atoms_empty_union in Hvx.
    rewrite atom_env_to_lty_env_dom, lvars_to_atoms_of_atoms in Hvx.
    rewrite lvars_to_atoms_empty_eq_fv, tm_lvars_fv in Hvx.
    rewrite lvars_to_atoms_empty_eq_fv; try rewrite tm_lvars_fv.
    assert (Hclosed_new :
      closed_env (store_restrict σ (({[x]} ∪ dom Δ) ∪ fv_tm e))).
    {
      destruct (store_closed_restrict_union_sets σ ({[x]} ∪ dom Δ)
        (dom Δ ∪ fv_tm e) (Hclosed_big σ Hσ) (Hclosed_old_fv σ Hσ))
        as [Hclosed_store _].
      replace (({[x]} ∪ dom Δ) ∪ fv_tm e)
        with (({[x]} ∪ dom Δ) ∪ (dom Δ ∪ fv_tm e)) by set_solver.
      exact Hclosed_store.
    }
    pose proof (subst_map_restrict_to_fv_from_superset e
      (dom Δ ∪ fv_tm e) σ ltac:(set_solver)
      (proj1 (Hclosed_old_fv σ Hσ))) as Hold.
    pose proof (subst_map_restrict_to_fv_from_superset e
      (({[x]} ∪ dom Δ) ∪ fv_tm e) σ ltac:(set_solver)
      Hclosed_new) as Hnew.
    rewrite <- Hold in Hvx.
    rewrite <- Hnew.
    exact Hvx.
Qed.

Lemma expr_total_lvar_drop_insert_fresh_atom_env
    (Δ : gmap atom ty) x T e (m : WfWorld) :
  x ∉ fv_tm e ->
  expr_total_lvar (atom_env_to_lty_env (<[x := T]> Δ)) e ∅ ∅ m ->
  expr_total_lvar (atom_env_to_lty_env Δ) e ∅ ∅ m.
Proof.
  intros Hfresh Htotal.
  unfold expr_total_lvar, expr_total_with_store in *.
  rewrite !atom_env_to_lty_env_dom in *.
  rewrite dom_insert_L in Htotal.
  rewrite !lvars_to_atoms_empty_union in *.
  rewrite !lvars_to_atoms_of_atoms in *.
  destruct Htotal as [Hclosed_big Hsteps_big].
  split.
  - intros σ Hσ.
    rewrite map_empty_union.
    pose proof (Hclosed_big σ Hσ) as Hclosed.
    rewrite map_empty_union in Hclosed.
    rewrite <- (store_restrict_twice_subset
      σ (({[x]} ∪ dom Δ) ∪ lvars_to_atoms ∅ (tm_lvars e))
        (dom Δ ∪ lvars_to_atoms ∅ (tm_lvars e))) by set_solver.
    apply store_closed_restrict. exact Hclosed.
  - intros σ Hσ.
    destruct (Hsteps_big σ Hσ) as [vx Hvx].
    exists vx.
    rewrite map_empty_union in *.
    rewrite !open_tm_env_empty in *.
    rewrite !lvars_to_atoms_empty_eq_fv in *; try rewrite tm_lvars_fv in *.
    assert (Hclosed_old :
      closed_env (store_restrict σ (dom Δ ∪ fv_tm e))).
    {
      pose proof (Hclosed_big σ Hσ) as Hclosed.
      rewrite map_empty_union in Hclosed.
      rewrite <- (store_restrict_twice_subset
        σ (({[x]} ∪ dom Δ) ∪ fv_tm e) (dom Δ ∪ fv_tm e))
        by set_solver.
      exact (proj1 (store_closed_restrict _ _ Hclosed)).
    }
    assert (Hclosed_new :
      closed_env (store_restrict σ (({[x]} ∪ dom Δ) ∪ fv_tm e))).
    {
      pose proof (Hclosed_big σ Hσ) as Hclosed.
      rewrite map_empty_union in Hclosed.
      exact (proj1 Hclosed).
    }
    pose proof (subst_map_restrict_to_fv_from_superset e
      (dom Δ ∪ fv_tm e) σ ltac:(set_solver) Hclosed_old) as Hold.
    pose proof (subst_map_restrict_to_fv_from_superset e
      (({[x]} ∪ dom Δ) ∪ fv_tm e) σ ltac:(set_solver)
      Hclosed_new) as Hnew.
    rewrite <- Hnew in Hvx.
    rewrite <- Hold.
    exact Hvx.
Qed.

Lemma basic_value_typing_lvar_lvars_subset :
  (∀ Γ v T,
    basic_value_lvar Γ v T ->
    lvars_to_atoms ∅ (value_lvars v) ⊆ lvars_fv (dom Γ)) /\
  (∀ Γ e T,
    basic_typing_lvar Γ e T ->
    lvars_to_atoms ∅ (tm_lvars e) ⊆ lvars_fv (dom Γ)).
Proof.
  apply basic_lvar_mutind;
    cbn [value_lvars tm_lvars];
    intros.
  - intros a Ha.
    apply lvars_to_atoms_elem in Ha as [u [Hu _]].
    cbn [value_lvars value_lvars_at] in Hu.
    set_solver.
  - intros a Ha.
    apply lvars_to_atoms_elem in Ha as [u [Hu Hatom]].
    cbn [value_lvars value_lvars_at] in Hu.
    apply elem_of_singleton in Hu. subst u.
    cbn [logic_var_to_atom] in Hatom. inversion Hatom. subst a.
    rewrite lvars_fv_elem.
    apply elem_of_dom. eexists. eassumption.
  - intros a Ha.
    apply lvars_to_atoms_elem in Ha as [u [Hu Hatom]].
    cbn [value_lvars value_lvars_at logic_var_at_depth] in Hu.
    apply elem_of_singleton in Hu. subst u.
    cbn [logic_var_to_atom] in Hatom.
    rewrite lookup_empty in Hatom. discriminate.
  - pose (y := fresh_for
      (lty_env_atom_dom Γ ∪ lvars_to_atoms ∅ (tm_lvars_at 1 e))).
    assert (Hy : y ∉ lty_env_atom_dom Γ ∪
      lvars_to_atoms ∅ (tm_lvars_at 1 e))
      by (subst y; apply fresh_for_not_in).
    match goal with
    | IH : ∀ x, x ∉ lty_env_atom_dom Γ ->
        lvars_to_atoms ∅ (tm_lvars (e ^^ x)) ⊆
        lvars_fv (dom (<[LVFree x := _]> Γ)) |- _ =>
        pose proof (IH y ltac:(set_solver)) as Hbody
    end.
    intros a Ha.
    pose proof Ha as Ha0.
    apply tm_lvars_body_open_atoms_subset with (x:=y) in Ha.
    apply Hbody in Ha.
    rewrite lty_env_insert_free_lvars_fv in Ha.
    unfold lty_env_atom_dom in Hy. set_solver.
  - pose (y := fresh_for
      (L ∪ lvars_to_atoms ∅ (value_lvars_at 1 vf))).
    assert (Hy : y ∉ L ∪ lvars_to_atoms ∅ (value_lvars_at 1 vf))
      by (subst y; apply fresh_for_not_in).
    match goal with
    | IH : ∀ x, x ∉ L ->
        lvars_to_atoms ∅ (value_lvars (vf ^^ x)) ⊆
        lvars_fv (dom (<[LVFree x := _]> Γ)) |- _ =>
        pose proof (IH y ltac:(set_solver)) as Hbody
    end.
    intros a Ha.
    pose proof Ha as Ha0.
    apply value_lvars_body_open_atoms_subset with (x:=y) in Ha.
    apply Hbody in Ha.
    rewrite lty_env_insert_free_lvars_fv in Ha.
    set_solver.
  - exact H.
  - match goal with
    | IH : lvars_to_atoms ∅ (tm_lvars e1) ⊆ lvars_fv (dom Γ) |- _ =>
        pose proof IH as He1
    end.
    pose (y := fresh_for
      (lty_env_atom_dom Γ ∪ lvars_to_atoms ∅ (tm_lvars_at 1 e2))).
    assert (Hy : y ∉ lty_env_atom_dom Γ ∪
      lvars_to_atoms ∅ (tm_lvars_at 1 e2))
      by (subst y; apply fresh_for_not_in).
    match goal with
    | IH : ∀ x, x ∉ lty_env_atom_dom Γ ->
        lvars_to_atoms ∅ (tm_lvars (e2 ^^ x)) ⊆
        lvars_fv (dom (<[LVFree x := _]> Γ)) |- _ =>
        pose proof (IH y ltac:(set_solver)) as Hbody
    end.
    cbn [tm_lvars tm_lvars_at].
    rewrite lvars_to_atoms_empty_union.
    intros a Ha.
    apply elem_of_union in Ha as [Ha|Ha].
    + apply He1. exact Ha.
    + pose proof Ha as Ha0.
      apply tm_lvars_body_open_atoms_subset with (x:=y) in Ha.
      apply Hbody in Ha.
      rewrite lty_env_insert_free_lvars_fv in Ha.
      unfold lty_env_atom_dom in Hy. set_solver.
  - match goal with
    | IH : lvars_to_atoms ∅ (value_lvars _) ⊆ _ |- _ => exact IH
    end.
  - cbn [tm_lvars tm_lvars_at].
    rewrite lvars_to_atoms_empty_union.
    set_solver.
  - cbn [tm_lvars tm_lvars_at].
    rewrite !lvars_to_atoms_empty_union.
    set_solver.
Qed.

Lemma basic_value_lvar_lvars_subset Γ v T :
  basic_value_lvar Γ v T ->
  lvars_to_atoms ∅ (value_lvars v) ⊆ lvars_fv (dom Γ).
Proof.
  exact (proj1 basic_value_typing_lvar_lvars_subset Γ v T).
Qed.

Lemma basic_typing_lvar_lvars_subset Γ e T :
  basic_typing_lvar Γ e T ->
  lvars_to_atoms ∅ (tm_lvars e) ⊆ lvars_fv (dom Γ).
Proof.
  exact (proj2 basic_value_typing_lvar_lvars_subset Γ e T).
Qed.

Lemma expr_total_lvar_atom_env_empty
    (Δ : gmap atom ty) e T (m : WfWorld) :
  Δ ⊢ₑ e ⋮ T ->
  world_dom (m : World) = dom Δ ->
  world_closed_on (dom Δ) m ->
  expr_total_on e m ->
  expr_total_lvar (atom_env_to_lty_env Δ) e ∅ ∅ m.
Proof.
  intros Htyped Hdom Hclosed Htotal.
  assert (Hlty : basic_typing_lvar (atom_env_to_lty_env Δ) e T).
  { apply basic_typing_lvar_atom_env_of_basic. exact Htyped. }
  pose proof (basic_typing_lvar_lvars_subset _ _ _ Hlty) as Hlvars.
  rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms in Hlvars.
  unfold expr_total_lvar, expr_total_with_store.
  rewrite lvars_to_atoms_empty_union.
  rewrite atom_env_to_lty_env_dom, lvars_to_atoms_of_atoms.
  replace (dom Δ ∪ lvars_to_atoms ∅ (tm_lvars e)) with (dom Δ)
    by set_solver.
  split.
  - intros σ Hσ.
    rewrite map_empty_union.
    exact (Hclosed σ Hσ).
  - intros σ Hσ.
    destruct Htotal as [Hfv Hsteps].
    destruct (Hsteps σ Hσ) as [vx Hvx].
    exists vx.
    replace (store_restrict (∅ ∪ σ) (dom Δ))
      with (store_restrict σ (dom Δ)).
    2:{ rewrite map_empty_union. reflexivity. }
    assert (Heq :
      subst_map (store_restrict σ (fv_tm e)) e =
      subst_map (store_restrict σ (dom Δ)) e).
    {
      apply subst_map_restrict_to_fv_from_superset.
      - rewrite <- Hdom. exact Hfv.
      - exact (proj1 (Hclosed σ Hσ)).
    }
    change (subst_map (store_restrict σ (dom Δ)) e →* tret vx).
    rewrite <- Heq.
    exact Hvx.
Qed.

Lemma basic_typing_lvar_empty_lvars_to_atoms_subset Σ e T :
  basic_typing_lvar (lty_env_open_lvars ∅ Σ) (open_tm_env ∅ e) T ->
  lvars_to_atoms ∅ (tm_lvars e) ⊆ lvars_fv (dom Σ).
Proof.
  intros Htyping.
  rewrite open_tm_env_empty in Htyping.
  pose proof (basic_typing_lvar_lvars_subset _ _ _ Htyping) as Hfv.
  rewrite lty_env_open_lvars_empty in Hfv.
  exact Hfv.
Qed.

Lemma FDenotObligationIn_total Σ τ e ρ m :
  res_models_with_store ρ m (FDenotObligationIn Σ τ e) ->
  expr_total_lvar Σ e ∅ ρ m.
Proof.
  intros Hm.
  unfold FDenotObligationIn in Hm.
  destruct (res_models_with_store_store_resource_atom_vars_elim ρ m
    (dom Σ) (denot_obligation_parts Σ τ e) Hm)
    as [m0 [Hscope [Hparts Hle]]].
  destruct Hparts as [_ [Htyping [_ Htotal]]].
  eapply (expr_total_lvar_obligation_extend Σ e ρ m0 m).
  - eapply basic_typing_lvar_empty_lvars_to_atoms_subset. exact Htyping.
  - unfold formula_scoped_in_world in Hscope.
    rewrite formula_fv_FStoreResourceAtom_lvars in Hscope.
    intros x Hx. apply Hscope. set_solver.
  - exact Hle.
  - exact Htotal.
Qed.

Lemma FDenotObligationIn_parts Σ τ e ρ m :
  res_models_with_store ρ m (FDenotObligationIn Σ τ e) ->
  basic_choice_ty_lvar
    (dom (lty_env_open_lvars ∅ Σ)) (open_cty_env ∅ τ) ∧
  basic_typing_lvar
    (lty_env_open_lvars ∅ Σ) (open_tm_env ∅ e)
    (erase_ty (open_cty_env ∅ τ)) ∧
  closed_resource_lvar Σ ∅ m ∧
  expr_total_lvar Σ e ∅ ρ m.
Proof.
  intros Hm.
  split; [eapply FDenotObligationIn_basic_choice; exact Hm |].
  split; [eapply FDenotObligationIn_basic_typing; exact Hm |].
  split; [eapply FDenotObligationIn_closed_resource; exact Hm |].
  eapply FDenotObligationIn_total. exact Hm.
Qed.

Lemma expr_total_lvar_obligation_restrict Σ e ρ m :
  lvars_to_atoms ∅ (tm_lvars e) ⊆ lvars_fv (dom Σ) ->
  expr_total_lvar Σ e ∅ ρ m ->
  expr_total_lvar Σ e ∅
    (store_restrict ρ (lvars_fv (dom Σ)))
    (res_restrict m (lvars_fv (dom Σ))).
Proof.
  intros Hfv Htotal.
  unfold expr_total_lvar, expr_total_with_store in *.
  set (D := lvars_fv (dom Σ)).
  set (X := lvars_to_atoms ∅ (dom Σ ∪ tm_lvars e)).
  assert (HX : X ⊆ D).
  {
    subst X D.
    rewrite lvars_to_atoms_empty_union.
    pose proof (lvars_to_atoms_empty_subset (dom Σ)).
    set_solver.
  }
  destruct Htotal as [Hclosed Hsteps].
  split.
  - intros σ Hσ.
    apply res_restrict_lift_store in Hσ as [σm [Hσm Hσ]].
    subst D X.
    rewrite <- Hσ.
    rewrite store_restrict_union_restrict_subset by exact HX.
    exact (Hclosed σm Hσm).
  - intros σ Hσ.
    apply res_restrict_lift_store in Hσ as [σm [Hσm Hσ]].
    subst D X.
    rewrite <- Hσ.
    rewrite store_restrict_union_restrict_subset by exact HX.
    exact (Hsteps σm Hσm).
Qed.

Lemma FDenotObligationIn_intro_from_typed_guard Σ τ e ρ m :
  res_models_with_store ρ m (FClosedResourceIn Σ) ->
  basic_choice_ty_lvar
    (dom (lty_env_open_lvars ∅ Σ)) (open_cty_env ∅ τ) ->
  basic_typing_lvar
    (lty_env_open_lvars ∅ Σ) (open_tm_env ∅ e)
    (erase_ty (open_cty_env ∅ τ)) ->
  expr_total_lvar Σ e ∅ ρ m ->
  res_models_with_store ρ m (FDenotObligationIn Σ τ e).
Proof.
  intros Hclosed Hbasic Htyping Htotal.
  unfold FDenotObligationIn.
  eapply res_models_with_store_store_resource_atom_vars_intro.
  - pose proof (res_models_with_store_fuel_scoped _ ρ m
      (FClosedResourceIn Σ) Hclosed) as Hscope.
    unfold FClosedResourceIn in Hscope.
    unfold formula_scoped_in_world in Hscope |- *.
    rewrite !formula_fv_FStoreResourceAtom_lvars in *.
    exact Hscope.
  - split; [exact Hbasic |].
    split; [exact Htyping |].
    split.
    + apply closed_resource_lvar_restrict_self.
      eapply FClosedResourceIn_closed_resource. exact Hclosed.
    + eapply expr_total_lvar_obligation_restrict.
      * eapply basic_typing_lvar_empty_lvars_to_atoms_subset. exact Htyping.
      * exact Htotal.
Qed.

Lemma FDenotObligationIn_insert_fresh_atom_env
    (Δ : gmap atom ty) x T τ e (m : WfWorld) :
  x ∉ dom Δ ∪ fv_cty τ ∪ fv_tm e ->
  m ⊨ FClosedResourceIn (atom_env_to_lty_env (<[x := T]> Δ)) ->
  m ⊨ FDenotObligationIn (atom_env_to_lty_env Δ) τ e ->
  m ⊨ FDenotObligationIn (atom_env_to_lty_env (<[x := T]> Δ)) τ e.
Proof.
  intros Hfresh Hclosed Hobl.
  pose proof (FDenotObligationIn_parts
    (atom_env_to_lty_env Δ) τ e ∅ m Hobl)
    as [Hbasic [Htyping [Hcr Htotal]]].
  eapply FDenotObligationIn_intro_from_typed_guard.
  - exact Hclosed.
  - rewrite !lty_env_open_lvars_empty in *.
    eapply basic_choice_ty_lvar_mono; [| exact Hbasic].
    rewrite !atom_env_to_lty_env_dom, dom_insert_L. set_solver.
  - rewrite !lty_env_open_lvars_empty in *.
    rewrite atom_env_to_lty_env_insert.
    + eapply basic_typing_lvar_weaken_free; [| exact Htyping].
      rewrite atom_env_to_lty_env_atom_dom. set_solver.
    + set_solver.
  - eapply expr_total_lvar_insert_fresh_atom_env.
    + set_solver.
    + eapply FClosedResourceIn_closed_resource. exact Hclosed.
    + exact Htotal.
Qed.

Lemma FDenotObligationIn_drop_insert_fresh_atom_env
    (Δ : gmap atom ty) x T τ e (m : WfWorld) :
  x ∉ dom Δ ∪ fv_cty τ ∪ fv_tm e ->
  m ⊨ FDenotObligationIn (atom_env_to_lty_env (<[x := T]> Δ)) τ e ->
  m ⊨ FDenotObligationIn (atom_env_to_lty_env Δ) τ e.
Proof.
  intros Hfresh Hobl.
  pose proof (FDenotObligationIn_parts
    (atom_env_to_lty_env (<[x := T]> Δ)) τ e ∅ m Hobl)
    as [Hbasic [Htyping [Hcr Htotal]]].
  assert (Hx_dom : x ∉ dom Δ).
  {
    intros Hx_in.
    apply Hfresh.
    rewrite elem_of_union.
    left.
    rewrite elem_of_union.
    left.
    exact Hx_in.
  }
  assert (Hx_cty : x ∉ fv_cty τ).
  {
    intros Hx_in.
    apply Hfresh.
    rewrite elem_of_union.
    left.
    rewrite elem_of_union.
    right.
    exact Hx_in.
  }
  assert (Hx_tm : x ∉ fv_tm e).
  {
    intros Hx_in.
    apply Hfresh.
    rewrite elem_of_union.
    right.
    exact Hx_in.
  }
  eapply FDenotObligationIn_intro_from_typed_guard.
  - eapply FClosedResourceIn_insert_fresh_atom_env.
    + exact Hx_dom.
    + eapply FClosedResourceIn_intro_lvar.
      * pose proof (res_models_with_store_fuel_scoped _ ∅ m _
          Hobl) as Hscope.
        unfold formula_scoped_in_world in Hscope.
        unfold FDenotObligationIn in Hscope.
        rewrite dom_empty_L, formula_fv_FStoreResourceAtom_lvars in Hscope.
        intros z Hz.
        apply Hscope.
        set_solver.
      * exact Hcr.
  - rewrite !lty_env_open_lvars_empty in *.
    rewrite !open_cty_env_empty in *.
    eapply basic_choice_ty_lvar_drop_insert_fresh_atom_env.
    + exact Hx_dom.
    + exact Hx_cty.
    + exact Hbasic.
  - rewrite !lty_env_open_lvars_empty in *.
    rewrite !open_tm_env_empty, !open_cty_env_empty in *.
    eapply basic_typing_lvar_drop_insert_fresh_atom_env.
    + exact Hx_dom.
    + exact Hx_tm.
    + exact Htyping.
  - eapply expr_total_lvar_drop_insert_fresh_atom_env.
    + exact Hx_tm.
    + exact Htotal.
Qed.

Lemma FDenotObligationIn_intro_under_typed_forall_lc Σ τ e ρ m :
  lc_choice_ty τ ->
  lc_tm e ->
  res_models_with_store ρ m (FClosedResourceIn Σ) ->
  basic_choice_ty_lvar (dom (lty_env_open_lvars ∅ Σ)) τ ->
  basic_typing_lvar (lty_env_open_lvars ∅ Σ) e (erase_ty τ) ->
  expr_total_lvar Σ e ∅ ρ m ->
  res_models_with_store ρ m (FDenotObligationIn Σ τ e).
Proof.
  intros Hτ He Hclosed Hbasic Htyping Htotal.
  eapply FDenotObligationIn_intro_from_typed_guard; eauto;
    rewrite ?open_cty_env_empty, ?open_tm_env_empty; eauto.
Qed.

Lemma FDenotObligationIn_intro_atom_env
    (Δ : gmap atom ty) (e : tm) (τ : choice_ty) (m : WfWorld) :
  Δ ⊢ₑ e ⋮ erase_ty τ ->
  basic_choice_ty (dom Δ) τ ->
  world_dom (m : World) = dom Δ ->
  world_closed_on (dom Δ) m ->
  expr_total_on e m ->
  m ⊨ FDenotObligationIn (atom_env_to_lty_env Δ) τ e.
Proof.
  intros Htyped Hbasic Hdom Hclosed Htotal.
  eapply FDenotObligationIn_intro_under_typed_forall_lc.
  - eapply basic_choice_ty_lc. exact Hbasic.
  - eapply typing_tm_lc. exact Htyped.
  - eapply FClosedResourceIn_atom_env_intro; eauto.
    rewrite Hdom. set_solver.
  - rewrite lty_env_open_lvars_empty.
    apply basic_choice_ty_lvar_atom_env_of_basic. exact Hbasic.
  - rewrite lty_env_open_lvars_empty.
    apply basic_typing_lvar_atom_env_of_basic. exact Htyped.
  - eapply expr_total_lvar_atom_env_empty; eauto.
Qed.

Lemma FDenotObligationIn_transport
    Σ1 Σ2 τ1 τ2 e1 e2 ρ m :
  FDenotObligationIn Σ1 τ1 e1 = FDenotObligationIn Σ2 τ2 e2 ->
  res_models_with_store ρ m (FDenotObligationIn Σ1 τ1 e1) ->
  res_models_with_store ρ m (FDenotObligationIn Σ2 τ2 e2).
Proof. intros -> Hm. exact Hm. Qed.
