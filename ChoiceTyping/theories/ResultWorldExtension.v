(** * ChoiceTyping.ResultWorldExtension

    Typing-facing bridges for expression-result world extensions.  The core
    semantic extension definitions live in [ChoiceType.TypeDenotation.ResultExtension]. *)

From CoreLang Require Import Instantiation InstantiationProps BasicTypingProps
  LocallyNamelessProps OperationalProps.
From ChoiceAlgebra Require Import Resource.
From ChoiceType Require Export TypeDenotation.ResultExtension.
From ChoiceType Require Import TypeDenotation.LemmasObligation.


Lemma result_extends_closed_insert_from_basic_subset
    (Δ : gmap atom ty) T e x (m mx : WfWorld) F :
  result_extends e x m F mx →
  Δ ⊢ₑ e ⋮ T →
  dom Δ ⊆ world_dom (m : World) →
  world_closed_on (dom Δ) m →
  expr_total_on e m →
  x ∉ dom Δ →
  world_closed_on (dom (<[x := T]> Δ)) mx.
Proof.
  intros Hext Htyped Hdom Hclosed Htotal Hx.
  rewrite dom_insert_L.
  replace ({[x]} ∪ dom Δ) with (dom Δ ∪ {[x]}) by set_solver.
  intros σx Hσx.
  destruct (result_extends_elim e x m mx F σx Hext Htotal Hσx)
    as [σ [vx [Hσ [Hsteps ->]]]].
  rewrite store_restrict_insert_fresh_union.
  2:{
    eapply store_lookup_none_of_dom.
    - apply wfworld_store_dom; eauto 6.
    - exact (result_extends_fresh _ _ _ _ _ Hext).
  }
  2:{ exact Hx. }
  destruct (Hclosed σ Hσ) as [Hclosedσ Hlcσ].
  assert (Hvx : stale vx = ∅ ∧ is_lc vx).
  {
    pose proof (basic_typing_contains_fv_tm Δ e T Htyped) as Hfv.
    pose proof (typing_tm_lc Δ e T Htyped) as Hlc.
    assert (Hclosed_fv : world_closed_on (fv_tm e) m).
    { eapply world_closed_on_mono; [exact Hfv | exact Hclosed]. }
    eapply (steps_closed_result_of_restrict_world
      (fv_tm e) e m (store_restrict σ (fv_tm e)) vx).
    - intros z Hz. apply Hdom. apply Hfv. exact Hz.
    - set_solver.
    - eauto 6.
    - eauto 6.
    - exists σ. split; eauto 6.
    - replace (store_restrict (store_restrict σ (fv_tm e)) (fv_tm e))
        with (store_restrict σ (fv_tm e)).
      + eauto 6.
      + store_norm. reflexivity.
  }
  destruct Hvx as [Hvx_closed Hvx_lc].
  split.
  - unfold closed_env in *.
    apply map_Forall_insert_2; eauto 6.
  - unfold lc_env in *.
    apply map_Forall_insert_2; eauto 6.
Qed.

Lemma result_extends_closed_insert_from_basic
    (Δ : gmap atom ty) T e x (m mx : WfWorld) F :
  result_extends e x m F mx →
  Δ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Δ →
  world_closed_on (dom Δ) m →
  expr_total_on e m →
  x ∉ dom Δ →
  world_closed_on (dom (<[x := T]> Δ)) mx.
Proof.
  intros Hext Htyped Hdom Hclosed Htotal Hx.
  eapply result_extends_closed_insert_from_basic_subset; eauto.
  rewrite Hdom. set_solver.
Qed.

Lemma closed_resource_typed_bind_insert_result_atom_env
    (Δ : gmap atom ty) e x y T1 Ty (my ny : WfWorld) Fx :
  x <> y ->
  x ∉ dom Δ ->
  y ∉ dom Δ ->
  result_extends e x my Fx ny ->
  (<[y := Ty]> Δ) ⊢ₑ e ⋮ T1 ->
  world_dom (my : World) = dom (<[y := Ty]> Δ) ->
  world_closed_on (dom (<[y := Ty]> Δ)) my ->
  expr_total_on e my ->
  ny ⊨ formula_open 0 y
    (FClosedResourceIn
      (typed_lty_env_bind (atom_env_to_lty_env (<[x := T1]> Δ)) Ty)).
Proof.
  intros Hxy Hx Hy Hext Htyped Hdom Hclosed Htotal.
  rewrite formula_open_FClosedResourceIn.
  rewrite lty_env_open_typed_bind_atom_env.
  2:{ rewrite dom_insert_L. set_solver. }
  assert (Hclosed_ny :
    world_closed_on (dom (<[x := T1]> (<[y := Ty]> Δ))) ny).
  {
    eapply result_extends_closed_insert_from_basic; eauto.
    rewrite dom_insert_L. set_solver.
  }
  assert (<[y := Ty]> (<[x := T1]> Δ) =
          <[x := T1]> (<[y := Ty]> Δ)) as Hperm.
  {
    apply map_eq. intros z.
    rewrite !lookup_insert.
    repeat case_decide; subst; try congruence; reflexivity.
  }
  rewrite Hperm.
  eapply FClosedResourceIn_atom_env_intro.
  - pose proof (result_extends_dom _ _ _ _ _ Hext) as Hdom_ny.
    rewrite Hdom_ny, Hdom.
    rewrite !dom_insert_L. set_solver.
  - exact Hclosed_ny.
Qed.



Lemma FExprResultAt_base_result_witness
    (Σ : gmap atom ty) (T : ty) e ν (m n : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  ν ∉ dom Σ →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  res_restrict n (dom Σ) = m →
  world_dom (n : World) = dom Σ ∪ {[ν]} →
  n ⊨ FExprResultAt (dom Σ) e ν →
  ∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx.
Proof.
  intros Hty HνΣ Hdom_m Hclosed Hrestrict Hdom_n Hmodel σ Hσm.
  pose proof (basic_typing_contains_fv_tm Σ e T Hty) as Hfv.
  pose proof (typing_tm_lc Σ e T Hty) as Hlc.
  assert (Hproj : (res_restrict n (dom Σ) : World) σ).
  { rewrite Hrestrict. exact Hσm. }
  destruct Hproj as [σn [Hσn HσnΣ]].
  assert (Hproj' : (res_restrict n (dom Σ) : World) σ).
  { exists σn. split; eauto. }
  pose proof (FExprResultAt_fiber_expr_result_in_world
    (dom Σ) e ν n σ Hproj' Hlc HνΣ Hdom_n Hmodel) as Hexpr.
  assert (Hfiber :
    (res_fiber_from_projection n (dom Σ) σ Hproj' : World) σn).
  { apply res_fiber_from_projection_member; eauto. }
  assert (Hνproj :
    (res_restrict
      (res_fiber_from_projection n (dom Σ) σ Hproj') {[ν]} : World)
      (store_restrict σn {[ν]})).
  { exists σn. split; eauto. }
  pose proof (expr_result_in_world_sound
    (store_restrict σ (dom Σ)) e ν
    (res_fiber_from_projection n (dom Σ) σ Hproj')
    (store_restrict σn {[ν]}) Hexpr Hνproj) as Hstore.
  destruct (expr_result_store_elim ν
    (subst_map (store_restrict σ (dom Σ)) e)
    (store_restrict σn {[ν]}) Hstore)
    as [vx [_ [_ [_ HstepsX]]]].
  exists vx.
  rewrite (subst_map_restrict_to_fv_from_superset e
    (dom Σ) σ Hfv (proj1 (Hclosed σ Hσm))).
  exact HstepsX.
Qed.
