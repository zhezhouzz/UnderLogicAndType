(** * ChoiceType.TypeDenotation.LemmasObligationExprCont.legacy

    Old opened/drop-result route for proving the constant-continuation insert
    helper.  This file is intentionally not listed in [_CoqProject]; the current
    compiled path keeps only the interface needed by [Denotation.v]. *)

From Stdlib Require Import Logic.FunctionalExtensionality
  Logic.PropExtensionality Lia.
From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps BasicTypingProps
  Sugar.
From ChoiceLogic Require Import FormulaDerived FormulaWorldExtension.
From ChoiceType Require Import BasicStore BasicTyping LocallyNamelessProps
  TypeDenotation.LemmasObligation.

Local Notation FQ := FormulaQ.

Lemma FExprResultAtLvar_drop_fresh_lvar_opened_legacy
    (L : lvset) (e : tm) (ν z : logic_var) k y (m : WfWorld) :
  logic_var_open k y ν ∈ lvars_open k y L ->
  z <> logic_var_open k y ν ->
  z ∉ lvars_open k y (tm_lvars e) ->
  world_closed_on (lvars_to_atoms ∅ (lvars_open k y (L ∪ {[z]}))) m ->
  m ⊨ formula_open k y (FExprResultAtLvar (L ∪ {[z]}) e ν) ->
  m ⊨ formula_open k y (FExprResultAtLvar L e ν).
Proof.
  (* Opened result atoms are the useful form: before opening, [ν] may be bound
     and [logic_var_to_atom ∅ ν] is intentionally [None].  The closed-resource
     premise is essential because [subst_map] recursively substitutes values:
     [e] not mentioning [z] is not enough if a value read by [e] contains [z]. *)
Admitted.

Lemma FExprResultAtLvar_typed_bind_drop_fresh_atom_env_opened_legacy
    (Δ : gmap atom ty) x Tx Ty e y (m : WfWorld) :
  x ∉ dom Δ ->
  y ∉ dom Δ ->
  x <> y ->
  x ∉ fv_tm e ->
  m ⊨ formula_open 0 y
    (FClosedResourceIn
      (typed_lty_env_bind
        (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty)) ->
  m ⊨ formula_open 0 y (FExprResultAtLvar
    (dom (typed_lty_env_bind
      (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty))
    (↑[0] e) (LVBound 0)) ->
  m ⊨ formula_open 0 y (FExprResultAtLvar
    (dom (typed_lty_env_bind (atom_env_to_lty_env Δ) Ty))
    (↑[0] e) (LVBound 0)).
Proof.
  intros Hx Hy Hxy Hxe Hclosed Hm.
  rewrite typed_lty_env_bind_atom_env_insert_dom in Hm by exact Hx.
  assert (Hclosed_world :
    world_closed_on
      (lvars_to_atoms ∅
        (lvars_open 0 y
          (dom (typed_lty_env_bind (atom_env_to_lty_env Δ) Ty) ∪
            {[LVFree x]}))) m).
  {
    rewrite formula_open_FClosedResourceIn in Hclosed.
    pose proof (FClosedResourceIn_closed_resource _ _ _ Hclosed) as Hcr.
    unfold closed_resource_lvar in Hcr.
    rewrite lty_env_open_one_dom in Hcr.
    rewrite typed_lty_env_bind_atom_env_insert_dom in Hcr by exact Hx.
    exact Hcr.
  }
  eapply (FExprResultAtLvar_drop_fresh_lvar_opened_legacy
    (dom (typed_lty_env_bind (atom_env_to_lty_env Δ) Ty))
    (↑[0] e) (LVBound 0) (LVFree x) 0 y m).
  - unfold lvars_open.
    apply elem_of_map.
    exists (LVBound 0). split; [reflexivity |].
    rewrite typed_lty_env_bind_dom. set_solver.
  - intros Hbad. cbn [logic_var_open] in Hbad. inversion Hbad. congruence.
  - intros Hbad.
    unfold lvars_open in Hbad.
    apply elem_of_map in Hbad as [v [Hv Hv_in]].
    destruct v as [n|a]; cbn [logic_var_open] in Hv.
    * destruct (decide (n = 0)) as [->|Hn].
      -- inversion Hv; subst. contradiction.
      -- inversion Hv.
    * inversion Hv; subst a.
      eapply tm_lvars_shift_free_fresh; eauto.
  - exact Hclosed_world.
  - exact Hm.
Qed.

Lemma FExprContBody_insert_fresh_atom_env_map_opened_legacy
    (Δ : gmap atom ty) x Tx Ty e Q Q' y (m : WfWorld) :
  x ∉ dom Δ ->
  y ∉ dom Δ ->
  x <> y ->
  x ∉ fv_tm e ->
  formula_scoped_in_world ∅ m
    (formula_open 0 y
      (FExprContBody (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty e Q')) ->
  (m ⊨ formula_open 0 y
      (Q (typed_lty_env_bind (atom_env_to_lty_env Δ) Ty)) ->
    m ⊨ formula_open 0 y
      (Q' (typed_lty_env_bind
        (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty))) ->
  m ⊨ formula_open 0 y
    (FExprContBody (atom_env_to_lty_env Δ) Ty e Q) ->
  m ⊨ formula_open 0 y
    (FExprContBody (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty e Q').
Proof.
  intros Hx Hy Hxy Hxe Hscope Hpost Hbody.
  unfold FExprContBody, FForallTypedBody in Hbody |- *.
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
  pose proof (res_models_impl_elim _ _ _ Hbody Hclosed_old) as Hinner.
  eapply res_models_impl_map.
  - pose proof (res_models_with_store_fuel_scoped _ ∅ m _
      Hclosed_new) as Hscope_closed_new.
    unfold formula_scoped_in_world in Hscope, Hscope_closed_new |- *.
    cbn [formula_fv]. set_solver.
  - eapply FExprResultAtLvar_typed_bind_drop_fresh_atom_env_opened_legacy; eauto.
  - exact Hpost.
  - exact Hinner.
Qed.
