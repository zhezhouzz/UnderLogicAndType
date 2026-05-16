(** * ChoiceLogic.FormulaWorldExtension

    Formula-level transport lemmas for explicit world extensions. *)

From ChoicePrelude Require Import Store.
From ChoiceAlgebra Require Import Resource WorldExtension.
From ChoiceLogic Require Import Formula FormulaTactics FormulaDerived.

Section FormulaWorldExtension.

Context {V : Type} `{ValueSig V}.

Local Notation StoreT := (gmap atom V) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).

Lemma formula_scoped_extend_mono
    (ρ : StoreT) (m : WfWorldT) F (n : WfWorldT) (φ : FormulaT) :
  m #> F ~~> n ->
  formula_scoped_in_world ρ m φ ->
  formula_scoped_in_world ρ n φ.
Proof.
  unfold formula_scoped_in_world.
  intros Hext Hscope.
  pose proof (res_extend_by_dom_subset _ _ _ Hext).
  set_solver.
Qed.

Lemma res_models_with_store_extend_mono
    (ρ : StoreT) (m : WfWorldT) F (n : WfWorldT) (φ : FormulaT) :
  m #> F ~~> n ->
  res_models_with_store ρ m φ ->
  res_models_with_store ρ n φ.
Proof.
  intros Hext Hmodel.
  eapply res_models_with_store_kripke.
  - eapply res_extend_by_le_base. exact Hext.
  - exact Hmodel.
Qed.

Lemma res_models_extend_mono (m : WfWorldT) F (n : WfWorldT) (φ : FormulaT) :
  m #> F ~~> n ->
  res_models m φ ->
  res_models n φ.
Proof.
  unfold res_models.
  apply res_models_with_store_extend_mono.
Qed.

Lemma res_models_with_store_forall_by_extension_iff
    (ρ : StoreT) (m : WfWorldT) (p : FormulaT) :
  formula_scoped_in_world ρ m (FForall p) ->
  (res_models_with_store ρ m (FForall p) <->
   ∃ L : aset,
     world_dom (m : World) ⊆ L /\
     forall y F my,
       y ∉ L ->
       forall_extension_shape (world_dom (m : World)) y F ->
       m #> F ~~> my ->
       res_models_with_store ρ my (formula_open 0 y p)).
Proof.
  intros Hscope. split.
  - intros Hforall.
    unfold res_models_with_store in Hforall.
    cbn [formula_measure res_models_with_store_fuel
      formula_scoped_in_world formula_fv] in Hforall.
    destruct Hforall as [_ [L [HLdom Hopen]]].
    exists L. split; [exact HLdom |].
    intros y F my Hy HFshape Hext.
    destruct HFshape as [_ Hout].
    pose proof (res_extend_by_dom _ _ _ Hext) as Hdom_my.
    pose proof (res_extend_by_restrict_base _ _ _ Hext) as Hrestrict.
    specialize (Hopen y Hy my ltac:(rewrite Hdom_my, Hout; reflexivity) Hrestrict).
    models_fuel_irrel Hopen.
  - intros [L [HLdom Hopen]].
    unfold res_models_with_store.
    cbn [formula_measure res_models_with_store_fuel
      formula_scoped_in_world formula_fv].
    split; [exact Hscope |].
    exists L. split; [exact HLdom |].
    intros y Hy my Hdom_my Hrestrict.
    assert (Hy_m : y ∉ world_dom (m : World)) by set_solver.
    destruct (forall_world_as_extend_by m y my Hy_m Hdom_my Hrestrict)
      as [F [HFshape Hext]].
    specialize (Hopen y F my Hy HFshape Hext).
    models_fuel_irrel Hopen.
Qed.

Lemma res_models_forall_by_extension_iff
    (m : WfWorldT) (p : FormulaT) :
  formula_scoped_in_world ∅ m (FForall p) ->
  (res_models m (FForall p) <->
   ∃ L : aset,
     world_dom (m : World) ⊆ L /\
     forall y F my,
       y ∉ L ->
       forall_extension_shape (world_dom (m : World)) y F ->
       m #> F ~~> my ->
       res_models my (formula_open 0 y p)).
Proof.
  intros Hscope.
  unfold res_models.
  apply res_models_with_store_forall_by_extension_iff.
  exact Hscope.
Qed.

Lemma res_models_forall_by_extension_map
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FForall φ) ->
  formula_scoped_in_world ∅ m (FForall ψ) ->
  (∃ L : aset,
    world_dom (m : World) ⊆ L /\
    ∀ y F my,
      y ∉ L ->
      forall_extension_shape (world_dom (m : World)) y F ->
      m #> F ~~> my ->
      res_models my (formula_open 0 y φ) ->
      res_models my (formula_open 0 y ψ)) ->
  res_models m (FForall φ) ->
  res_models m (FForall ψ).
Proof.
  intros Hscopeφ Hscopeψ [Lmap [HLmap Hmap]] Hforall.
  apply (proj2 (res_models_forall_by_extension_iff m ψ Hscopeψ)).
  destruct (proj1 (res_models_forall_by_extension_iff m φ Hscopeφ) Hforall)
    as [L [HL Hopen]].
  exists (L ∪ Lmap). split; [set_solver |].
  intros y F my Hy HFshape Hext.
  rewrite not_elem_of_union in Hy.
  destruct Hy as [HyL HyMap].
  eapply Hmap; eauto.
Qed.

Lemma res_models_forall_by_extension_congr
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FForall φ) ->
  formula_scoped_in_world ∅ m (FForall ψ) ->
  (∃ L : aset,
    world_dom (m : World) ⊆ L /\
    ∀ y F my,
      y ∉ L ->
      forall_extension_shape (world_dom (m : World)) y F ->
      m #> F ~~> my ->
      (res_models my (formula_open 0 y φ) <->
       res_models my (formula_open 0 y ψ))) ->
  res_models m (FForall φ) <-> res_models m (FForall ψ).
Proof.
  intros Hscopeφ Hscopeψ [L [HL Hiff]].
  split.
  - eapply res_models_forall_by_extension_map; eauto.
    exists L. split; [exact HL |].
    intros y F my Hy HFshape Hext Hmodel.
    exact (proj1 (Hiff y F my Hy HFshape Hext) Hmodel).
  - eapply res_models_forall_by_extension_map; eauto.
    exists L. split; [exact HL |].
    intros y F my Hy HFshape Hext Hmodel.
    exact (proj2 (Hiff y F my Hy HFshape Hext) Hmodel).
Qed.

End FormulaWorldExtension.
