(** * ChoiceLogic.FormulaWorldExtension

    Formula-level transport principles for explicit world extensions under the
    store-free semantics.  The old forall-by-extension equivalence lemmas are
    intentionally absent: forall is now defined directly by extension. *)

From ChoiceAlgebra Require Import Resource.
From ChoiceLogic Require Import Formula FormulaDerived.

Section FormulaWorldExtension.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).

Lemma formula_scoped_extend_mono
    (m : WfWorldT) (F : fiber_extension (V := V))
    (n : WfWorldT) (φ : FormulaT) :
  res_extend_by m F n →
  formula_scoped_in_world m φ →
  formula_scoped_in_world n φ.
Proof.
  intros Hext Hscope.
  unfold formula_scoped_in_world in *.
  pose proof (res_extend_by_dom m F n Hext) as Hdom.
  set_solver.
Qed.

Lemma formula_scoped_extend_base_iff
    (m : WfWorldT) (F : fiber_extension (V := V))
    (n : WfWorldT) (φ : FormulaT) :
  res_extend_by m F n →
  formula_fv φ ⊆ world_dom (m : WorldT) →
  (formula_scoped_in_world n φ ↔ formula_scoped_in_world m φ).
Proof.
  intros Hext Hfv. split.
  - intros _. exact Hfv.
  - eapply formula_scoped_extend_mono. exact Hext.
Qed.

Lemma res_models_extend_mono
    (m : WfWorldT) (F : fiber_extension (V := V))
    (n : WfWorldT) (φ : FormulaT) :
  res_extend_by m F n →
  res_models m φ →
  res_models n φ.
Proof.
  intros Hext Hmodel.
  eapply res_models_kripke; [| exact Hmodel].
  apply res_extend_by_le with (F := F). exact Hext.
Qed.

Lemma res_models_extend_base_iff
    (m : WfWorldT) (F : fiber_extension (V := V))
    (n : WfWorldT) (φ : FormulaT) :
  res_extend_by m F n →
  formula_fv φ ⊆ world_dom (m : WorldT) →
  (res_models n φ ↔ res_models m φ).
Proof.
  intros Hext Hfv. split.
  - intros Hn.
    pose proof (proj1 (res_models_restrict_fv_iff n φ) Hn) as Hnr.
    pose proof (res_extend_by_le m F n Hext) as Hle.
    rewrite <- (res_restrict_le_eq m n (formula_fv φ) Hle Hfv) in Hnr.
    eapply res_models_kripke; [| exact Hnr].
    apply res_restrict_le.
  - apply res_models_extend_mono with (F := F). exact Hext.
Qed.

Lemma res_models_extend_input_widen_to_iff
  (m : WfWorldT)
  (F F' : fiber_extension (V := V))
  (n n' : WfWorldT) (φ : FormulaT) :
  fiber_extension_input_widen_to F F' →
  ext_in F' ⊆ world_dom (m : WorldT) →
  res_extend_by m F n →
  res_extend_by m F' n' →
  formula_fv φ ⊆ world_dom (m : WorldT) →
  (res_models n φ ↔ res_models n' φ).
Proof.
  intros _ _ Hext Hext' Hfv.
  transitivity (res_models m φ).
  - apply res_models_extend_base_iff with (F := F); assumption.
  - symmetry. apply res_models_extend_base_iff with (F := F'); assumption.
Qed.

Lemma res_models_plus_extend_pullback
    (m : WfWorldT) (F : fiber_extension (V := V)) (n : WfWorldT)
    (φ1 φ2 ψ1 ψ2 : FormulaT) :
  res_extend_by m F n →
  world_dom (m : WorldT) ⊆ formula_fv φ1 →
  world_dom (m : WorldT) ⊆ formula_fv φ2 →
  res_models n (FPlus φ1 φ2) →
  fiber_extension_functional_on m F →
  (∀ (m1 n1 : WfWorldT),
    world_dom (m1 : WorldT) = world_dom (m : WorldT) →
    res_subset m1 m →
    res_extend_by m1 F n1 →
    res_models n1 φ1 →
    res_models m1 ψ1) →
  (∀ (m2 n2 : WfWorldT),
    world_dom (m2 : WorldT) = world_dom (m : WorldT) →
    res_subset m2 m →
    res_extend_by m2 F n2 →
    res_models n2 φ2 →
    res_models m2 ψ2) →
  res_models m (FPlus ψ1 ψ2).
Proof.
  intros Hext Hdomφ1 Hdomφ2 Hplus Hfun Hψ1 Hψ2.
  pose proof (res_models_fuel_scoped _ _ _ Hplus) as Hscope_plus.
  pose proof (proj1 (res_models_plus_iff n φ1 φ2 Hscope_plus) Hplus)
    as [n1 [n2 [Hdef [Hsum_le [Hn1 Hn2]]]]].
  assert (Hdom_m_n1 : world_dom (m : WorldT) ⊆ world_dom (n1 : WorldT)).
  {
    pose proof (res_models_fuel_scoped _ _ _ Hn1) as Hscope1.
    unfold formula_scoped_in_world in Hscope1. set_solver.
  }
  assert (Hdom_m_n2 : world_dom (m : WorldT) ⊆ world_dom (n2 : WorldT)).
  {
    pose proof (res_models_fuel_scoped _ _ _ Hn2) as Hscope2.
    unfold formula_scoped_in_world in Hscope2. set_solver.
  }
  destruct (res_extend_by_sum_pullback m F n n1 n2 Hdef
    Hext Hfun Hdom_m_n1 Hdom_m_n2 Hsum_le)
    as (m1 & m2 & Hdefm & n1' & n2' &
      Hdom_m1 & Hdom_m2 & Hsub_m1 & Hsub_m2 & Hsum_m &
      Hext1 & Hle1 & Hext2 & Hle2).
  eapply res_models_plus_intro_from_models; [exact Hsum_m | |].
  - eapply Hψ1; [exact Hdom_m1 | exact Hsub_m1 | exact Hext1 |].
    eapply res_models_kripke; [exact Hle1 | exact Hn1].
  - eapply Hψ2; [exact Hdom_m2 | exact Hsub_m2 | exact Hext2 |].
    eapply res_models_kripke; [exact Hle2 | exact Hn2].
Qed.

Lemma res_models_resource_atom_extend_iff
    (m : WfWorldT) (F : fiber_extension (V := V))
    (my : WfWorldT) (D : lvset)
    (P : LWorldOn (V := V) D → Prop) :
  res_extend_by m F my →
  lvars_fv D ⊆ world_dom (m : WorldT) →
  (res_models my (FResourceAtom D P) ↔
   res_models m (FResourceAtom D P)).
Proof.
  intros Hext Hfv.
  apply res_models_extend_base_iff with (F := F); [exact Hext |].
  rewrite formula_fv_FResourceAtom_lvars. exact Hfv.
Qed.

Lemma res_models_forall_map_same_fv_by_extension
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ = formula_fv ψ →
  formula_scoped_in_world m (FForall ψ) →
  (∀ (y : atom) (F : fiber_extension (V := V)) (my : WfWorldT),
    ext_in F = formula_fv φ →
    ext_out F = {[y]} →
    res_extend_by m F my →
  res_models my (formula_open 0 y φ) →
  res_models my (formula_open 0 y ψ)) →
  res_models m (FForall φ) →
  res_models m (FForall ψ).
Proof.
  intros Hfv Hscope Hmap Hforall.
  eapply res_models_forall_map_same_fv; eauto.
Qed.

Lemma res_models_forall_transport_by_extension
    (m n : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ = formula_fv ψ →
  formula_scoped_in_world n (FForall ψ) →
  (∀ (y : atom) (F : fiber_extension (V := V))
      (my ny : WfWorldT),
    ext_in F = formula_fv φ →
    ext_out F = {[y]} →
    res_extend_by m F my →
    res_extend_by n F ny →
  res_models my (formula_open 0 y φ) →
  res_models ny (formula_open 0 y ψ)) →
  res_models m (FForall φ) →
  res_models n (FForall ψ).
Proof.
  intros Hfv Hscope Htransport Hforall.
  eapply res_models_forall_transport; eauto.
Qed.

Lemma res_models_one_point_extension_pushout
    (m n my : WfWorldT) (y : atom) (φ : FormulaT) :
  m ⊑ n →
  y ∉ world_dom (n : WorldT) →
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} →
  res_restrict my (world_dom (m : WorldT)) = m →
  res_models my φ →
  ∃ ny : WfWorldT,
    world_dom (ny : WorldT) = world_dom (n : WorldT) ∪ {[y]} ∧
    res_restrict ny (world_dom (n : WorldT)) = n ∧
    my ⊑ ny ∧
    res_models ny φ.
Proof.
  intros Hle Hy Hdom Hrestrict Hmodel.
  destruct (res_one_point_extension_pushout m n my y Hle Hy Hdom Hrestrict)
    as [ny [Hdom_ny [Hrestrict_ny Hle_my]]].
  exists ny. repeat split; eauto.
  eapply res_models_kripke; eauto.
Qed.

End FormulaWorldExtension.
