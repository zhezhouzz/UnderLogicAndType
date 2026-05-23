(** * ChoiceLogic.FormulaForall

    Derived proof principles for forall under the extension-based formula
    semantics. *)

From ChoiceLogic Require Import Formula FormulaTactics FormulaConnectives.

Section FormulaForall.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Lemma res_models_forall_intro (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ F : fiber_extension,
      ext_in F = formula_fv φ →
      ext_out F = {[y]} →
      ∀ my : WfWorldT,
        res_extend_by m F my →
        my ⊨ formula_open 0 y φ) →
  m ⊨ FForall φ.
Proof.
  unfold res_models.
  simpl. intros Hscope [L Hforall]. split; [exact Hscope |].
  exists L. intros y Hy F HFin HFout my Hext.
  pose proof (Hforall y Hy F HFin HFout my Hext) as Hbody.
  models_fuel_irrel Hbody.
Qed.

Lemma res_models_forall_iff (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) →
  (m ⊨ FForall φ ↔
    ∃ L : aset,
      ∀ y : atom, y ∉ L →
      ∀ F : fiber_extension,
        ext_in F = formula_fv φ →
        ext_out F = {[y]} →
        ∀ my : WfWorldT,
          res_extend_by m F my →
          my ⊨ formula_open 0 y φ).
Proof.
  intros Hscope. split.
  - unfold res_models. simpl.
    intros [_ [L Hforall]]. exists L.
    intros y Hy F HFin HFout my Hext.
    specialize (Hforall y Hy F HFin HFout my Hext).
    unfold res_models. models_fuel_irrel Hforall.
  - intros Hforall.
    eapply res_models_forall_intro; eauto.
Qed.

Lemma res_models_forall_map_same_fv
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ = formula_fv ψ →
  formula_scoped_in_world m (FForall ψ) →
  (∀ y F my,
    ext_in F = formula_fv φ →
    ext_out F = {[y]} →
    res_extend_by m F my →
    my ⊨ formula_open 0 y φ →
    my ⊨ formula_open 0 y ψ) →
  m ⊨ FForall φ →
  m ⊨ FForall ψ.
Proof.
  intros Hfv Hscope Hmap Hforall.
  eapply res_models_forall_intro; [exact Hscope |].
  pose proof (res_models_fuel_scoped _ _ _ Hforall) as Hφscope.
  pose proof (proj1 (res_models_forall_iff m φ Hφscope) Hforall) as [L Hbody].
  exists L. intros y Hy F HFin HFout my Hext.
  eapply (Hmap y F my); [| exact HFout | exact Hext |].
  - rewrite Hfv. exact HFin.
  - apply (Hbody y Hy F); [| exact HFout | exact Hext].
    rewrite Hfv. exact HFin.
Qed.

Lemma res_models_forall_map
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ = formula_fv ψ →
  formula_scoped_in_world m (FForall ψ) →
  (∀ (y : atom) (F : fiber_extension (V := V)) (my : WfWorldT),
    ext_in F = formula_fv φ →
    ext_out F = {[y]} →
    res_extend_by m F my →
    my ⊨ formula_open 0 y φ →
    my ⊨ formula_open 0 y ψ) →
  m ⊨ FForall φ →
  m ⊨ FForall ψ.
Proof.
  apply res_models_forall_map_same_fv.
Qed.

Lemma res_models_forall_congr_same_fv
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ = formula_fv ψ →
  formula_scoped_in_world m (FForall φ) →
  formula_scoped_in_world m (FForall ψ) →
  (∀ (y : atom) (F : fiber_extension (V := V)) (my : WfWorldT),
    ext_in F = formula_fv φ →
    ext_out F = {[y]} →
    res_extend_by m F my →
    (my ⊨ formula_open 0 y φ ↔
	     my ⊨ formula_open 0 y ψ)) →
  (m ⊨ FForall φ ↔ m ⊨ FForall ψ).
Proof.
  intros Hfv Hφscope Hψscope Hiff. split.
  - intros Hforall.
    eapply res_models_forall_map_same_fv; [exact Hfv | exact Hψscope | | exact Hforall].
    intros y F my HFin HFout Hext Hφ.
    apply (proj1 (Hiff y F my HFin HFout Hext)). exact Hφ.
  - intros Hforall.
    eapply res_models_forall_map_same_fv; [symmetry; exact Hfv | exact Hφscope | | exact Hforall].
    intros y F my HFin HFout Hext Hψ.
    apply (proj2 (Hiff y F my ltac:(rewrite Hfv; exact HFin) HFout Hext)).
    exact Hψ.
Qed.

Lemma res_models_forall_transport
    (m n : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ = formula_fv ψ →
  formula_scoped_in_world n (FForall ψ) →
  (∀ y F my ny,
    ext_in F = formula_fv φ →
    ext_out F = {[y]} →
    res_extend_by m F my →
    res_extend_by n F ny →
	    my ⊨ formula_open 0 y φ →
	    ny ⊨ formula_open 0 y ψ) →
  m ⊨ FForall φ →
  n ⊨ FForall ψ.
Proof.
  intros Hfv Hψscope Htransport Hforall.
  eapply res_models_forall_intro; [exact Hψscope |].
  pose proof (res_models_fuel_scoped _ _ _ Hforall) as Hφscope.
  pose proof (proj1 (res_models_forall_iff m φ Hφscope) Hforall)
    as [L Hbody].
  exists (L ∪ world_dom (m : WorldT)).
  intros y Hy F HFin HFout ny Hny.
  assert (HyL : y ∉ L) by set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  assert (Happ : extension_applicable F m).
  {
    constructor.
    - unfold ext_in in HFin. rewrite HFin. rewrite <- Hfv. exact Hφscope.
    - unfold ext_out in HFout. rewrite HFout. set_solver.
  }
  destruct (res_extend_by_exists m F Happ) as [my Hmy].
  eapply Htransport; [| exact HFout | exact Hmy | exact Hny |].
  - rewrite Hfv. exact HFin.
  - eapply (Hbody y HyL F); [| exact HFout | exact Hmy].
    rewrite Hfv. exact HFin.
Qed.

End FormulaForall.
