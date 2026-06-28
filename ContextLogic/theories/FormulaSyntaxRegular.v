From ContextLogic Require Export FormulaSyntaxCore.
From CoreLang Require Import Prelude.
From ContextBase Require Import BaseTactics LogicVarOpenEnv LogicVarShift.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.

(** * Regular facts for formula syntax. *)

Section Formula.

Context {V : Type} `{ValueSig V}.

Local Notation QualifierT := (qualifier (V := V)) (only parsing).
Local Notation LStoreT := (gmap logic_var V) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation FTrue := (@FTrue V) (only parsing).
Local Notation FFalse := (@FFalse V) (only parsing).
Implicit Types p q φ ψ P : FormulaT.
Implicit Types a : QualifierT.

Lemma formula_fv_true :
  formula_fv FTrue = ∅.
Proof. reflexivity. Qed.

Lemma formula_fv_false :
  formula_fv FFalse = ∅.
Proof. reflexivity. Qed.

Lemma formula_fv_atom (q : QualifierT) :
  formula_fv (FAtom q) = lvars_fv (qual_vars q).
Proof. unfold formula_fv, formula_lvars; cbn [formula_lvars_at]. apply lvars_fv_lvars_at_depth. Qed.

Lemma formula_fv_and p q :
  formula_fv (FAnd p q) = formula_fv p ∪ formula_fv q.
Proof. unfold formula_fv, formula_lvars; cbn [formula_lvars_at]; apply lvars_fv_union. Qed.

Lemma formula_fv_or p q :
  formula_fv (FOr p q) = formula_fv p ∪ formula_fv q.
Proof. unfold formula_fv, formula_lvars; cbn [formula_lvars_at]; apply lvars_fv_union. Qed.

Lemma formula_fv_impl p q :
  formula_fv (FImpl p q) = formula_fv p ∪ formula_fv q.
Proof. unfold formula_fv, formula_lvars; cbn [formula_lvars_at]; apply lvars_fv_union. Qed.

Lemma formula_fv_star p q :
  formula_fv (FStar p q) = formula_fv p ∪ formula_fv q.
Proof. unfold formula_fv, formula_lvars; cbn [formula_lvars_at]; apply lvars_fv_union. Qed.

Lemma formula_fv_fbwand d p q :
  formula_fv (FBWand d p q) =
  lvars_fv (formula_lvars_at d p) ∪ lvars_fv (formula_lvars_at d q).
Proof. unfold formula_fv, formula_lvars; cbn [formula_lvars_at]; apply lvars_fv_union. Qed.

Lemma formula_fv_plus p q :
  formula_fv (FPlus p q) = formula_fv p ∪ formula_fv q.
Proof. unfold formula_fv, formula_lvars; cbn [formula_lvars_at]; apply lvars_fv_union. Qed.

Lemma formula_fv_forall p :
  formula_fv (FForall p) = lvars_fv (formula_lvars_at 1 p).
Proof. reflexivity. Qed.

Lemma formula_fv_over p :
  formula_fv (FOver p) = formula_fv p.
Proof. reflexivity. Qed.

Lemma formula_fv_under p :
  formula_fv (FUnder p) = formula_fv p.
Proof. reflexivity. Qed.

Lemma formula_fv_persist p :
  formula_fv (FPersist p) = formula_fv p.
Proof. reflexivity. Qed.

Lemma formula_fv_fibvars D p :
  formula_fv (FFibVars D p) = lvars_fv D ∪ formula_fv p.
Proof.
  unfold formula_fv, formula_lvars; cbn [formula_lvars_at].
  rewrite lvars_fv_union, lvars_fv_lvars_at_depth. reflexivity.
Qed.

Lemma formula_lvars_at_fv d (φ : FormulaT) :
  lvars_fv (formula_lvars_at d φ) = formula_fv φ.
Proof.
  induction φ in d |- *; cbn [formula_lvars_at].
  - rewrite formula_fv_true. reflexivity.
  - rewrite formula_fv_false. reflexivity.
  - rewrite lvars_fv_lvars_at_depth, formula_fv_atom. reflexivity.
  - rewrite lvars_fv_union, (IHφ1 d), (IHφ2 d), formula_fv_and.
    reflexivity.
  - rewrite lvars_fv_union, (IHφ1 d), (IHφ2 d), formula_fv_or.
    reflexivity.
  - rewrite lvars_fv_union, (IHφ1 d), (IHφ2 d), formula_fv_impl.
    reflexivity.
  - rewrite lvars_fv_union, (IHφ1 d), (IHφ2 d), formula_fv_star.
    reflexivity.
  - rewrite lvars_fv_union, (IHφ1 (d + d0)), (IHφ2 (d + d0)).
    rewrite formula_fv_fbwand, (IHφ1 d0), (IHφ2 d0). reflexivity.
  - rewrite lvars_fv_union, (IHφ1 d), (IHφ2 d), formula_fv_plus.
    reflexivity.
  - rewrite (IHφ (S d)), formula_fv_forall, (IHφ 1). reflexivity.
  - rewrite (IHφ d), formula_fv_over. reflexivity.
  - rewrite (IHφ d), formula_fv_under. reflexivity.
  - rewrite (IHφ d), formula_fv_persist. reflexivity.
  - rewrite lvars_fv_union, lvars_fv_lvars_at_depth, (IHφ d),
      formula_fv_fibvars.
    reflexivity.
Qed.


Lemma formula_msubst_store_fibvars σ D φ :
  formula_msubst_store σ (FFibVars D φ) =
  FFibVars (D ∖ lvars_of_atoms (dom (σ : Store (V := V))))
    (formula_msubst_store σ φ).
Proof.
  unfold formula_msubst_store. cbn [formula_mlsubst].
  rewrite dom_lstore_lift_free. reflexivity.
Qed.

Lemma lvars_fv_difference_atoms (D : lvset) (X : aset) :
  lvars_fv (D ∖ lvars_of_atoms X) = lvars_fv D ∖ X.
Proof.
  apply set_eq. intros x.
  rewrite elem_of_difference.
  split.
  - intros Hx.
    split.
    + apply lvars_fv_elem.
      apply lvars_fv_elem in Hx.
      set_solver.
    + intros Hbad.
      apply lvars_fv_elem in Hx.
      apply elem_of_difference in Hx as [_ Hnot].
      apply Hnot.
      unfold lvars_of_atoms.
      apply elem_of_map. exists x. split; [reflexivity|exact Hbad].
  - intros [HxD HxX].
    rewrite lvars_fv_elem.
    apply elem_of_difference. split.
    + apply lvars_fv_elem in HxD. exact HxD.
    + intros Hbad. apply HxX.
      unfold lvars_of_atoms in Hbad.
      apply elem_of_map in Hbad as [a [Heq Ha]].
      inversion Heq. subst a. exact Ha.
Qed.

Lemma formula_mlsubst_fiber_atom ρ (q : QualifierT) :
  formula_mlsubst ρ (FFiberAtom q) =
  FFiberAtom (qual_mlsubst ρ q).
Proof.
  unfold FFiberAtom. cbn [formula_mlsubst].
  destruct q. reflexivity.
Qed.

Lemma formula_msubst_store_fiber_atom σ (q : QualifierT) :
  formula_msubst_store σ (FFiberAtom q) =
  FFiberAtom (qual_msubst_store σ q).
Proof. apply formula_mlsubst_fiber_atom. Qed.

Lemma formula_fv_fiber_atom (q : QualifierT) :
  formula_fv (FFiberAtom q) = qual_dom q.
Proof.
  unfold FFiberAtom.
  rewrite formula_fv_fibvars, formula_fv_atom.
  unfold qual_dom. set_solver.
Qed.

Lemma formula_msubst_store_empty (σ : Store (V := V)) (φ : FormulaT) :
  dom (σ : gmap atom V) = ∅ ->
  formula_msubst_store σ φ = φ.
Proof.
  intros Hdom.
  assert (Hσ : (σ : gmap atom V) = ∅).
  {
    apply (map_eq (M:=gmap atom)). intros x.
    apply not_elem_of_dom.
    rewrite Hdom. set_solver.
  }
  rewrite Hσ.
  unfold formula_msubst_store, lstore_lift_free.
  rewrite kmap_empty.
  induction φ; cbn [formula_mlsubst];
    try (rewrite ?IHφ1, ?IHφ2, ?IHφ; reflexivity).
  - rewrite qual_mlsubst_empty. reflexivity.
  - rewrite dom_empty_L, difference_empty_L, IHφ. reflexivity.
Qed.

Lemma formula_mlsubst_merge ρ_outer ρ_inner φ :
  dom (ρ_outer : gmap logic_var V) ##
    dom (ρ_inner : gmap logic_var V) ->
  formula_mlsubst ρ_inner (formula_mlsubst ρ_outer φ) =
  formula_mlsubst (ρ_outer ∪ ρ_inner) φ.
Proof.
  intros Hdisj.
  induction φ; cbn [formula_mlsubst];
    try (rewrite ?IHφ1, ?IHφ2, ?IHφ; reflexivity).
  - rewrite qual_mlsubst_merge; [reflexivity|exact Hdisj].
  - f_equal.
    + set_solver.
    + exact IHφ.
Qed.

Lemma formula_msubst_store_merge σ_outer σ_inner φ :
  dom (σ_outer : Store (V := V)) ##
    dom (σ_inner : Store (V := V)) ->
  formula_msubst_store σ_inner (formula_msubst_store σ_outer φ) =
  formula_msubst_store (σ_outer ∪ σ_inner) φ.
Proof.
  intros Hdisj.
  unfold formula_msubst_store.
  rewrite lstore_lift_free_union.
  apply formula_mlsubst_merge.
  rewrite !dom_lstore_lift_free.
  unfold lvars_of_atoms.
  set_solver.
Qed.

Lemma formula_mlsubst_preserves_measure ρ φ :
  formula_measure (formula_mlsubst ρ φ) = formula_measure φ.
Proof.
  induction φ; simpl; eauto; lia.
Qed.

Lemma formula_msubst_store_preserves_measure σ φ :
  formula_measure (formula_msubst_store σ φ) = formula_measure φ.
Proof. apply formula_mlsubst_preserves_measure. Qed.

Lemma formula_lvars_at_msubst_store σ φ depth :
  formula_lvars_at depth (formula_msubst_store σ φ) =
  formula_lvars_at depth φ ∖ lvars_of_atoms (dom (σ : Store (V := V))).
Proof.
  revert depth.
  induction φ; intros depth;
    unfold formula_msubst_store in *;
    cbn [formula_mlsubst formula_lvars_at].
  all: try reflexivity.
  all: try match goal with
  | |- context[qual_mlsubst (lstore_lift_free ?sigma) ?q] =>
      destruct q as [D P]; cbn [qual_mlsubst qual_vars];
      rewrite dom_lstore_lift_free; apply lvars_at_depth_difference_of_atoms
  end.
  all: try match goal with
  | q : qualifier (V := V) |- _ =>
      destruct q; cbn [qual_mlsubst qual_vars];
      rewrite dom_lstore_lift_free;
      apply lvars_at_depth_difference_of_atoms
  end.
  all: try (repeat match goal with
    | H : forall depth, formula_lvars_at depth
        (formula_mlsubst (lstore_lift_free ?σ) ?p) = _ |- _ =>
        rewrite H
    end).
  all: better_set_solver.
  destruct a as [D P]; cbn [qual_mlsubst qual_vars].
  change (lvars_at_depth depth (D ∖ dom (lstore_lift_free σ)) =
    lvars_at_depth depth D ∖ lvars_of_atoms (dom σ)).
  rewrite dom_lstore_lift_free.
  apply lvars_at_depth_difference_of_atoms.
  all: rewrite ?dom_lstore_lift_free, ?lvars_at_depth_difference_of_atoms;
    better_set_solver.
Qed.

Lemma formula_msubst_store_fv σ φ :
  formula_fv (formula_msubst_store σ φ) =
  formula_fv φ ∖ dom (σ : Store (V := V)).
Proof.
  unfold formula_fv, formula_lvars.
  rewrite formula_lvars_at_msubst_store.
  apply lvars_fv_difference_atoms.
Qed.

Lemma formula_mlsubst_fv_subset ρ φ :
  formula_fv (formula_mlsubst ρ φ) ⊆ formula_fv φ.
Proof.
  assert (Hsubset : forall depth,
      formula_lvars_at depth (formula_mlsubst ρ φ) ⊆
      formula_lvars_at depth φ).
  {
    induction φ; intros depth;
      cbn [formula_mlsubst formula_lvars_at];
      try solve [
        set_solver
      | destruct a as [D P]; cbn [qual_mlsubst qual_vars];
        apply lvars_at_depth_mono; set_solver
      | match goal with
        | H1 : forall depth, formula_lvars_at depth (formula_mlsubst ρ ?p) ⊆ formula_lvars_at depth ?p,
          H2 : forall depth, formula_lvars_at depth (formula_mlsubst ρ ?q) ⊆ formula_lvars_at depth ?q
          |- formula_lvars_at ?δ (formula_mlsubst ρ ?p) ∪
               formula_lvars_at ?δ (formula_mlsubst ρ ?q) ⊆ _ =>
            specialize (H1 δ); specialize (H2 δ); set_solver
        end
      | match goal with
        | H : forall depth, formula_lvars_at depth (formula_mlsubst ρ ?p) ⊆ formula_lvars_at depth ?p
          |- formula_lvars_at ?δ (formula_mlsubst ρ ?p) ⊆ _ =>
            specialize (H δ); set_solver
        end
      | match goal with
        | H : forall depth, formula_lvars_at depth (formula_mlsubst ρ ?p) ⊆ formula_lvars_at depth ?p
          |- lvars_at_depth ?δ (?D ∖ dom (ρ : gmap logic_var V)) ∪
               formula_lvars_at ?δ (formula_mlsubst ρ ?p) ⊆ _ =>
            pose proof (lvars_at_depth_mono δ
              (D ∖ dom (ρ : gmap logic_var V)) D ltac:(set_solver));
            specialize (H δ); set_solver
        end
      ].
  }
  unfold formula_fv, formula_lvars.
  apply lvars_fv_mono. apply Hsubset.
Qed.

Lemma formula_msubst_store_fv_subset σ φ :
  formula_fv (formula_msubst_store σ φ) ⊆ formula_fv φ.
Proof. apply formula_mlsubst_fv_subset. Qed.


Lemma formula_open_true k x :
  formula_open k x FTrue = FTrue.
Proof. reflexivity. Qed.

Lemma formula_open_false k x :
  formula_open k x FFalse = FFalse.
Proof. reflexivity. Qed.

Lemma formula_open_atom k x (q : QualifierT) :
  formula_open k x (FAtom q) = FAtom (qual_open_atom k x q).
Proof. reflexivity. Qed.

Lemma formula_open_and k x p q :
  formula_open k x (FAnd p q) =
  FAnd (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_or k x p q :
  formula_open k x (FOr p q) =
  FOr (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_impl k x p q :
  formula_open k x (FImpl p q) =
  FImpl (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_star k x p q :
  formula_open k x (FStar p q) =
  FStar (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_fbwand k x d p q :
  formula_open k x (FBWand d p q) =
  FBWand d (formula_open (k + d) x p) (formula_open (k + d) x q).
Proof. reflexivity. Qed.

Lemma formula_open_plus k x p q :
  formula_open k x (FPlus p q) =
  FPlus (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_forall k x p :
  formula_open k x (FForall p) =
  FForall (formula_open (S k) x p).
Proof. reflexivity. Qed.

Lemma formula_open_over k x p :
  formula_open k x (FOver p) =
  FOver (formula_open k x p).
Proof. reflexivity. Qed.

Lemma formula_open_under k x p :
  formula_open k x (FUnder p) =
  FUnder (formula_open k x p).
Proof. reflexivity. Qed.

Lemma formula_open_persist k x p :
  formula_open k x (FPersist p) =
  FPersist (formula_open k x p).
Proof. reflexivity. Qed.

Lemma formula_open_fibvars k x D p :
  formula_open k x (FFibVars D p) =
  FFibVars (lvars_open k x D) (formula_open k x p).
Proof. reflexivity. Qed.

Lemma formula_open_fiber_atom k x (q : QualifierT) :
  formula_open k x (FFiberAtom q) =
  FFiberAtom (qual_open_atom k x q).
Proof.
  unfold FFiberAtom. cbn [formula_open].
  rewrite qual_open_atom_vars. reflexivity.
Qed.

Lemma formula_open_preserves_measure k x φ :
  formula_measure (formula_open k x φ) = formula_measure φ.
Proof.
  revert k. induction φ; intros k; simpl; eauto; lia.
Qed.

Lemma formula_mlsubst_open_fresh ρ k x φ :
  (forall j, LVBound j ∉ dom (ρ : gmap logic_var V)) ->
  LVFree x ∉ dom (ρ : gmap logic_var V) ->
  formula_mlsubst ρ (formula_open k x φ) =
  formula_open k x (formula_mlsubst ρ φ).
Proof.
  intros Hbound Hfree.
  induction φ in k |- *; cbn [formula_open formula_mlsubst];
    try solve [rewrite ?IHφ1, ?IHφ2, ?IHφ; eauto; reflexivity].
  - rewrite qual_mlsubst_open_atom_fresh; [reflexivity|exact Hbound|exact Hfree].
  - rewrite IHφ.
    match goal with
    | |- FFibVars ?A ?P = FFibVars ?B ?P =>
        replace B with A; [reflexivity|]
    end.
    symmetry.
    apply set_swap_difference_fresh; [apply Hbound|exact Hfree].
Qed.

Lemma formula_msubst_store_open_fresh σ k x φ :
  x ∉ dom (σ : Store (V := V)) ->
  formula_msubst_store σ (formula_open k x φ) =
  formula_open k x (formula_msubst_store σ φ).
Proof.
  intros Hx.
  unfold formula_msubst_store.
  apply formula_mlsubst_open_fresh.
  - intros j Hj.
    rewrite dom_lstore_lift_free in Hj.
    unfold lvars_of_atoms in Hj.
    apply elem_of_map in Hj as [a [Hbad _]]. discriminate.
  - rewrite dom_lstore_lift_free.
    unfold lvars_of_atoms.
    intros Hbad. apply elem_of_map in Hbad as [a [Heq Ha]].
    inversion Heq. subst. exact (Hx Ha).
Qed.

Lemma formula_atom_swap_preserves_measure x y φ :
  formula_measure (formula_atom_swap x y φ) = formula_measure φ.
Proof.
  induction φ; simpl; eauto; lia.
Qed.

Lemma formula_fv_atom_swap x y φ :
  formula_fv (formula_atom_swap x y φ) =
  set_swap x y (formula_fv φ).
Proof.
  induction φ; cbn [formula_atom_swap].
  - rewrite formula_fv_true, set_swap_empty. reflexivity.
  - rewrite formula_fv_false, set_swap_empty. reflexivity.
  - rewrite !formula_fv_atom.
    destruct a as [D P]. cbn [qual_atom_swap qual_vars].
    apply lvars_fv_swap.
  - rewrite formula_fv_and, IHφ1, IHφ2, formula_fv_and, set_swap_union.
    reflexivity.
  - rewrite formula_fv_or, IHφ1, IHφ2, formula_fv_or, set_swap_union.
    reflexivity.
  - rewrite formula_fv_impl, IHφ1, IHφ2, formula_fv_impl, set_swap_union.
    reflexivity.
  - rewrite formula_fv_star, IHφ1, IHφ2, formula_fv_star, set_swap_union.
    reflexivity.
  - rewrite !formula_fv_fbwand.
    rewrite !formula_lvars_at_fv.
    rewrite IHφ1, IHφ2.
    rewrite set_swap_union. reflexivity.
  - rewrite formula_fv_plus, IHφ1, IHφ2, formula_fv_plus, set_swap_union.
    reflexivity.
  - rewrite !formula_fv_forall.
    rewrite !formula_lvars_at_fv. exact IHφ.
  - rewrite formula_fv_over, IHφ, formula_fv_over. reflexivity.
  - rewrite formula_fv_under, IHφ, formula_fv_under. reflexivity.
  - rewrite formula_fv_persist, IHφ, formula_fv_persist. reflexivity.
  - rewrite !formula_fv_fibvars.
    rewrite lvars_fv_swap, IHφ, set_swap_union. reflexivity.
Qed.

Lemma formula_atom_swap_involutive x y φ :
  formula_atom_swap x y (formula_atom_swap x y φ) = φ.
Proof.
  induction φ; cbn [formula_atom_swap]; try reflexivity;
    try (rewrite ?IHφ1, ?IHφ2, ?IHφ; reflexivity).
  - f_equal. apply qual_atom_swap_involutive.
  - rewrite set_swap_involutive, IHφ. reflexivity.
Qed.

Lemma formula_atom_swap_fresh_id x y φ :
  x ∉ formula_fv φ ->
  y ∉ formula_fv φ ->
  formula_atom_swap x y φ = φ.
Proof.
  induction φ; intros Hx Hy; cbn [formula_atom_swap]; try reflexivity.
  - rewrite formula_fv_atom in Hx, Hy.
    f_equal. apply qual_atom_swap_fresh_id; assumption.
  - rewrite formula_fv_and in Hx, Hy.
    rewrite IHφ1, IHφ2; set_solver.
  - rewrite formula_fv_or in Hx, Hy.
    rewrite IHφ1, IHφ2; set_solver.
  - rewrite formula_fv_impl in Hx, Hy.
    rewrite IHφ1, IHφ2; set_solver.
  - rewrite formula_fv_star in Hx, Hy.
    rewrite IHφ1, IHφ2; set_solver.
  - rewrite formula_fv_fbwand in Hx, Hy.
    rewrite !formula_lvars_at_fv in Hx, Hy.
    rewrite IHφ1, IHφ2; set_solver.
  - rewrite formula_fv_plus in Hx, Hy.
    rewrite IHφ1, IHφ2; set_solver.
  - rewrite formula_fv_forall in Hx, Hy.
    rewrite formula_lvars_at_fv in Hx, Hy.
    rewrite (IHφ Hx Hy). reflexivity.
  - rewrite formula_fv_over in Hx, Hy.
    rewrite (IHφ Hx Hy). reflexivity.
  - rewrite formula_fv_under in Hx, Hy.
    rewrite (IHφ Hx Hy). reflexivity.
  - rewrite formula_fv_persist in Hx, Hy.
    rewrite (IHφ Hx Hy). reflexivity.
  - rewrite formula_fv_fibvars in Hx, Hy.
    rewrite lvars_swap_fresh, IHφ; set_solver.
Qed.

Lemma formula_atom_swap_open_conjugate k x y z φ :
  formula_atom_swap x y (formula_open k (swap x y z) φ) =
  formula_open k z (formula_atom_swap x y φ).
Proof.
  induction φ in k |- *; cbn [formula_atom_swap formula_open]; try reflexivity.
  - f_equal. apply qual_atom_swap_open_conjugate.
  - rewrite IHφ1, IHφ2. reflexivity.
  - rewrite IHφ1, IHφ2. reflexivity.
  - rewrite IHφ1, IHφ2. reflexivity.
  - rewrite IHφ1, IHφ2. reflexivity.
  - rewrite IHφ1, IHφ2. reflexivity.
  - rewrite IHφ1, IHφ2. reflexivity.
  - rewrite IHφ. reflexivity.
  - rewrite IHφ. reflexivity.
  - rewrite IHφ. reflexivity.
  - rewrite IHφ. reflexivity.
  - rewrite lvars_swap_open_conjugate, IHφ. reflexivity.
Qed.

Lemma formula_atom_swap_open_fresh x y φ :
  x ∉ formula_fv φ ->
  y ∉ formula_fv φ ->
  formula_atom_swap x y (formula_open 0 x φ) = formula_open 0 y φ.
Proof.
  intros Hx Hy.
  pose proof (formula_atom_swap_open_conjugate 0 x y y φ) as Hopen.
  rewrite swap_r in Hopen.
  rewrite Hopen.
  rewrite formula_atom_swap_fresh_id by assumption.
  reflexivity.
Qed.

Lemma formula_atom_swap_mlsubst x y (ρ : LStoreT) φ :
  formula_atom_swap x y (formula_mlsubst ρ φ) =
  formula_mlsubst (lvar_store_swap x y ρ) (formula_atom_swap x y φ).
Proof.
  induction φ; cbn [formula_atom_swap formula_mlsubst]; try reflexivity;
    try (rewrite ?IHφ1, ?IHφ2, ?IHφ; reflexivity).
  - f_equal. apply qual_atom_swap_mlsubst.
  - f_equal.
    + transitivity (set_swap (LVFree x) (LVFree y) D ∖
        set_swap (LVFree x) (LVFree y) (dom (ρ : LStoreT))).
      * apply set_swap_difference.
      * apply (f_equal (fun R =>
          set_swap (LVFree x) (LVFree y) D ∖ R)).
        symmetry. apply lvar_store_swap_dom.
    + exact IHφ.
Qed.

Lemma formula_atom_swap_msubst_store x y (σ : Store (V := V)) φ :
  formula_atom_swap x y (formula_msubst_store σ φ) =
  formula_msubst_store (storeA_swap x y σ) (formula_atom_swap x y φ).
Proof.
  unfold formula_msubst_store.
  rewrite formula_atom_swap_mlsubst.
  rewrite lstore_lift_free_swap.
  reflexivity.
Qed.

Lemma formula_open_commute_fresh i j x y φ :
  i <> j ->
  x <> y ->
  formula_open i x (formula_open j y φ) =
  formula_open j y (formula_open i x φ).
Proof.
  intros Hij Hxy.
  induction φ in i, j, Hij |- *; cbn [formula_open]; try reflexivity.
  - rewrite qual_open_atom_commute_fresh by assumption. reflexivity.
  - rewrite IHφ1 by assumption. rewrite IHφ2 by assumption. reflexivity.
  - rewrite IHφ1 by assumption. rewrite IHφ2 by assumption. reflexivity.
  - rewrite IHφ1 by assumption. rewrite IHφ2 by assumption. reflexivity.
  - rewrite IHφ1 by assumption. rewrite IHφ2 by assumption. reflexivity.
  - rewrite IHφ1 by (try lia; exact Hxy).
    rewrite IHφ2 by (try lia; exact Hxy). reflexivity.
  - rewrite IHφ1 by assumption. rewrite IHφ2 by assumption. reflexivity.
  - rewrite IHφ by (try lia; exact Hxy). reflexivity.
  - rewrite IHφ by assumption. reflexivity.
  - rewrite IHφ by assumption. reflexivity.
  - rewrite IHφ by assumption. reflexivity.
  - rewrite lvars_open_commute_fresh by assumption.
    rewrite IHφ by assumption. reflexivity.
Qed.


Lemma formula_open_env_preserves_measure η φ :
  formula_measure (formula_open_env η φ) = formula_measure φ.
Proof.
  unfold formula_open_env.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite map_fold_empty. reflexivity.
  - rewrite Hfold, formula_open_preserves_measure. exact IH.
Qed.

Lemma formula_open_env_empty φ :
  formula_open_env ∅ φ = φ.
Proof.
  unfold formula_open_env. rewrite map_fold_empty. reflexivity.
Qed.

Lemma formula_open_env_singleton k x φ :
  formula_open_env (<[k := x]> ∅) φ = formula_open k x φ.
Proof.
  unfold formula_open_env.
  change (<[k := x]> (∅ : gmap nat atom)) with ({[k := x]} : gmap nat atom).
  rewrite map_fold_singleton. reflexivity.
Qed.

Lemma formula_open_env_insert_fresh η k x φ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  formula_open_env (<[k := x]> η) φ =
  formula_open k x (formula_open_env η φ).
Proof.
  intros Hfresh Havoid Hinj.
  unfold formula_open_env.
  apply (map_fold_insert_L (M:=gmap nat) (A:=atom) (B:=Formula)
    (fun k x acc => formula_open k x acc) φ k x η).
  - intros i j xi xj acc Hij Hi Hj.
    apply formula_open_commute_fresh; [exact Hij|].
    intros Heq. subst xj.
    pose proof (open_env_values_inj_insert k x η Hfresh Havoid Hinj)
      as Hinj'.
    apply Hij. eapply Hinj'; eassumption.
  - exact Hfresh.
Qed.

Lemma formula_atom_swap_open_env_fresh x y η φ :
  open_env_atoms η ## ({[x]} ∪ {[y]}) ->
  open_env_values_inj η ->
  formula_atom_swap x y (formula_open_env η φ) =
  formula_open_env η (formula_atom_swap x y φ).
Proof.
  induction η as [|k a η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros _ _. rewrite formula_open_env_empty, formula_open_env_empty.
    reflexivity.
  - intros Hatoms Hinj.
    pose proof (open_env_values_inj_insert_inv η k a Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_env_atoms_insert in Hatoms by exact Hfresh.
    assert (Ha_xy : swap x y a = a).
    {
      apply swap_fresh; intros ->; set_solver.
    }
    assert (Hatomsη : open_env_atoms η ## ({[x]} ∪ {[y]})) by set_solver.
    rewrite (formula_open_env_insert_fresh η k a φ Hfresh Havoid Hinjη).
    rewrite (formula_open_env_insert_fresh η k a (formula_atom_swap x y φ)
      Hfresh Havoid Hinjη).
    rewrite <- Ha_xy at 1.
    rewrite formula_atom_swap_open_conjugate.
    rewrite IH; [reflexivity | exact Hatomsη | exact Hinjη].
Qed.

Lemma formula_open_env_true η :
  formula_open_env η FTrue = FTrue.
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) FTrue η = FTrue)
    _ _ η).
  - rewrite map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH. rewrite Hfold, IH. reflexivity.
Qed.

Lemma formula_open_env_false η :
  formula_open_env η FFalse = FFalse.
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) FFalse η = FFalse)
    _ _ η).
  - rewrite map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH. rewrite Hfold, IH. reflexivity.
Qed.

Lemma formula_open_env_and η φ ψ :
  formula_open_env η (FAnd φ ψ) =
  FAnd (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FAnd φ ψ) η =
      FAnd
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_or η φ ψ :
  formula_open_env η (FOr φ ψ) =
  FOr (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FOr φ ψ) η =
      FOr
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_impl η φ ψ :
  formula_open_env η (FImpl φ ψ) =
  FImpl (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FImpl φ ψ) η =
      FImpl
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_star η φ ψ :
  formula_open_env η (FStar φ ψ) =
  FStar (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FStar φ ψ) η =
      FStar
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_fbwand η d φ ψ :
  open_env_values_inj η ->
  formula_open_env η (FBWand d φ ψ) =
  FBWand d
    (formula_open_env (open_env_lift_by d η) φ)
    (formula_open_env (open_env_lift_by d η) ψ).
Proof.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros _. rewrite formula_open_env_empty, open_env_lift_by_empty,
      !formula_open_env_empty.
    reflexivity.
  - intros Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by exact Hinjη.
    cbn [formula_open].
    rewrite open_env_lift_by_insert.
    assert (Hlift_fresh :
      open_env_lift_by d η !! (k + d) = None).
    { apply open_env_lift_by_lookup_none. exact Hfresh. }
    assert (Hlift_avoid :
      open_env_avoids_atom x (open_env_lift_by d η)).
    { apply open_env_avoids_atom_lift_by. exact Havoid. }
    assert (Hlift_inj :
      open_env_values_inj (open_env_lift_by d η)).
    { apply open_env_values_inj_lift_by. exact Hinjη. }
    rewrite (formula_open_env_insert_fresh
      (open_env_lift_by d η) (k + d) x φ
      Hlift_fresh Hlift_avoid Hlift_inj).
    rewrite (formula_open_env_insert_fresh
      (open_env_lift_by d η) (k + d) x ψ
      Hlift_fresh Hlift_avoid Hlift_inj).
    reflexivity.
Qed.

Lemma formula_open_env_plus η φ ψ :
  formula_open_env η (FPlus φ ψ) =
  FPlus (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FPlus φ ψ) η =
      FPlus
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_over η φ :
  formula_open_env η (FOver φ) =
  FOver (formula_open_env η φ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FOver φ) η =
      FOver (map_fold (fun k x acc => formula_open k x acc) φ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_under η φ :
  formula_open_env η (FUnder φ) =
  FUnder (formula_open_env η φ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FUnder φ) η =
      FUnder (map_fold (fun k x acc => formula_open k x acc) φ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_persist η φ :
  formula_open_env η (FPersist φ) =
  FPersist (formula_open_env η φ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FPersist φ) η =
      FPersist (map_fold (fun k x acc => formula_open k x acc) φ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_atom η (q : QualifierT) :
  formula_open_env η (FAtom q) = FAtom (qual_open_env η q).
Proof.
  unfold formula_open_env, qual_open_env.
  induction η as [|k x η' Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite !map_fold_empty. reflexivity.
  - rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_fibvars η D φ :
  open_env_fresh_for_lvars η D ->
  formula_open_env η (FFibVars D φ) =
  FFibVars (lvars_open_env η D) (formula_open_env η φ).
Proof.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros _. rewrite formula_open_env_empty, lvars_open_env_empty.
    reflexivity.
  - intros Henv.
    pose proof (open_env_fresh_for_lvars_insert_head η k x D Hfresh Henv)
      as Hhead.
    pose proof (open_env_fresh_for_lvars_insert_tail η k x D Hfresh Henv)
      as Htail.
    unfold formula_open_env.
    rewrite !Hfold.
    fold (formula_open_env η (FFibVars D φ)).
    fold (formula_open_env η φ).
    rewrite IH by exact Htail.
    cbn [formula_open].
    rewrite lvars_open_env_insert_fresh by (exact Hfresh || exact Hhead).
    reflexivity.
Qed.

Lemma formula_open_env_fiber_atom η (q : QualifierT) :
  open_env_fresh_for_lvars η (qual_vars q) ->
  formula_open_env η (FFiberAtom q) =
  FFiberAtom (qual_open_env η q).
Proof.
  intros Hfresh.
  unfold FFiberAtom.
  rewrite formula_open_env_fibvars by exact Hfresh.
  rewrite formula_open_env_atom.
  rewrite qual_open_env_vars by exact Hfresh.
  reflexivity.
Qed.

Lemma formula_open_env_forall η φ :
  open_env_values_inj η ->
  formula_open_env η (FForall φ) =
  FForall (formula_open_env ((kmap S η)) φ).
Proof.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros _. rewrite formula_open_env_empty, kmap_empty,
      formula_open_env_empty.
    reflexivity.
  - intros Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by exact Hinjη.
    cbn [formula_open].
    rewrite open_env_lift_insert.
    rewrite formula_open_env_insert_fresh
      by (try better_base_solver;
          try apply open_env_values_inj_lift; assumption).
    reflexivity.
Qed.

Lemma formula_open_fv_subset k x φ :
  formula_fv (formula_open k x φ) ⊆ formula_fv φ ∪ {[x]}.
Proof.
  revert k. induction φ; intros k;
    unfold formula_fv, formula_lvars in *;
    cbn [formula_lvars_at formula_open].
  - set_solver.
  - set_solver.
  - destruct a as [D P]. cbn [qual_dom qual_lvars qual_open_atom].
    rewrite !lvars_fv_lvars_at_depth.
    apply lvars_fv_open_subset.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - rewrite !lvars_fv_union.
    rewrite !(formula_lvars_at_fv _ (formula_open _ _ _)).
    rewrite !(formula_lvars_at_fv _ φ1), !(formula_lvars_at_fv _ φ2).
    specialize (IHφ1 (k + d)). specialize (IHφ2 (k + d)).
    set_solver.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - rewrite (formula_lvars_at_fv _ (formula_open _ _ φ)).
    rewrite (formula_lvars_at_fv _ φ).
    apply IHφ.
  - apply IHφ.
  - apply IHφ.
  - apply IHφ.
  - rewrite !lvars_fv_union.
    rewrite !lvars_fv_lvars_at_depth.
    pose proof (lvars_fv_open_subset k x D) as HD.
    specialize (IHφ k). set_solver.
Qed.

Lemma formula_fv_open_fibvars_qual_body_obs
    (q : QualifierT) y (P : FormulaT) :
  formula_fv P ⊆ qual_dom q ->
  formula_fv
    (formula_open 0 y
      (FFibVars (qual_vars q ∖ {[LVBound 0]}) P)) ⊆
  qual_dom q ∪ {[y]}.
Proof.
  intros HP.
  etransitivity; [apply formula_open_fv_subset|].
  rewrite formula_fv_fibvars.
  assert (HD : lvars_fv (qual_vars q ∖ {[LVBound 0]}) ⊆ qual_dom q).
  {
    intros a Ha. unfold qual_dom.
    rewrite lvars_fv_elem in Ha |- *.
    apply elem_of_difference in Ha as [Ha _]. exact Ha.
  }
  set_solver.
Qed.

Lemma formula_open_env_fv_subset η φ :
  formula_fv (formula_open_env η φ) ⊆
    formula_fv φ ∪ open_env_atoms η.
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      formula_fv (map_fold (fun k x acc => formula_open k x acc) φ η) ⊆
        formula_fv φ ∪ open_env_atoms η)
    _ _ η).
  - rewrite map_fold_empty, open_env_atoms_empty. set_solver.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold.
    pose proof (formula_open_fv_subset k x
      (map_fold (fun k x acc => formula_open k x acc) φ η')) as Hopen.
    rewrite open_env_atoms_insert by exact Hfresh.
    set_solver.
Qed.

Lemma formula_open_fv_ne k x φ z :
  z ∈ formula_fv (formula_open k x φ) ->
  z <> x ->
  z ∈ formula_fv φ.
Proof.
  intros Hz Hne.
  pose proof (formula_open_fv_subset k x φ z Hz).
  set_solver.
Qed.

Lemma formula_measure_pos (φ : FormulaT) :
  0 < formula_measure φ.
Proof. induction φ; simpl; lia. Qed.


End Formula.
