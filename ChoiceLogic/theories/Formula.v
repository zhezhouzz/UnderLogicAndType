From ChoiceLogic Require Import Prelude LogicQualifier.

(** * Choice Logic  (Definitions 1.8 and 1.9)

    Formulas are independent of the core language.  Core expressions are
    embedded into the logic by ChoiceType through ordinary logic qualifiers. *)

Section Formula.

Context {V : Type} `{ValueSig V}.

Local Notation StoreT := (gmap atom V) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := V)) (only parsing).

(** ** Formula syntax *)

Inductive Formula : Type :=
  | FTrue
  | FFalse
  | FAtom   (a : LogicQualifierT)
  | FAnd    (p q : Formula)
  | FOr     (p q : Formula)
  | FImpl   (p q : Formula)                     (* Kripke implication *)
  | FStar   (p q : Formula)                     (* separating conjunction p ∗ q *)
  | FWand   (p q : Formula)                     (* magic wand p −∗ q *)
  | FPlus   (p q : Formula)                     (* choice sum p ⊕ q *)
  | FForall (x : atom) (p : Formula)            (* ordinary universal quantifier *)
  | FExists (x : atom) (p : Formula)            (* ordinary existential quantifier *)
  | FOver   (p : Formula)                       (* overapproximation  o p *)
  | FUnder  (p : Formula)                       (* underapproximation u p *)
  | FFib    (x : atom) (p : Formula).           (* fiberwise modality *)

Fixpoint formula_stale (φ : Formula) : aset :=
  match φ with
  | FTrue | FFalse => ∅
  | FAtom q => stale q
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      formula_stale p ∪ formula_stale q
  | FForall x p | FExists x p => {[x]} ∪ formula_stale p
  | FOver p | FUnder p => formula_stale p
  | FFib x p => {[x]} ∪ formula_stale p
  end.

Fixpoint formula_fv (φ : Formula) : aset :=
  match φ with
  | FTrue | FFalse => ∅
  | FAtom q => stale q
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      formula_fv p ∪ formula_fv q
  | FForall x p | FExists x p => formula_fv p ∖ {[x]}
  | FOver p | FUnder p => formula_fv p
  | FFib x p => {[x]} ∪ formula_fv p
  end.

#[global] Instance stale_formula : Stale Formula := formula_fv.
Arguments stale_formula /.

Fixpoint formula_rename_atom (x y : atom) (φ : Formula) : Formula :=
  match φ with
  | FTrue => FTrue
  | FFalse => FFalse
  | FAtom q => FAtom (lqual_rename_atom x y q)
  | FAnd p q => FAnd (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FOr p q => FOr (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FImpl p q => FImpl (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FStar p q => FStar (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FWand p q => FWand (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FPlus p q => FPlus (formula_rename_atom x y p) (formula_rename_atom x y q)
  | FForall z p =>
      FForall (atom_rename x y z) (formula_rename_atom x y p)
  | FExists z p =>
      FExists (atom_rename x y z) (formula_rename_atom x y p)
  | FOver p => FOver (formula_rename_atom x y p)
  | FUnder p => FUnder (formula_rename_atom x y p)
  | FFib z p => FFib (atom_rename x y z) (formula_rename_atom x y p)
  end.

Fixpoint formula_swap (x y : atom) (φ : Formula) : Formula :=
  match φ with
  | FTrue => FTrue
  | FFalse => FFalse
  | FAtom q => FAtom (lqual_swap x y q)
  | FAnd p q => FAnd (formula_swap x y p) (formula_swap x y q)
  | FOr p q => FOr (formula_swap x y p) (formula_swap x y q)
  | FImpl p q => FImpl (formula_swap x y p) (formula_swap x y q)
  | FStar p q => FStar (formula_swap x y p) (formula_swap x y q)
  | FWand p q => FWand (formula_swap x y p) (formula_swap x y q)
  | FPlus p q => FPlus (formula_swap x y p) (formula_swap x y q)
  | FForall z p =>
      FForall (atom_swap x y z) (formula_swap x y p)
  | FExists z p =>
      FExists (atom_swap x y z) (formula_swap x y p)
  | FOver p => FOver (formula_swap x y p)
  | FUnder p => FUnder (formula_swap x y p)
  | FFib z p => FFib (atom_swap x y z) (formula_swap x y p)
  end.

Fixpoint formula_measure (φ : Formula) : nat :=
  match φ with
  | FTrue | FFalse | FAtom _ => 1
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      1 + formula_measure p + formula_measure q
  | FForall _ p | FExists _ p | FOver p | FUnder p | FFib _ p =>
      1 + formula_measure p
  end.

Lemma formula_rename_preserves_measure x y φ :
  formula_measure (formula_rename_atom x y φ) = formula_measure φ.
Proof.
  induction φ; simpl; eauto; lia.
Qed.

Lemma formula_swap_preserves_measure x y φ :
  formula_measure (formula_swap x y φ) = formula_measure φ.
Proof.
  induction φ; simpl; eauto; lia.
Qed.

Lemma formula_fv_swap x y φ :
  formula_fv (formula_swap x y φ) = aset_swap x y (formula_fv φ).
Proof.
  induction φ as
    [| |q|p IHp q' IHq|p IHp q' IHq|p IHp q' IHq|p IHp q' IHq
     |p IHp q' IHq|p IHp q' IHq|a p IHp|a p IHp|p IHp|p IHp|a p IHp];
    simpl; try reflexivity.
  - match goal with
    | q : logic_qualifier |- _ => destruct q; simpl; reflexivity
    end.
  - rewrite IHp, IHq, <- aset_swap_union. reflexivity.
  - rewrite IHp, IHq, <- aset_swap_union. reflexivity.
  - rewrite IHp, IHq, <- aset_swap_union. reflexivity.
  - rewrite IHp, IHq, <- aset_swap_union. reflexivity.
  - rewrite IHp, IHq, <- aset_swap_union. reflexivity.
  - rewrite IHp, IHq, <- aset_swap_union. reflexivity.
  - rewrite IHp, aset_swap_difference_singleton. reflexivity.
  - rewrite IHp, aset_swap_difference_singleton. reflexivity.
  - rewrite IHp. reflexivity.
  - rewrite IHp. reflexivity.
  - rewrite IHp, <- (aset_swap_singleton x y a), <- aset_swap_union. reflexivity.
Qed.

Lemma elem_of_aset_rename_unchanged x y z X :
  z ∈ X →
  z ≠ x →
  z ≠ y →
  z ∈ aset_rename x y X.
Proof.
  unfold aset_rename. destruct (decide (x ∈ X)); set_solver.
Qed.

Lemma formula_fv_rename_unchanged x y z φ :
  z ∈ formula_fv φ →
  z ≠ x →
  z ≠ y →
  z ∈ formula_fv (formula_rename_atom x y φ).
Proof.
  revert z.
  induction φ as
    [| |a|p IHp q IHq|p IHp q IHq|p IHp q IHq|p IHp q IHq
     |p IHp q IHq|p IHp q IHq|b p IHp|b p IHp|p IHp|p IHp|b p IHp];
    intros z Hz Hzx Hzy; simpl in *; try set_solver.
  - destruct a as [d p]. simpl in *.
    apply elem_of_aset_rename_unchanged; assumption.
  - apply elem_of_difference in Hz as [Hz Hzx0].
    apply elem_of_difference. split.
    + apply IHp; assumption.
    + unfold atom_rename. destruct (decide (b = x)); set_solver.
  - apply elem_of_difference in Hz as [Hz Hzx0].
    apply elem_of_difference. split.
    + apply IHp; assumption.
    + unfold atom_rename. destruct (decide (b = x)); set_solver.
  - apply elem_of_union in Hz as [Hz | Hz].
    + apply elem_of_union. left.
      unfold atom_rename. destruct (decide (b = x)); set_solver.
    + apply elem_of_union. right. apply IHp; assumption.
Qed.

Lemma formula_measure_pos (φ : Formula) :
  0 < formula_measure φ.
Proof. induction φ; simpl; lia. Qed.

(** [fresh_forall D body] chooses a syntactic representative for an explicit
    formula binder.  The representative is not semantically privileged:
    [FForall]'s satisfaction relation later renames it to every sufficiently
    fresh atom. *)
Definition fresh_forall (D : aset) (body : atom → Formula) : Formula :=
  let x := fresh_for D in
  FForall x (body x).

(** A formula can only be interpreted at worlds that already track every free
    coordinate it may inspect.  Explicit quantifiers remove their representative
    binder from this set; the bound coordinate is introduced by their semantic
    one-coordinate extension. *)
Definition formula_scoped_in_world
    (ρ : StoreT)
    (m : WfWorldT)
    (φ : Formula) : Prop :=
  dom ρ ∪ formula_fv φ ⊆ world_dom m.

Lemma formula_scoped_res_subset
    (ρ : StoreT) (m m' : WfWorldT) (φ : Formula) :
  formula_scoped_in_world ρ m φ →
  res_subset m m' →
  formula_scoped_in_world ρ m' φ.
Proof.
  unfold formula_scoped_in_world, res_subset.
  intros Hscope [Hdom _]. rewrite <- Hdom. exact Hscope.
Qed.

Lemma formula_scoped_world_dom_eq
    (ρ : StoreT) (m m' : WfWorldT) (φ : Formula) :
  world_dom m = world_dom m' →
  formula_scoped_in_world ρ m φ →
  formula_scoped_in_world ρ m' φ.
Proof.
  unfold formula_scoped_in_world. intros Hdom Hscope. rewrite <- Hdom.
  exact Hscope.
Qed.

(** ** Satisfaction relation *)

Fixpoint res_models_with_store_fuel
    (gas : nat)
    (ρ : StoreT)
    (m : WfWorldT)
    (φ : Formula) : Prop :=
  match gas with
  | 0 => False
  | S gas' =>
  formula_scoped_in_world ρ m φ ∧
  match φ with

  (** Basic connectives (Definition 1.8) *)

  | FTrue  => True

  | FFalse => False

  | FAtom a =>
      ∃ m0 : WfWorldT,
        logic_qualifier_denote a ρ m0 ∧ m0 ⊑ m

  | FAnd p q =>
      res_models_with_store_fuel gas' ρ m p ∧
      res_models_with_store_fuel gas' ρ m q

  | FOr p q =>
      res_models_with_store_fuel gas' ρ m p ∨
      res_models_with_store_fuel gas' ρ m q

  | FImpl p q =>
      ∀ m' : WfWorldT,
        m ⊑ m' →
        res_models_with_store_fuel gas' ρ m' p →
        res_models_with_store_fuel gas' ρ m' q

  | FStar p q =>
      ∃ (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
        res_product m1 m2 Hc ⊑ m ∧
        res_models_with_store_fuel gas' ρ m1 p ∧
        res_models_with_store_fuel gas' ρ m2 q

  | FWand p q =>
      ∀ m' : WfWorldT,
        ∀ Hc : world_compat m' m,
        res_models_with_store_fuel gas' ρ m' p →
        res_models_with_store_fuel gas' ρ (res_product m' m Hc) q

  | FPlus p q =>
      ∃ (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
        res_sum m1 m2 Hdef ⊑ m ∧
        res_models_with_store_fuel gas' ρ m1 p ∧
        res_models_with_store_fuel gas' ρ m2 q

  | FForall x p =>
      ∃ L : aset,
        world_dom m ⊆ L ∧
        ∀ y : atom,
          y ∉ L →
          ∀ m' : WfWorldT,
            world_dom m' = world_dom m ∪ {[y]} →
            res_restrict m' (world_dom m) = m →
            res_models_with_store_fuel gas' ρ m' (formula_rename_atom x y p)

  | FExists x p =>
      ∃ L : aset,
        world_dom m ⊆ L ∧
        ∀ y : atom,
          y ∉ L →
          ∃ m' : WfWorldT,
            world_dom m' = world_dom m ∪ {[y]} ∧
            res_restrict m' (world_dom m) = m ∧
            res_models_with_store_fuel gas' ρ m' (formula_rename_atom x y p)

  (** Approximation modalities (Definition 1.9) *)

  | FOver p =>
      ∃ m' : WfWorldT, res_subset m m' ∧
        res_models_with_store_fuel gas' ρ m' p

  | FUnder p =>
      ∃ m' : WfWorldT, res_subset m' m ∧
        res_models_with_store_fuel gas' ρ m' p

  | FFib x p =>
      dom ρ ## {[x]} ∧
      ∀ σ (Hproj : res_restrict m {[x]} σ),
        res_models_with_store_fuel gas' (ρ ∪ σ)
          (res_fiber_from_projection m {[x]} σ Hproj) p

  end
  end.

Lemma res_models_with_store_fuel_scoped
    (gas : nat) (ρ : StoreT) (m : WfWorldT) (φ : Formula) :
  res_models_with_store_fuel gas ρ m φ →
  formula_scoped_in_world ρ m φ.
Proof.
  destruct gas as [|gas']; simpl; [tauto | intros [Hscope _]; exact Hscope].
Qed.

Lemma res_models_with_store_fuel_irrel
    (gas1 gas2 : nat) (ρ : StoreT) (m : WfWorldT) (φ : Formula) :
  formula_measure φ <= gas1 →
  formula_measure φ <= gas2 →
  res_models_with_store_fuel gas1 ρ m φ →
  res_models_with_store_fuel gas2 ρ m φ.
Proof.
  assert (Hstrong :
    ∀ n (ψ : Formula) gas1 gas2 ρ m,
      formula_measure ψ <= n →
      formula_measure ψ <= gas1 →
      formula_measure ψ <= gas2 →
      res_models_with_store_fuel gas1 ρ m ψ →
      res_models_with_store_fuel gas2 ρ m ψ).
  {
    induction n as [|n IHn].
    { intros ψ gasA gasB ρ0 m0 Hn. pose proof (formula_measure_pos ψ). lia. }
    intros ψ gasA gasB ρ0 m0 Hn HgasA HgasB Hmodel.
    destruct gasA as [|gasA']; [pose proof (formula_measure_pos ψ); lia |].
    destruct gasB as [|gasB']; [pose proof (formula_measure_pos ψ); lia |].
    simpl in *.
    destruct Hmodel as [Hscope Hmodel]. split; [exact Hscope |].
    destruct ψ as [| |a|p q|p q|p q|p q|p q|p q|x p|x p|p|p|x p];
      simpl in *.
    - exact Hmodel.
    - exact Hmodel.
    - exact Hmodel.
    - destruct Hmodel as [Hp Hq]. split.
      + exact (IHn p gasA' gasB' ρ0 m0 ltac:(lia) ltac:(lia) ltac:(lia) Hp).
      + exact (IHn q gasA' gasB' ρ0 m0 ltac:(lia) ltac:(lia) ltac:(lia) Hq).
    - destruct Hmodel as [Hp | Hq].
      + left. exact (IHn p gasA' gasB' ρ0 m0 ltac:(lia) ltac:(lia) ltac:(lia) Hp).
      + right. exact (IHn q gasA' gasB' ρ0 m0 ltac:(lia) ltac:(lia) ltac:(lia) Hq).
    - intros m' Hle Hp.
      pose proof (IHn p gasB' gasA' ρ0 m' ltac:(lia) ltac:(lia) ltac:(lia) Hp)
        as Hp_src.
      exact (IHn q gasA' gasB' ρ0 m' ltac:(lia) ltac:(lia) ltac:(lia)
        (Hmodel m' Hle Hp_src)).
    - destruct Hmodel as [m1 [m2 [Hc [Hprod [Hp Hq]]]]].
      exists m1, m2, Hc. split; [exact Hprod |]. split.
      + exact (IHn p gasA' gasB' ρ0 m1 ltac:(lia) ltac:(lia) ltac:(lia) Hp).
      + exact (IHn q gasA' gasB' ρ0 m2 ltac:(lia) ltac:(lia) ltac:(lia) Hq).
    - intros m' Hc Hp.
      pose proof (IHn p gasB' gasA' ρ0 m' ltac:(lia) ltac:(lia) ltac:(lia) Hp)
        as Hp_src.
      exact (IHn q gasA' gasB' ρ0 (res_product m' m0 Hc)
        ltac:(lia) ltac:(lia) ltac:(lia) (Hmodel m' Hc Hp_src)).
    - destruct Hmodel as [m1 [m2 [Hdef [Hsum [Hp Hq]]]]].
      exists m1, m2, Hdef. split; [exact Hsum |]. split.
      + exact (IHn p gasA' gasB' ρ0 m1 ltac:(lia) ltac:(lia) ltac:(lia) Hp).
      + exact (IHn q gasA' gasB' ρ0 m2 ltac:(lia) ltac:(lia) ltac:(lia) Hq).
    - destruct Hmodel as [L [HL Hforall]].
      exists L. split; [exact HL |].
      intros y Hy m' Hdom Hrestr.
      exact (IHn (formula_rename_atom x y p) gasA' gasB' ρ0 m'
        ltac:(rewrite formula_rename_preserves_measure; lia)
        ltac:(rewrite formula_rename_preserves_measure; lia)
        ltac:(rewrite formula_rename_preserves_measure; lia)
        (Hforall y Hy m' Hdom Hrestr)).
    - destruct Hmodel as [L [HL Hexists]].
      exists L. split; [exact HL |].
      intros y Hy.
      destruct (Hexists y Hy) as [m' [Hdom [Hrestr Hp]]].
      exists m'. split; [exact Hdom |]. split; [exact Hrestr |].
      exact (IHn (formula_rename_atom x y p) gasA' gasB' ρ0 m'
        ltac:(rewrite formula_rename_preserves_measure; lia)
        ltac:(rewrite formula_rename_preserves_measure; lia)
        ltac:(rewrite formula_rename_preserves_measure; lia)
        Hp).
    - destruct Hmodel as [m' [Hsub Hp]].
      exists m'. split; [exact Hsub |].
      exact (IHn p gasA' gasB' ρ0 m' ltac:(lia) ltac:(lia) ltac:(lia) Hp).
    - destruct Hmodel as [m' [Hsub Hp]].
      exists m'. split; [exact Hsub |].
      exact (IHn p gasA' gasB' ρ0 m' ltac:(lia) ltac:(lia) ltac:(lia) Hp).
    - destruct Hmodel as [Hdisj Hfib]. split; [exact Hdisj |].
      intros σ Hproj.
      exact (IHn p gasA' gasB' (ρ0 ∪ σ)
        (res_fiber_from_projection m0 {[x]} σ Hproj)
        ltac:(lia) ltac:(lia) ltac:(lia) (Hfib σ Hproj)).
  }
  eapply Hstrong with (n := formula_measure φ); eauto.
Qed.

Lemma formula_scoped_res_le
    (ρ : StoreT) (m m' : WfWorldT) (φ : Formula) :
  formula_scoped_in_world ρ m φ →
  m ⊑ m' →
  formula_scoped_in_world ρ m' φ.
Proof.
  unfold formula_scoped_in_world. intros Hscope Hle.
  pose proof (raw_le_dom m m' Hle) as Hdom.
  set_solver.
Qed.

Lemma res_models_with_store_fuel_kripke
    (gas : nat) (ρ : StoreT) (m n : WfWorldT) (φ : Formula) :
  m ⊑ n →
  res_models_with_store_fuel gas ρ m φ →
  res_models_with_store_fuel gas ρ n φ.
Proof.
  revert ρ m n φ.
  induction gas as [|gas IH]; intros ρ m n φ Hle Hmodel; simpl in *.
  { exact Hmodel. }
  destruct Hmodel as [Hscope Hmodel].
  split.
  { eapply formula_scoped_res_le; eauto. }
  destruct φ; simpl in *.
  - exact I.
  - exact Hmodel.
  - destruct Hmodel as [m0 [Ha Hm0m]].
    exists m0. split; [exact Ha |].
    etrans; eauto.
  - destruct Hmodel as [Hp Hq]. split; eauto.
  - destruct Hmodel as [Hp | Hq]; [left | right]; eauto.
  - intros m' Hnm' Hp.
    apply Hmodel; [etrans; eauto | exact Hp].
  - destruct Hmodel as [m1 [m2 [Hc [Hprod [Hp Hq]]]]].
    exists m1, m2, Hc. split; [etrans; eauto |].
    split; eauto.
  - intros m' Hc' Hp.
    pose proof (world_compat_le_r m' m n Hle Hc') as Hc_m.
    pose proof (Hmodel m' Hc_m Hp) as Hq.
    eapply IH; [| exact Hq].
    apply res_product_le_mono; [reflexivity | exact Hle].
  - destruct Hmodel as [m1 [m2 [Hdef [Hsum [Hp Hq]]]]].
    exists m1, m2, Hdef. split; [etrans; eauto |].
    split; eauto.
  - destruct Hmodel as [L [HL Hforall]].
    exists (L ∪ world_dom (n : World)). split.
    { set_solver. }
    intros y Hy n' Hdom_n' Hrestr_n'.
    assert (HyL : y ∉ L) by set_solver.
    set (m' := res_restrict n' (world_dom (m : World) ∪ {[y]})).
    assert (Hdom_m' : world_dom (m' : World) = world_dom (m : World) ∪ {[y]}).
    {
      unfold m'. simpl.
      pose proof (raw_le_dom m n Hle) as Hdom_m_n.
      set_solver.
    }
    assert (Hrestr_nm : res_restrict n' (world_dom (m : World)) = m).
    {
      transitivity (res_restrict (res_restrict n' (world_dom (n : World)))
        (world_dom (m : World))).
      - rewrite res_restrict_restrict_eq.
        pose proof (raw_le_dom m n Hle) as Hdom_m_n.
        replace (world_dom (n : World) ∩ world_dom (m : World))
          with (world_dom (m : World)) by set_solver.
        reflexivity.
      - rewrite Hrestr_n'. apply res_restrict_eq_of_le. exact Hle.
    }
    assert (Hrestr_m' : res_restrict m' (world_dom (m : World)) = m).
    {
      unfold m'. rewrite res_restrict_restrict_eq.
      pose proof (raw_le_dom m n Hle) as Hdom_m_n.
      replace ((world_dom (m : World) ∪ {[y]}) ∩ world_dom (m : World))
        with (world_dom (m : World)) by set_solver.
      exact Hrestr_nm.
    }
    pose proof (Hforall y HyL m' Hdom_m' Hrestr_m') as Hp.
    eapply IH; [| exact Hp].
    unfold m'. apply res_restrict_le.
  - destruct Hmodel as [L [HL Hexists]].
    exists (L ∪ world_dom (n : World)). split.
    { set_solver. }
    intros y Hy.
    assert (HyL : y ∉ L) by set_solver.
    assert (Hyn : y ∉ world_dom (n : World)) by set_solver.
    destruct (Hexists y HyL) as [my [Hdom_my [Hrestr_my Hp]]].
    destruct (res_one_point_extension_pushout m n my y Hle Hyn Hdom_my Hrestr_my)
      as [ny [Hdom_ny [Hrestr_ny Hmy_ny]]].
    exists ny. split; [exact Hdom_ny |].
    split; [exact Hrestr_ny |].
    eauto.
  - destruct Hmodel as [mo [Hsub Hpo]].
    destruct (res_subset_lift_over m n mo Hle Hsub) as [no [Hsub_no Hmo_no]].
    exists no. split; [exact Hsub_no |].
    eauto.
  - destruct Hmodel as [mu [Hsub Hpu]].
    destruct (res_subset_lift_under m n mu Hle Hsub) as [nu [Hsub_nu Hmu_nu]].
    exists nu. split; [exact Hsub_nu |].
    eauto.
  - destruct Hmodel as [Hdisj Hfib]. split; [exact Hdisj |].
    intros σ Hproj_n.
    assert (HX : {[x]} ⊆ world_dom (m : World)).
    { unfold formula_scoped_in_world in Hscope. simpl in Hscope. set_solver. }
    assert (Hproj_m : res_restrict m {[x]} σ).
    {
      rewrite (res_restrict_le_eq m n {[x]} Hle HX).
      exact Hproj_n.
    }
    pose proof (Hfib σ Hproj_m) as Hp.
    eapply IH; [| exact Hp].
    apply res_fiber_from_projection_le; [exact Hle | exact HX].
Qed.

Definition res_models_with_store
    (ρ : StoreT)
    (m : WfWorldT)
    (φ : Formula) : Prop :=
  res_models_with_store_fuel (formula_measure φ) ρ m φ.

(** [res_models m φ] is the empty-store instance of the substitution-aware
    satisfaction relation. *)
Definition res_models (m : WfWorldT) (φ : Formula) : Prop :=
  res_models_with_store ∅ m φ.

(** Entailment: φ ⊨ ψ holds when every world modeling φ also models ψ. *)
Definition entails (φ ψ : Formula) : Prop :=
  ∀ m, res_models m φ → res_models m ψ.

Lemma entails_rename_atom_fresh x y (φ ψ : Formula) :
  y ∉ formula_fv φ ∪ formula_fv ψ →
  entails φ ψ →
  entails (formula_rename_atom x y φ) (formula_rename_atom x y ψ).
Proof.
Admitted.

Lemma formula_scoped_forall_from_renamed
    (ρ : StoreT) (m : WfWorldT) (x : atom) (φ : Formula) (L : aset) :
  world_dom m ⊆ L →
  (∀ y : atom,
    y ∉ L →
    ∀ m' : WfWorldT,
      world_dom m' = world_dom m ∪ {[y]} →
      res_restrict m' (world_dom m) = m →
      formula_scoped_in_world ρ m' (formula_rename_atom x y φ)) →
  formula_scoped_in_world ρ m (FForall x φ).
Proof.
  unfold formula_scoped_in_world.
  intros HL Hrenamed z Hz.
  apply elem_of_union in Hz as [Hzρ | Hzφ].
  - set (y := fresh_for (L ∪ {[z]})).
    assert (HyL : y ∉ L) by (subst y; pose proof (fresh_for_not_in (L ∪ {[z]})); set_solver).
    assert (Hzy : z ≠ y) by (subst y; pose proof (fresh_for_not_in (L ∪ {[z]})); set_solver).
    assert (Hym : y ∉ world_dom (m : World)) by set_solver.
    destruct (res_one_point_extension_exists m y Hym) as [m' [Hdom Hrestr]].
    pose proof (Hrenamed y HyL m' Hdom Hrestr) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    assert (Hzm' : z ∈ world_dom (m' : World)) by set_solver.
    rewrite Hdom in Hzm'. set_solver.
  - apply elem_of_difference in Hzφ as [Hzφ Hzx].
    set (y := fresh_for (L ∪ {[z]})).
    assert (HyL : y ∉ L) by (subst y; pose proof (fresh_for_not_in (L ∪ {[z]})); set_solver).
    assert (Hzy : z ≠ y) by (subst y; pose proof (fresh_for_not_in (L ∪ {[z]})); set_solver).
    assert (Hym : y ∉ world_dom (m : World)) by set_solver.
    destruct (res_one_point_extension_exists m y Hym) as [m' [Hdom Hrestr]].
    pose proof (Hrenamed y HyL m' Hdom Hrestr) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    assert (Hzrenamed : z ∈ formula_fv (formula_rename_atom x y φ)).
    { apply formula_fv_rename_unchanged; set_solver. }
    assert (Hzm' : z ∈ world_dom (m' : World)) by set_solver.
    rewrite Hdom in Hzm'. set_solver.
Qed.

Lemma formula_scoped_exists_from_renamed
    (ρ : StoreT) (m : WfWorldT) (x : atom) (φ : Formula) (L : aset) :
  world_dom m ⊆ L →
  (∀ y : atom,
    y ∉ L →
    ∃ m' : WfWorldT,
      world_dom m' = world_dom m ∪ {[y]} ∧
      res_restrict m' (world_dom m) = m ∧
      formula_scoped_in_world ρ m' (formula_rename_atom x y φ)) →
  formula_scoped_in_world ρ m (FExists x φ).
Proof.
  unfold formula_scoped_in_world.
  intros _ Hrenamed z Hz.
  apply elem_of_union in Hz as [Hzρ | Hzφ].
  - set (y := fresh_for (L ∪ {[z]})).
    assert (Hy : y ∉ L) by (subst y; pose proof (fresh_for_not_in (L ∪ {[z]})); set_solver).
    assert (Hzy : z ≠ y) by (subst y; pose proof (fresh_for_not_in (L ∪ {[z]})); set_solver).
    destruct (Hrenamed y Hy) as [m' [Hdom [Hrestr Hscope]]].
    unfold formula_scoped_in_world in Hscope.
    assert (Hzm' : z ∈ world_dom (m' : World)) by set_solver.
    rewrite Hdom in Hzm'. set_solver.
  - apply elem_of_difference in Hzφ as [Hzφ Hzx].
    set (y := fresh_for (L ∪ {[z]})).
    assert (Hy : y ∉ L) by (subst y; pose proof (fresh_for_not_in (L ∪ {[z]})); set_solver).
    assert (Hzy : z ≠ y) by (subst y; pose proof (fresh_for_not_in (L ∪ {[z]})); set_solver).
    destruct (Hrenamed y Hy) as [m' [Hdom [Hrestr Hscope]]].
    unfold formula_scoped_in_world in Hscope.
    assert (Hzrenamed : z ∈ formula_fv (formula_rename_atom x y φ)).
    { apply formula_fv_rename_unchanged; set_solver. }
    assert (Hzm' : z ∈ world_dom (m' : World)) by set_solver.
    rewrite Hdom in Hzm'. set_solver.
Qed.

(** The fuel-level spec records the intended meaning of [fresh_forall]:
    [fresh_for D] is only the body representative, while models checks all
    names outside a cofinite set by renaming that representative. *)
Lemma res_models_fresh_forall_fuel
    (gas : nat) (ρ : StoreT) (m : WfWorldT) (D : aset)
    (body : atom → Formula) :
  res_models_with_store_fuel (S gas) ρ m (fresh_forall D body) ↔
  formula_scoped_in_world ρ m (fresh_forall D body) ∧
  (∃ L : aset,
      world_dom m ⊆ L ∧
      ∀ y : atom,
        y ∉ L →
        ∀ m' : WfWorldT,
          world_dom m' = world_dom m ∪ {[y]} →
          res_restrict m' (world_dom m) = m →
          res_models_with_store_fuel gas ρ m'
            (formula_rename_atom (fresh_for D) y (body (fresh_for D)))).
Proof. reflexivity. Qed.

Lemma res_models_fresh_forall_intro
    (gas : nat) (ρ : StoreT) (m : WfWorldT) (D : aset)
    (body : atom → Formula) :
  formula_scoped_in_world ρ m (fresh_forall D body) →
  (∃ L : aset,
      world_dom m ⊆ L ∧
      ∀ y : atom,
        y ∉ L →
        ∀ m' : WfWorldT,
          world_dom m' = world_dom m ∪ {[y]} →
          res_restrict m' (world_dom m) = m →
          res_models_with_store_fuel gas ρ m'
            (formula_rename_atom (fresh_for D) y (body (fresh_for D)))) →
  res_models_with_store_fuel (S gas) ρ m (fresh_forall D body).
Proof. intros Hscope Hfresh. exact (conj Hscope Hfresh). Qed.

End Formula.
