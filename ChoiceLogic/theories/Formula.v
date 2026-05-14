From ChoiceLogic Require Export FormulaSyntax.

(** * Choice Logic  (Definitions 1.8 and 1.9)

    Formula syntax and naming operations live in [FormulaSyntax]; this file
    contains satisfaction and semantic proof principles. *)

Section Formula.

Context {V : Type} `{ValueSig V}.

Local Notation StoreT := (gmap atom V) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := V)) (only parsing).
Local Notation Formula := (Formula (V := V)) (only parsing).

(** A formula can only be interpreted at worlds that already track every free
    coordinate it may inspect.  Explicit quantifiers remove their representative
    binder from this set; the bound coordinate is introduced by their semantic
    one-coordinate extension. *)
Definition formula_scoped_in_world
    (ρ : StoreT)
    (m : WfWorldT)
    (φ : Formula) : Prop :=
  dom ρ ∪ formula_fv φ ⊆ world_dom m.

Lemma formula_scoped_swap x y ρ m φ :
  formula_scoped_in_world ρ m (formula_rename_atom x y φ) ↔
  formula_scoped_in_world (store_swap x y ρ) (res_swap x y m) φ.
Proof.
  unfold formula_scoped_in_world.
  rewrite formula_fv_rename_atom, store_swap_dom. simpl.
  split; intros Hscope z Hz.
  - apply elem_of_aset_swap.
    apply Hscope.
    rewrite elem_of_union in Hz |- *.
    destruct Hz as [Hz | Hz].
    + left. rewrite elem_of_aset_swap in Hz. exact Hz.
    + right. rewrite elem_of_aset_swap, atom_swap_involutive. exact Hz.
  - rewrite elem_of_union in Hz.
    destruct Hz as [Hz | Hz].
    + assert (Hzρ : atom_swap x y z ∈ aset_swap x y (dom ρ)).
      { rewrite elem_of_aset_swap, atom_swap_involutive. exact Hz. }
      assert (Hzscope : atom_swap x y z ∈ aset_swap x y (dom ρ) ∪ formula_fv φ)
        by (apply elem_of_union; left; exact Hzρ).
      pose proof (Hscope _ Hzscope) as Hm.
      rewrite elem_of_aset_swap in Hm. rewrite atom_swap_involutive in Hm. exact Hm.
    + assert (Hzφ : atom_swap x y z ∈ formula_fv φ).
      { rewrite elem_of_aset_swap in Hz. exact Hz. }
      assert (Hzscope : atom_swap x y z ∈ aset_swap x y (dom ρ) ∪ formula_fv φ)
        by (apply elem_of_union; right; exact Hzφ).
      pose proof (Hscope _ Hzscope) as Hm.
      rewrite elem_of_aset_swap in Hm. rewrite atom_swap_involutive in Hm. exact Hm.
Qed.

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
        formula_scoped_in_world ρ m0 (FAtom a) ∧
        logic_qualifier_denote a ρ m0 ∧
        m0 ⊑ m

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

  | FForall p =>
      ∃ L : aset,
        world_dom m ⊆ L ∧
        ∀ y : atom,
          y ∉ L →
          ∀ m' : WfWorldT,
            world_dom m' = world_dom m ∪ {[y]} →
            res_restrict m' (world_dom m) = m →
            res_models_with_store_fuel gas' ρ m' (formula_open 0 y p)

  | FExists p =>
      ∃ L : aset,
        world_dom m ⊆ L ∧
        ∀ y : atom,
          y ∉ L →
          ∃ m' : WfWorldT,
            world_dom m' = world_dom m ∪ {[y]} ∧
            res_restrict m' (world_dom m) = m ∧
            res_models_with_store_fuel gas' ρ m' (formula_open 0 y p)

  (** Approximation modalities (Definition 1.9) *)

  | FOver p =>
      ∃ m' : WfWorldT, res_subset m m' ∧
        res_models_with_store_fuel gas' ρ m' p

  | FUnder p =>
      ∃ m' : WfWorldT, res_subset m' m ∧
        res_models_with_store_fuel gas' ρ m' p

  | FFibVars D p =>
      let X := lvars_fv D in
      dom ρ ## X ∧
      ∀ σ (Hproj : res_restrict m X σ),
        res_models_with_store_fuel gas' (ρ ∪ σ)
          (res_fiber_from_projection m X σ Hproj) p

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
    destruct ψ as [| |a|p q|p q|p q|p q|p q|p q|p|p|p|p|X p];
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
      exact (IHn (formula_open 0 y p) gasA' gasB' ρ0 m'
        ltac:(rewrite formula_open_preserves_measure; lia)
        ltac:(rewrite formula_open_preserves_measure; lia)
        ltac:(rewrite formula_open_preserves_measure; lia)
        (Hforall y Hy m' Hdom Hrestr)).
    - destruct Hmodel as [L [HL Hexists]].
      exists L. split; [exact HL |].
      intros y Hy.
      destruct (Hexists y Hy) as [m' [Hdom [Hrestr Hp]]].
      exists m'. split; [exact Hdom |]. split; [exact Hrestr |].
      exact (IHn (formula_open 0 y p) gasA' gasB' ρ0 m'
        ltac:(rewrite formula_open_preserves_measure; lia)
        ltac:(rewrite formula_open_preserves_measure; lia)
        ltac:(rewrite formula_open_preserves_measure; lia)
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
        (res_fiber_from_projection m0 (lvars_fv X) σ Hproj)
        ltac:(lia) ltac:(lia) ltac:(lia) (Hfib σ Hproj)).
  }
  eapply Hstrong with (n := formula_measure φ); eauto.
Qed.

Local Ltac formula_models_fuel_finish :=
  rewrite ?formula_rename_preserves_measure; simpl; lia.

Local Tactic Notation "formula_models_fuel_irrel" constr(H) :=
  eapply res_models_with_store_fuel_irrel; [| | exact H];
  formula_models_fuel_finish.

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
  destruct φ as [| |a|p q|p q|p q|p q|p q|p q|p|p|p|p|D p];
    simpl in *.
  - exact I.
  - exact Hmodel.
  - destruct Hmodel as [m0 [Hscope0 [Ha Hm0m]]].
    exists m0. split; [exact Hscope0 |]. split; [exact Ha |].
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
    set (XF := lvars_fv D).
    assert (HX : XF ⊆ world_dom (m : World)).
    { unfold formula_scoped_in_world in Hscope. simpl in Hscope. set_solver. }
    assert (Hproj_m : res_restrict m XF σ).
    {
      rewrite (res_restrict_le_eq m n XF Hle HX).
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

Lemma res_models_with_store_kripke
    (ρ : StoreT) (m n : WfWorldT) (φ : Formula) :
  m ⊑ n →
  res_models_with_store ρ m φ →
  res_models_with_store ρ n φ.
Proof.
  unfold res_models_with_store.
  apply res_models_with_store_fuel_kripke.
Qed.

Lemma res_models_kripke
    (m n : WfWorldT) (φ : Formula) :
  m ⊑ n →
  res_models m φ →
  res_models n φ.
Proof.
  unfold res_models.
  apply res_models_with_store_kripke.
Qed.

Lemma res_models_with_store_fuel_restrict_fv
    (gas : nat) (ρ : StoreT) (m : WfWorldT) (φ : Formula) :
  res_models_with_store_fuel gas ρ m φ →
  res_models_with_store_fuel gas ρ
    (res_restrict m (dom ρ ∪ formula_fv φ)) φ.
Proof.
  revert ρ m φ.
  induction gas as [|gas IH]; intros ρ m φ Hmodel; simpl in *.
  { exact Hmodel. }
  destruct Hmodel as [Hscope Hmodel].
  set (S := dom ρ ∪ formula_fv φ).
  assert (Hscope_restrict : formula_scoped_in_world ρ (res_restrict m S) φ).
  {
    unfold formula_scoped_in_world in *. subst S. simpl. set_solver.
  }
  split; [exact Hscope_restrict |].
  destruct φ as [| |a|p q|p q|p q|p q|p q|p q|p|p|p|p|X p];
    simpl in *; subst S.
  - exact I.
  - exact Hmodel.
  - destruct Hmodel as [m0 [Hscope0 [Ha Hle]]].
    exists (res_restrict m0 (dom ρ ∪ stale a)). split.
    + unfold formula_scoped_in_world in *. simpl in *. set_solver.
    + split.
      * rewrite logic_qualifier_denote_restrict.
        -- exact Ha.
        -- set_solver.
      * eapply res_restrict_le_mono. exact Hle.
  - destruct Hmodel as [Hp Hq]. split.
    + pose proof (IH ρ m p Hp) as Hp_small.
      eapply res_models_with_store_fuel_kripke; [| exact Hp_small].
      apply res_restrict_mono. set_solver.
    + pose proof (IH ρ m q Hq) as Hq_small.
      eapply res_models_with_store_fuel_kripke; [| exact Hq_small].
      apply res_restrict_mono. set_solver.
  - destruct Hmodel as [Hp | Hq].
    + left.
      pose proof (IH ρ m p Hp) as Hp_small.
      eapply res_models_with_store_fuel_kripke; [| exact Hp_small].
      apply res_restrict_mono. set_solver.
    + right.
      pose proof (IH ρ m q Hq) as Hq_small.
      eapply res_models_with_store_fuel_kripke; [| exact Hq_small].
      apply res_restrict_mono. set_solver.
  - intros n Hle_rn Hp_n.
    set (Sp := dom ρ ∪ formula_fv p).
    set (Sq := dom ρ ∪ formula_fv q).
    assert (HSpS : Sp ⊆ dom ρ ∪ (formula_fv p ∪ formula_fv q)) by (subst Sp; set_solver).
    assert (HSqS : Sq ⊆ dom ρ ∪ (formula_fv p ∪ formula_fv q)) by (subst Sq; set_solver).
    assert (HSpm : Sp ⊆ world_dom (m : World)).
    { unfold formula_scoped_in_world in Hscope. subst Sp. set_solver. }
    assert (HSqm : Sq ⊆ world_dom (m : World)).
    { unfold formula_scoped_in_world in Hscope. subst Sq. set_solver. }
    pose proof (IH ρ n p Hp_n) as Hp_small.
    assert (Heq_p : res_restrict n Sp = res_restrict m Sp).
    {
      subst Sp.
      eapply res_restrict_le_eq_from_base; [exact Hle_rn | set_solver | set_solver].
    }
    change (dom ρ ∪ formula_fv p) with Sp in Hp_small.
    rewrite Heq_p in Hp_small.
    assert (Hp_m : res_models_with_store_fuel gas ρ m p).
    { eapply res_models_with_store_fuel_kripke; [apply res_restrict_le | exact Hp_small]. }
    pose proof (Hmodel m ltac:(reflexivity) Hp_m) as Hq_m.
    pose proof (IH ρ m q Hq_m) as Hq_small.
    change (dom ρ ∪ formula_fv q) with Sq in Hq_small.
    assert (Hsmall_n : res_restrict m Sq ⊑ n).
    {
      rewrite <- (res_restrict_le_eq_from_base m n
        (dom ρ ∪ (formula_fv p ∪ formula_fv q)) Sq Hle_rn HSqS HSqm).
      apply res_restrict_le.
    }
    eapply res_models_with_store_fuel_kripke; [exact Hsmall_n | exact Hq_small].
  - destruct Hmodel as [m1 [m2 [Hc [Hprod [Hp Hq]]]]].
    set (Sp := dom ρ ∪ formula_fv p).
    set (Sq := dom ρ ∪ formula_fv q).
    set (r1 := res_restrict m1 Sp).
    set (r2 := res_restrict m2 Sq).
    assert (Hc' : world_compat r1 r2).
    {
      subst r1 r2.
      eapply world_compat_le_l.
      - apply res_restrict_le.
      - eapply world_compat_le_r.
        + apply res_restrict_le.
        + exact Hc.
    }
    exists r1, r2, Hc'. split.
    + eapply res_le_restrict.
      * etrans.
        -- eapply (res_product_le_mono r1 r2 m1 m2 Hc' Hc);
             apply res_restrict_le.
        -- exact Hprod.
      * subst r1 r2 Sp Sq. simpl. set_solver.
    + split.
      * subst r1 Sp. apply IH. exact Hp.
      * subst r2 Sq. apply IH. exact Hq.
  - intros n Hc Hp.
    set (S := dom ρ ∪ (formula_fv p ∪ formula_fv q)).
    set (Sp := dom ρ ∪ formula_fv p).
    set (Sq := dom ρ ∪ formula_fv q).
    assert (HSpS : Sp ⊆ S) by (subst Sp S; set_solver).
    assert (HSqS : Sq ⊆ S) by (subst Sq S; set_solver).
    assert (Hc_small : world_compat (res_restrict n Sp) m).
    {
      eapply world_compat_restrict_l_full_r.
      - exact HSpS.
      - exact Hc.
    }
    pose proof (IH ρ n p Hp) as Hp_small.
    change (dom ρ ∪ formula_fv p) with Sp in Hp_small.
    pose proof (Hmodel (res_restrict n Sp) Hc_small Hp_small) as Hq_big.
    pose proof (IH ρ (res_product (res_restrict n Sp) m Hc_small) q Hq_big)
      as Hq_small.
    change (dom ρ ∪ formula_fv q) with Sq in Hq_small.
    eapply res_models_with_store_fuel_kripke; [| exact Hq_small].
    assert (HSqm : Sq ⊆ world_dom (m : World)).
    { unfold formula_scoped_in_world in Hscope. subst Sq. set_solver. }
    exact (res_product_restrict_wand_le n m S Sp Sq Hc_small Hc HSqS HSqm).
  - destruct Hmodel as [m1 [m2 [Hdef [Hsum [Hp Hq]]]]].
    set (Sp := dom ρ ∪ formula_fv p).
    set (Sq := dom ρ ∪ formula_fv q).
    set (S := dom ρ ∪ (formula_fv p ∪ formula_fv q)).
    set (r1 := res_restrict m1 S).
    set (r2 := res_restrict m2 S).
    assert (Hdef' : raw_sum_defined r1 r2).
    {
      subst r1 r2 S. unfold raw_sum_defined. simpl.
      rewrite Hdef. reflexivity.
    }
    exists r1, r2, Hdef'. split.
    + eapply res_le_restrict.
      * etrans.
        -- eapply (res_sum_le_mono r1 r2 m1 m2 Hdef' Hdef);
             apply res_restrict_le.
        -- exact Hsum.
      * subst r1 S. simpl. set_solver.
    + split.
      * pose proof (IH ρ m1 p Hp) as Hp_small.
        subst r1 Sp S.
        eapply res_models_with_store_fuel_kripke; [| exact Hp_small].
        apply res_restrict_mono. set_solver.
      * pose proof (IH ρ m2 q Hq) as Hq_small.
        subst r2 Sq S.
        eapply res_models_with_store_fuel_kripke; [| exact Hq_small].
        apply res_restrict_mono. set_solver.
  - destruct Hmodel as [L [HL Hforall]].
    set (S := dom ρ ∪ formula_fv p).
    exists (L ∪ world_dom (m : World) ∪ S). split.
    { subst S. simpl. set_solver. }
    intros y Hy n Hdom_n Hrestr_n.
    assert (HyL : y ∉ L) by set_solver.
    assert (Hym : y ∉ world_dom (m : World)) by set_solver.
    assert (HS_m : S ⊆ world_dom (m : World)).
    { unfold formula_scoped_in_world in Hscope. subst S. set_solver. }
    assert (Hle_rm : res_restrict m S ⊑ m) by apply res_restrict_le.
    destruct (res_one_point_extension_pushout
      (res_restrict m S) m n y Hle_rm Hym Hdom_n Hrestr_n)
      as [my [Hdom_my [Hrestr_my Hn_my]]].
    pose proof (Hforall y HyL my Hdom_my Hrestr_my) as Hp_my.
    pose proof (IH ρ my (formula_open 0 y p) Hp_my) as Hp_small.
    set (X := dom ρ ∪ formula_fv (formula_open 0 y p)).
    change (dom ρ ∪ formula_fv (formula_open 0 y p)) with X in Hp_small.
    assert (HX_n : X ⊆ world_dom (n : World)).
    {
      subst X S. rewrite Hdom_n. simpl.
      intros z Hz.
      apply elem_of_union in Hz as [Hzρ | Hzφ].
      - apply elem_of_union. left. unfold formula_scoped_in_world in Hscope.
        set_solver.
      - pose proof (formula_open_fv_subset 0 y p z Hzφ) as Hzopen.
        set_solver.
    }
    rewrite <- (res_restrict_le_eq n my X Hn_my HX_n) in Hp_small.
    eapply res_models_with_store_fuel_kripke; [apply res_restrict_le | exact Hp_small].
  - destruct Hmodel as [L [HL Hexists]].
    set (S := dom ρ ∪ formula_fv p).
    exists (L ∪ world_dom (m : World) ∪ S). split.
    { subst S. simpl. set_solver. }
    intros y Hy.
    assert (HyL : y ∉ L) by set_solver.
    assert (HS_m : S ⊆ world_dom (m : World)).
    { unfold formula_scoped_in_world in Hscope. subst S. set_solver. }
    destruct (Hexists y HyL) as [my [Hdom_my [Hrestr_my Hp_my]]].
    set (n := res_restrict my (S ∪ {[y]})).
    exists n. split.
    + subst n. simpl. rewrite Hdom_my.
      apply set_eq. intros z. set_solver.
    + split.
      * subst n.
        change (res_restrict (res_restrict my (S ∪ {[y]}))
          (world_dom (res_restrict m S : World)) = res_restrict m S).
        simpl.
        replace (world_dom (m : World) ∩ S) with S by set_solver.
        rewrite res_restrict_restrict_eq.
        replace ((S ∪ {[y]}) ∩ S) with S by set_solver.
        rewrite <- Hrestr_my.
        rewrite res_restrict_restrict_eq.
        replace (world_dom (m : World) ∩ S) with S by set_solver.
        reflexivity.
      * pose proof (IH ρ my (formula_open 0 y p) Hp_my) as Hp_small.
        set (X := dom ρ ∪ formula_fv (formula_open 0 y p)).
        change (dom ρ ∪ formula_fv (formula_open 0 y p)) with X in Hp_small.
        assert (HX_n : X ⊆ world_dom (n : World)).
        {
          subst X n S. simpl. rewrite Hdom_my.
          intros z Hz.
          apply elem_of_union in Hz as [Hzρ | Hzφ].
          - unfold formula_scoped_in_world in Hscope. set_solver.
          - pose proof (formula_open_fv_subset 0 y p z Hzφ) as Hzopen.
            set_solver.
        }
        rewrite <- (res_restrict_le_eq n my X ltac:(subst n; apply res_restrict_le) HX_n)
          in Hp_small.
        eapply res_models_with_store_fuel_kripke; [apply res_restrict_le | exact Hp_small].
  - destruct Hmodel as [m' [Hsub Hp]].
    set (S := dom ρ ∪ formula_fv p).
    exists (res_restrict m' S). split.
    + destruct Hsub as [Hdom Hin]. split.
      * subst S. simpl. rewrite Hdom. reflexivity.
      * intros σ Hrσ. simpl in Hrσ.
        destruct Hrσ as [σm [Hσm Hrestrict]].
        exists σm. split; [apply Hin; exact Hσm | exact Hrestrict].
    + subst S. apply IH. exact Hp.
  - destruct Hmodel as [m' [Hsub Hp]].
    set (S := dom ρ ∪ formula_fv p).
    exists (res_restrict m' S). split.
    + destruct Hsub as [Hdom Hin]. split.
      * subst S. simpl. rewrite Hdom. reflexivity.
      * intros σ Hrσ. simpl in Hrσ.
        destruct Hrσ as [σm [Hσm Hrestrict]].
        exists σm. split; [apply Hin; exact Hσm | exact Hrestrict].
    + subst S. apply IH. exact Hp.
  - destruct Hmodel as [Hdisj Hfib]. split; [exact Hdisj |].
    intros σ Hproj_r.
    set (XF := lvars_fv X).
    set (S := dom ρ ∪ (XF ∪ formula_fv p)).
    assert (HXm : XF ⊆ world_dom (m : World)).
    { unfold formula_scoped_in_world in Hscope. set_solver. }
    assert (Hproj_m : res_restrict m XF σ).
    {
      change ((res_restrict m XF : World) σ).
      change ((res_restrict (res_restrict m S) XF : World) σ) in Hproj_r.
      rewrite res_restrict_restrict_eq in Hproj_r.
      replace (S ∩ XF) with XF in Hproj_r by set_solver.
      exact Hproj_r.
    }
    pose proof (Hfib σ Hproj_m) as Hp_fib.
    pose proof (IH (ρ ∪ σ)
      (res_fiber_from_projection m XF σ Hproj_m) p Hp_fib) as Hp_small.
    set (T := dom (ρ ∪ σ) ∪ formula_fv p).
    change (dom (ρ ∪ σ) ∪ formula_fv p) with T in Hp_small.
    assert (Hfiber_le :
      res_fiber_from_projection (res_restrict m S) XF σ Hproj_r ⊑
      res_fiber_from_projection m XF σ Hproj_m).
    {
      eapply res_fiber_from_projection_le.
      - apply res_restrict_le.
      - simpl. set_solver.
    }
    assert (HT_target :
      T ⊆ world_dom (res_fiber_from_projection (res_restrict m S) XF σ Hproj_r : World)).
    {
      subst T S. simpl.
      pose proof (wfworld_store_dom (res_restrict m XF) σ Hproj_m) as Hdomσ.
      simpl in Hdomσ.
      replace (world_dom (m : World) ∩ XF) with XF in Hdomσ by set_solver.
      rewrite dom_union_L. rewrite Hdomσ.
      unfold formula_scoped_in_world in Hscope. set_solver.
    }
    rewrite <- (res_restrict_le_eq
      (res_fiber_from_projection (res_restrict m S) XF σ Hproj_r)
      (res_fiber_from_projection m XF σ Hproj_m)
      T Hfiber_le HT_target) in Hp_small.
    eapply res_models_with_store_fuel_kripke; [apply res_restrict_le | exact Hp_small].
Qed.

Lemma res_models_with_store_restrict_fv
    (ρ : StoreT) (m : WfWorldT) (φ : Formula) :
  res_models_with_store ρ m φ →
  res_models_with_store ρ
    (res_restrict m (dom ρ ∪ formula_fv φ)) φ.
Proof.
  unfold res_models_with_store.
  apply res_models_with_store_fuel_restrict_fv.
Qed.

Lemma res_models_restrict_fv (m : WfWorldT) (φ : Formula) :
  res_models m φ →
  res_models (res_restrict m (formula_fv φ)) φ.
Proof.
  unfold res_models.
  intros Hm.
  pose proof (res_models_with_store_restrict_fv ∅ m φ Hm) as Hrestrict.
  change (dom (∅ : StoreT)) with (∅ : aset) in Hrestrict.
  replace (∅ ∪ formula_fv φ) with (formula_fv φ) in Hrestrict by set_solver.
  exact Hrestrict.
Qed.

Lemma res_models_minimal_on (S : aset) (m : WfWorldT) (φ : Formula) :
  formula_fv φ ⊆ S →
  res_models m φ ↔ res_models (res_restrict m S) φ.
Proof.
  intros Hfv. split.
  - intros Hm.
    eapply res_models_kripke.
    + apply res_restrict_mono. exact Hfv.
    + apply res_models_restrict_fv. exact Hm.
  - intros Hm.
    eapply res_models_kripke.
    + apply res_restrict_le.
    + exact Hm.
Qed.

Lemma res_models_with_store_impl_refl
    (ρ : StoreT) (m : WfWorldT) (φ : Formula) :
  formula_scoped_in_world ρ m φ →
  res_models_with_store ρ m (FImpl φ φ).
Proof.
  unfold res_models_with_store. simpl.
  intros Hscope. split.
  - unfold formula_scoped_in_world in *. simpl. set_solver.
  - intros m' _ Hmodel. exact Hmodel.
Qed.

Lemma res_models_impl_refl (m : WfWorldT) (φ : Formula) :
  formula_scoped_in_world ∅ m φ →
  res_models m (FImpl φ φ).
Proof.
  unfold res_models.
  apply res_models_with_store_impl_refl.
Qed.

Lemma res_models_with_store_and_elim_l
    (ρ : StoreT) (m : WfWorldT) (φ ψ : Formula) :
  res_models_with_store ρ m (FAnd φ ψ) →
  res_models_with_store ρ m φ.
Proof.
  unfold res_models_with_store.
  simpl. intros [_ [Hφ _]].
  formula_models_fuel_irrel Hφ.
Qed.

Lemma res_models_with_store_and_elim_r
    (ρ : StoreT) (m : WfWorldT) (φ ψ : Formula) :
  res_models_with_store ρ m (FAnd φ ψ) →
  res_models_with_store ρ m ψ.
Proof.
  unfold res_models_with_store.
  simpl. intros [_ [_ Hψ]].
  formula_models_fuel_irrel Hψ.
Qed.

Lemma res_models_with_store_and_intro
    (ρ : StoreT) (m : WfWorldT) (φ ψ : Formula) :
  formula_scoped_in_world ρ m (FAnd φ ψ) →
  res_models_with_store ρ m φ →
  res_models_with_store ρ m ψ →
  res_models_with_store ρ m (FAnd φ ψ).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Hφ Hψ. split; [exact Hscope |].
  split.
  - formula_models_fuel_irrel Hφ.
  - formula_models_fuel_irrel Hψ.
Qed.

Lemma res_models_with_store_or_intro_l
    (ρ : StoreT) (m : WfWorldT) (φ ψ : Formula) :
  formula_scoped_in_world ρ m (FOr φ ψ) →
  res_models_with_store ρ m φ →
  res_models_with_store ρ m (FOr φ ψ).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  left. formula_models_fuel_irrel Hφ.
Qed.

Lemma res_models_with_store_or_intro_r
    (ρ : StoreT) (m : WfWorldT) (φ ψ : Formula) :
  formula_scoped_in_world ρ m (FOr φ ψ) →
  res_models_with_store ρ m ψ →
  res_models_with_store ρ m (FOr φ ψ).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Hψ. split; [exact Hscope |].
  right. formula_models_fuel_irrel Hψ.
Qed.

Lemma res_models_with_store_and_map
    (ρ : StoreT) (m : WfWorldT)
    (φ1 φ2 ψ1 ψ2 : Formula) :
  formula_scoped_in_world ρ m (FAnd ψ1 ψ2) →
  (res_models_with_store ρ m φ1 → res_models_with_store ρ m ψ1) →
  (res_models_with_store ρ m φ2 → res_models_with_store ρ m ψ2) →
  res_models_with_store ρ m (FAnd φ1 φ2) →
  res_models_with_store ρ m (FAnd ψ1 ψ2).
Proof.
  intros Hscope H1 H2 Hm.
  eapply res_models_with_store_and_intro; [exact Hscope | |].
  - apply H1. eapply res_models_with_store_and_elim_l. exact Hm.
  - apply H2. eapply res_models_with_store_and_elim_r. exact Hm.
Qed.

Lemma res_models_with_store_or_map
    (ρ : StoreT) (m : WfWorldT)
    (φ1 φ2 ψ1 ψ2 : Formula) :
  formula_scoped_in_world ρ m (FOr ψ1 ψ2) →
  (res_models_with_store ρ m φ1 → res_models_with_store ρ m ψ1) →
  (res_models_with_store ρ m φ2 → res_models_with_store ρ m ψ2) →
  res_models_with_store ρ m (FOr φ1 φ2) →
  res_models_with_store ρ m (FOr ψ1 ψ2).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope H1 H2 [_ [Hφ1 | Hφ2]].
  - split; [exact Hscope |].
    left.
    pose proof (H1 ltac:(formula_models_fuel_irrel Hφ1)) as Hψ1.
    formula_models_fuel_irrel Hψ1.
  - split; [exact Hscope |].
    right.
      pose proof (H2 ltac:(formula_models_fuel_irrel Hφ2)) as Hψ2.
    formula_models_fuel_irrel Hψ2.
Qed.

Lemma res_models_with_store_pure_intro
    (ρ : StoreT) (m : WfWorldT) (P : Prop) :
  formula_scoped_in_world ρ m (FPure P) →
  P →
  res_models_with_store ρ m (FPure P).
Proof.
  unfold res_models_with_store. simpl.
  intros Hscope HP. split; [exact Hscope |].
  exists m. split; [exact Hscope |].
  split; [exact HP | reflexivity].
Qed.

Lemma res_models_with_store_pure_elim
    (ρ : StoreT) (m : WfWorldT) (P : Prop) :
  res_models_with_store ρ m (FPure P) →
  P.
Proof.
  unfold res_models_with_store. simpl.
  intros [_ [m0 [_ [HP _]]]]. exact HP.
Qed.

Lemma res_models_with_store_resource_atom_intro
    (ρ : StoreT) (m : WfWorldT) D (P : WfWorldT → Prop) :
  formula_scoped_in_world ρ m (FResourceAtom D P) →
  P (res_restrict m D) →
  res_models_with_store ρ m (FResourceAtom D P).
Proof.
  unfold res_models_with_store. simpl.
  intros Hscope HP. split; [exact Hscope |].
  exists m. split; [exact Hscope |].
  rewrite lvars_fv_of_atoms.
  split; [exact HP | reflexivity].
Qed.

Lemma res_models_with_store_resource_atom_elim
    (ρ : StoreT) (m : WfWorldT) D (P : WfWorldT → Prop) :
  res_models_with_store ρ m (FResourceAtom D P) →
  ∃ m0,
    formula_scoped_in_world ρ m0 (FResourceAtom D P) ∧
    P (res_restrict m0 D) ∧
    m0 ⊑ m.
Proof.
  unfold res_models_with_store. simpl.
  intros [_ [m0 [Hscope [HP Hle]]]].
  rewrite lvars_fv_of_atoms in HP.
  exists m0. repeat split; eauto.
Qed.

Lemma res_models_with_store_store_resource_atom_intro
    (ρ : StoreT) (m : WfWorldT) D
    (P : gmap nat atom → StoreT → WfWorldT → Prop) :
  formula_scoped_in_world ρ m (FStoreResourceAtom D P) →
  P ∅ (store_restrict ρ D) (res_restrict m D) →
  res_models_with_store ρ m (FStoreResourceAtom D P).
Proof.
  unfold res_models_with_store. simpl.
  intros Hscope HP. split; [exact Hscope |].
  exists m. split; [exact Hscope |].
  rewrite lvars_fv_of_atoms.
  split; [exact HP | reflexivity].
Qed.

Lemma res_models_with_store_store_resource_atom_elim
    (ρ : StoreT) (m : WfWorldT) D
    (P : gmap nat atom → StoreT → WfWorldT → Prop) :
  res_models_with_store ρ m (FStoreResourceAtom D P) →
  ∃ m0,
    formula_scoped_in_world ρ m0 (FStoreResourceAtom D P) ∧
    P ∅ (store_restrict ρ D) (res_restrict m0 D) ∧
    m0 ⊑ m.
Proof.
  unfold res_models_with_store. simpl.
  intros [_ [m0 [Hscope [HP Hle]]]].
  rewrite lvars_fv_of_atoms in HP.
  exists m0. repeat split; eauto.
Qed.

Lemma res_models_with_store_impl_intro
    (ρ : StoreT) (m : WfWorldT) (φ ψ : Formula) :
  formula_scoped_in_world ρ m (FImpl φ ψ) →
  (∀ m', m ⊑ m' →
     res_models_with_store ρ m' φ →
     res_models_with_store ρ m' ψ) →
  res_models_with_store ρ m (FImpl φ ψ).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Himpl. split; [exact Hscope |].
  intros m' Hle Hφ.
  pose proof (res_models_with_store_fuel_irrel
    (formula_measure φ + formula_measure ψ) (formula_measure φ)
    ρ m' φ ltac:(simpl; lia) ltac:(lia) Hφ) as Hφ_exact.
  pose proof (Himpl m' Hle Hφ_exact) as Hψ_exact.
  formula_models_fuel_irrel Hψ_exact.
Qed.

Lemma res_models_with_store_impl_elim
    (ρ : StoreT) (m : WfWorldT) (φ ψ : Formula) :
  res_models_with_store ρ m (FImpl φ ψ) →
  res_models_with_store ρ m φ →
  res_models_with_store ρ m ψ.
Proof.
  unfold res_models_with_store.
  simpl. intros [_ Himpl] Hφ.
  pose proof (res_models_with_store_fuel_irrel
    (formula_measure φ) (formula_measure φ + formula_measure ψ)
    ρ m φ ltac:(lia) ltac:(simpl; lia) Hφ) as Hφ_big.
  pose proof (Himpl m ltac:(reflexivity) Hφ_big) as Hψ_big.
  formula_models_fuel_irrel Hψ_big.
Qed.

Lemma res_models_with_store_impl_antecedent_strengthen
    (ρ : StoreT) (m : WfWorldT) (φ1 φ2 ψ : Formula) :
  formula_scoped_in_world ρ m (FImpl φ2 ψ) →
  (∀ m', m ⊑ m' →
     res_models_with_store ρ m' φ2 →
     res_models_with_store ρ m' φ1) →
  res_models_with_store ρ m (FImpl φ1 ψ) →
  res_models_with_store ρ m (FImpl φ2 ψ).
Proof.
  intros Hscope Hφ Himpl.
  eapply res_models_with_store_impl_intro.
  - exact Hscope.
  - intros m' Hle Hφ2.
    eapply res_models_with_store_impl_elim.
    + eapply res_models_with_store_kripke; [exact Hle | exact Himpl].
    + eapply Hφ; eauto.
Qed.

Lemma res_models_with_store_fuel_swap
    (a b : atom) (gas : nat) (ρ : StoreT) (m : WfWorldT) (φ : Formula) :
  res_models_with_store_fuel gas ρ m (formula_rename_atom a b φ) ↔
  res_models_with_store_fuel gas (store_swap a b ρ) (res_swap a b m) φ.
Proof.
  (* Temporary compatibility for the explicit-name layer.  The LN refactor
     removes formula-level swap/rename instead of repairing this legacy proof. *)
Admitted.

Lemma res_models_swap x y (m : WfWorldT) (φ : Formula) :
  res_models m (formula_rename_atom x y φ) ↔
  res_models (res_swap x y m) φ.
Proof.
  unfold res_models, res_models_with_store.
  rewrite formula_rename_preserves_measure.
  rewrite <- (store_swap_empty x y) at 2.
  apply res_models_with_store_fuel_swap.
Qed.

Lemma res_models_with_store_swap x y ρ (m : WfWorldT) (φ : Formula) :
  res_models_with_store ρ m (formula_rename_atom x y φ) ↔
  res_models_with_store (store_swap x y ρ) (res_swap x y m) φ.
Proof.
  unfold res_models_with_store.
  rewrite formula_rename_preserves_measure.
  apply res_models_with_store_fuel_swap.
Qed.

Lemma entails_rename_atom_fresh x y (φ ψ : Formula) :
  y ∉ formula_fv φ ∪ formula_fv ψ →
  entails φ ψ →
  entails (formula_rename_atom x y φ) (formula_rename_atom x y ψ).
Proof.
  intros _ Hent m Hm.
  unfold entails in Hent.
  apply res_models_swap.
  apply Hent.
  apply res_models_swap.
  exact Hm.
Qed.

Lemma entails_rename_atom_fresh_fuel x y (φ ψ : Formula) (m : WfWorldT) :
  y ∉ formula_fv φ ∪ formula_fv ψ →
  entails φ ψ →
  res_models_with_store_fuel
    (formula_measure (formula_rename_atom x y φ)) ∅ m
    (formula_rename_atom x y φ) →
  res_models_with_store_fuel
    (formula_measure (formula_rename_atom x y ψ)) ∅ m
    (formula_rename_atom x y ψ).
Proof.
  intros Hyfresh Hent Hp.
  exact (entails_rename_atom_fresh x y φ ψ Hyfresh Hent m Hp).
Qed.


Lemma formula_scoped_forall_from_open
    (ρ : StoreT) (m : WfWorldT) (φ : Formula) (L : aset) :
  world_dom m ⊆ L →
  (∀ y : atom,
    y ∉ L →
    ∀ m' : WfWorldT,
      world_dom m' = world_dom m ∪ {[y]} →
      res_restrict m' (world_dom m) = m →
      formula_scoped_in_world ρ m' (formula_open 0 y φ)) →
  formula_scoped_in_world ρ m (FForall φ).
Proof.
Admitted.

Lemma formula_scoped_exists_from_open
    (ρ : StoreT) (m : WfWorldT) (φ : Formula) (L : aset) :
  world_dom m ⊆ L →
  (∀ y : atom,
    y ∉ L →
    ∃ m' : WfWorldT,
      world_dom m' = world_dom m ∪ {[y]} ∧
      res_restrict m' (world_dom m) = m ∧
      formula_scoped_in_world ρ m' (formula_open 0 y φ)) →
  formula_scoped_in_world ρ m (FExists φ).
Proof.
Admitted.

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
            (formula_open 0 y (body (fresh_for D)))).
Proof.
Admitted.

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
            (formula_open 0 y (body (fresh_for D)))) →
  res_models_with_store_fuel (S gas) ρ m (fresh_forall D body).
Proof.
Admitted.

Lemma res_models_fresh_forall_transport_fuel
    (gas : nat) (ρ : StoreT) (m : WfWorldT)
    (D1 D2 : aset) (body1 body2 : atom → Formula) :
  formula_scoped_in_world ρ m (fresh_forall D2 body2) →
  (∀ y m',
    res_models_with_store_fuel gas ρ m'
      (formula_open 0 y (body1 (fresh_for D1))) →
    res_models_with_store_fuel gas ρ m'
      (formula_open 0 y (body2 (fresh_for D2)))) →
  res_models_with_store_fuel (S gas) ρ m (fresh_forall D1 body1) →
  res_models_with_store_fuel (S gas) ρ m (fresh_forall D2 body2).
Proof.
Admitted.

Lemma res_models_with_store_fresh_forall_transport
    (ρ : StoreT) (m : WfWorldT)
    (D1 D2 : aset) (body1 body2 : atom → Formula) :
  formula_scoped_in_world ρ m (fresh_forall D2 body2) →
  (∀ y m',
    res_models_with_store ρ m'
      (formula_open 0 y (body1 (fresh_for D1))) →
    res_models_with_store ρ m'
      (formula_open 0 y (body2 (fresh_for D2)))) →
  res_models_with_store ρ m (fresh_forall D1 body1) →
  res_models_with_store ρ m (fresh_forall D2 body2).
Proof.
Admitted.

End Formula.
