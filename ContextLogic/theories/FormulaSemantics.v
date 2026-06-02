From ContextLogic Require Export FormulaSyntax.
From ContextLogic Require Import FormulaSyntax.
From Stdlib Require Import Lia.

(** * Context Logic semantics

    The semantic judgment no longer carries an explicit store environment.
    Formula scope is simply a subset check against the current atom-world
    domain.  Universal quantification is phrased directly with resource
    extensions whose input is the free-variable footprint of the body. *)

Section Formula.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).

Definition formula_scoped_in_world
    (m : WfWorldT) (φ : FormulaT) : Prop :=
  formula_fv φ ⊆ world_dom (m : WorldT).

Lemma formula_scoped_res_subset
    (m m' : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m φ →
  res_subset m m' →
  formula_scoped_in_world m' φ.
Proof.
  unfold formula_scoped_in_world.
  intros Hscope [Hdom _].
  unfold world_dom in *.
  change (formula_fv φ ⊆ ResourceCore.worldA_dom (m : WorldT)) in Hscope.
  change (formula_fv φ ⊆ ResourceCore.worldA_dom (m' : WorldT)).
  change (ResourceCore.worldA_dom (m : WorldT) =
          ResourceCore.worldA_dom (m' : WorldT)) in Hdom.
  rewrite Hdom in Hscope. exact Hscope.
Qed.

Lemma formula_scoped_world_dom_eq
    (m m' : WfWorldT) (φ : FormulaT) :
  world_dom (m : WorldT) = world_dom (m' : WorldT) →
  formula_scoped_in_world m φ →
  formula_scoped_in_world m' φ.
Proof.
  unfold formula_scoped_in_world. intros Hdom Hscope. rewrite <- Hdom.
  exact Hscope.
Qed.

Lemma formula_scoped_true_iff (m : WfWorldT) :
  formula_scoped_in_world m FTrue ↔ True.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm.
  split; [trivial | intros _ z Hz; rewrite lvars_fv_elem in Hz; set_solver].
Qed.

Lemma formula_scoped_false_iff (m : WfWorldT) :
  formula_scoped_in_world m FFalse ↔ True.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm.
  split; [trivial | intros _ z Hz; rewrite lvars_fv_elem in Hz; set_solver].
Qed.

Lemma formula_scoped_atom_iff (m : WfWorldT) q :
  formula_scoped_in_world m (FAtom q) ↔ lqual_fv q ⊆ world_dom (m : WorldT).
Proof. reflexivity. Qed.

Lemma formula_scoped_and_iff (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FAnd φ ψ) ↔
  formula_scoped_in_world m φ ∧ formula_scoped_in_world m ψ.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm. set_solver.
Qed.

Lemma formula_scoped_and_l (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FAnd φ ψ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_and_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_and_r (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FAnd φ ψ) ->
  formula_scoped_in_world m ψ.
Proof. intros Hscope. apply (proj1 (formula_scoped_and_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_or_iff (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FOr φ ψ) ↔
  formula_scoped_in_world m φ ∧ formula_scoped_in_world m ψ.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm. set_solver.
Qed.

Lemma formula_scoped_or_l (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FOr φ ψ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_or_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_or_r (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FOr φ ψ) ->
  formula_scoped_in_world m ψ.
Proof. intros Hscope. apply (proj1 (formula_scoped_or_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_impl_iff (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FImpl φ ψ) ↔
  formula_scoped_in_world m φ ∧ formula_scoped_in_world m ψ.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm. set_solver.
Qed.

Lemma formula_scoped_impl_l (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FImpl φ ψ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_impl_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_impl_r (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FImpl φ ψ) ->
  formula_scoped_in_world m ψ.
Proof. intros Hscope. apply (proj1 (formula_scoped_impl_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_star_iff (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FStar φ ψ) ↔
  formula_scoped_in_world m φ ∧ formula_scoped_in_world m ψ.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm. set_solver.
Qed.

Lemma formula_scoped_star_l (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FStar φ ψ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_star_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_star_r (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FStar φ ψ) ->
  formula_scoped_in_world m ψ.
Proof. intros Hscope. apply (proj1 (formula_scoped_star_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_wand_iff (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FWand φ ψ) ↔
  formula_scoped_in_world m φ ∧ formula_scoped_in_world m ψ.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm. set_solver.
Qed.

Lemma formula_scoped_wand_l (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FWand φ ψ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_wand_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_wand_r (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FWand φ ψ) ->
  formula_scoped_in_world m ψ.
Proof. intros Hscope. apply (proj1 (formula_scoped_wand_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_plus_iff (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FPlus φ ψ) ↔
  formula_scoped_in_world m φ ∧ formula_scoped_in_world m ψ.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm. set_solver.
Qed.

Lemma formula_scoped_plus_l (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FPlus φ ψ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_plus_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_plus_r (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FPlus φ ψ) ->
  formula_scoped_in_world m ψ.
Proof. intros Hscope. apply (proj1 (formula_scoped_plus_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_forall_iff (m : WfWorldT) φ :
  formula_scoped_in_world m (FForall φ) ↔
  formula_scoped_in_world m φ.
Proof. reflexivity. Qed.

Lemma formula_scoped_forall_body (m : WfWorldT) φ :
  formula_scoped_in_world m (FForall φ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_forall_iff m φ)); exact Hscope. Qed.

Lemma formula_scoped_over_iff (m : WfWorldT) φ :
  formula_scoped_in_world m (FOver φ) ↔
  formula_scoped_in_world m φ.
Proof. reflexivity. Qed.

Lemma formula_scoped_over_body (m : WfWorldT) φ :
  formula_scoped_in_world m (FOver φ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_over_iff m φ)); exact Hscope. Qed.

Lemma formula_scoped_under_iff (m : WfWorldT) φ :
  formula_scoped_in_world m (FUnder φ) ↔
  formula_scoped_in_world m φ.
Proof. reflexivity. Qed.

Lemma formula_scoped_under_body (m : WfWorldT) φ :
  formula_scoped_in_world m (FUnder φ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_under_iff m φ)); exact Hscope. Qed.

Lemma formula_scoped_fibvars_iff (m : WfWorldT) D φ :
  formula_scoped_in_world m (FFibVars D φ) ↔
  lvars_fv D ⊆ world_dom (m : WorldT) ∧ formula_scoped_in_world m φ.
Proof.
  unfold formula_scoped_in_world. formula_fv_syntax_norm. set_solver.
Qed.

Lemma formula_scoped_fibvars_l (m : WfWorldT) D φ :
  formula_scoped_in_world m (FFibVars D φ) ->
  lvars_fv D ⊆ world_dom (m : WorldT).
Proof. intros Hscope. apply (proj1 (formula_scoped_fibvars_iff m D φ)) in Hscope. tauto. Qed.

Lemma formula_scoped_fibvars_r (m : WfWorldT) D φ :
  formula_scoped_in_world m (FFibVars D φ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_fibvars_iff m D φ)) in Hscope. tauto. Qed.

Lemma formula_scoped_open_from_fv
    (m : WfWorldT) k x φ :
  formula_fv φ ∪ {[x]} ⊆ world_dom (m : WorldT) →
  formula_scoped_in_world m (formula_open k x φ).
Proof.
  unfold formula_scoped_in_world.
  intros Hscope.
  pose proof (formula_open_fv_subset k x φ) as Hopen.
  set_solver.
Qed.

Lemma formula_scoped_open_from_forall_world_dom
    (m my : WfWorldT) (φ : FormulaT) y :
  formula_scoped_in_world m (FForall φ) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  formula_scoped_in_world my (formula_open 0 y φ).
Proof.
  intros Hscope Hdom.
  eapply formula_scoped_open_from_fv.
  unfold formula_scoped_in_world in Hscope.
  rewrite formula_fv_forall in Hscope.
  rewrite Hdom.
  pose proof (formula_open_fv_subset 0 y φ).
  set_solver.
Qed.

Lemma formula_scoped_open
    (m : WfWorldT) k x φ :
  formula_scoped_in_world m φ →
  x ∈ world_dom (m : WorldT) →
  formula_scoped_in_world m (formula_open k x φ).
Proof.
  unfold formula_scoped_in_world.
  intros Hscope Hx.
  pose proof (formula_open_fv_subset k x φ) as Hopen.
  set_solver.
Qed.

Lemma formula_scoped_from_fv_subset
    (m : WfWorldT) (φ : FormulaT) (S : aset) :
  S ⊆ world_dom (m : WorldT) →
  formula_fv φ ⊆ S →
  formula_scoped_in_world m φ.
Proof.
  unfold formula_scoped_in_world. set_solver.
Qed.

Lemma formula_scoped_open_res_le
    (m n : WfWorldT) k x φ :
  formula_scoped_in_world m φ →
  m ⊑ n →
  x ∈ world_dom (n : WorldT) →
  formula_scoped_in_world n (formula_open k x φ).
Proof.
  unfold formula_scoped_in_world.
  intros Hscope Hle Hx.
  pose proof (raw_le_dom _ _ Hle) as Hdom.
  pose proof (formula_open_fv_subset k x φ) as Hopen.
  set_solver.
Qed.

Lemma formula_scoped_forall_open_res_le
    (m n : WfWorldT) x φ :
  formula_scoped_in_world m (FForall φ) →
  m ⊑ n →
  x ∈ world_dom (n : WorldT) →
  formula_scoped_in_world n (formula_open 0 x φ).
Proof.
  intros Hscope Hle Hx.
  eapply formula_scoped_open_res_le; [| exact Hle | exact Hx].
  eapply formula_scoped_forall_body. exact Hscope.
Qed.

End Formula.

(** * Context Logic semantics *)

Section Formula.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).

Fixpoint res_models_fuel
    (gas : nat) (m : WfWorldT) (φ : FormulaT) : Prop :=
  match gas with
  | 0 => False
  | S gas' =>
      formula_scoped_in_world m φ ∧
      match φ with
      | FTrue => True
      | FFalse => False
      | FAtom a =>
          logic_qualifier_denote a m
      | FAnd p q =>
          res_models_fuel gas' m p ∧
          res_models_fuel gas' m q
      | FOr p q =>
          res_models_fuel gas' m p ∨
          res_models_fuel gas' m q
      | FImpl p q =>
          ∀ m' : WfWorldT,
            m ⊑ m' →
            res_models_fuel gas' m' p →
            res_models_fuel gas' m' q
      | FStar p q =>
          ∃ (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
            res_product m1 m2 Hc ⊑ m ∧
            res_models_fuel gas' m1 p ∧
            res_models_fuel gas' m2 q
      | FWand p q =>
          ∀ (m' : WfWorldT) (Hc : world_compat m' m),
            res_models_fuel gas' m' p →
            res_models_fuel gas' (res_product m' m Hc) q
      | FPlus p q =>
          ∃ (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
            res_sum m1 m2 Hdef ⊑ m ∧
            res_models_fuel gas' m1 p ∧
            res_models_fuel gas' m2 q
      | FForall p =>
          ∃ L : aset,
            ∀ y : atom, y ∉ L →
            ∀ F : fiber_extension,
              ext_in F = formula_fv p →
              ext_out F = {[y]} →
              ∀ my : WfWorldT,
                res_extend_by m F my →
                res_models_fuel gas' my (formula_open 0 y p)
      | FOver p =>
          ∃ m' : WfWorldT,
            res_subset m m' ∧ res_models_fuel gas' m' p
      | FUnder p =>
          ∃ m' : WfWorldT,
            res_subset m' m ∧ res_models_fuel gas' m' p
	      | FFibVars D p =>
	          lc_lvars D ∧
	          ∀ (σ : Store (V := V)) (mfib : WfWorldT),
	            res_fiber_from_projection m (lvars_fv D) σ mfib →
	            res_models_fuel gas' mfib (formula_msubst_store σ p)
      end
  end.  

Lemma res_models_fuel_scoped
    (gas : nat) (m : WfWorldT) (φ : FormulaT) :
  res_models_fuel gas m φ →
  formula_scoped_in_world m φ.
Proof.
  destruct gas; simpl; [tauto | intros [Hscope _]; exact Hscope].
Qed.

Lemma res_models_fuel_irrel
    (gas1 gas2 : nat) (m : WfWorldT) (φ : FormulaT) :
  formula_measure φ <= gas1 →
  formula_measure φ <= gas2 →
  res_models_fuel gas1 m φ →
  res_models_fuel gas2 m φ.
Proof.
  assert (Hstrong :
    ∀ n (ψ : FormulaT) gas1 gas2 m,
      formula_measure ψ <= n →
      formula_measure ψ <= gas1 →
      formula_measure ψ <= gas2 →
      res_models_fuel gas1 m ψ →
      res_models_fuel gas2 m ψ).
  {
    induction n as [|n IHn].
    { intros ψ gasA gasB m0 Hn. pose proof (formula_measure_pos ψ). lia. }
    intros ψ gasA gasB m0 Hn HgasA HgasB Hmodel.
    destruct gasA as [|gasA']; [pose proof (formula_measure_pos ψ); lia |].
    destruct gasB as [|gasB']; [pose proof (formula_measure_pos ψ); lia |].
    simpl in *.
    destruct Hmodel as [Hscope Hmodel]. split; [exact Hscope |].
    destruct ψ as [| |a|p q|p q|p q|p q|p q|p q|p|p|p|D p];
      simpl in *.
    - exact Hmodel.
    - exact Hmodel.
    - exact Hmodel.
    - destruct Hmodel as [Hp Hq]. split.
      + exact (IHn p gasA' gasB' m0 ltac:(lia) ltac:(lia) ltac:(lia) Hp).
      + exact (IHn q gasA' gasB' m0 ltac:(lia) ltac:(lia) ltac:(lia) Hq).
    - destruct Hmodel as [Hp | Hq].
      + left. exact (IHn p gasA' gasB' m0 ltac:(lia) ltac:(lia) ltac:(lia) Hp).
      + right. exact (IHn q gasA' gasB' m0 ltac:(lia) ltac:(lia) ltac:(lia) Hq).
    - intros m' Hle Hp.
      pose proof (IHn p gasB' gasA' m' ltac:(lia) ltac:(lia) ltac:(lia) Hp)
        as Hp_src.
      exact (IHn q gasA' gasB' m' ltac:(lia) ltac:(lia) ltac:(lia)
        (Hmodel m' Hle Hp_src)).
    - destruct Hmodel as [m1 [m2 [Hc [Hprod [Hp Hq]]]]].
      exists m1, m2, Hc. split; [exact Hprod |]. split.
      + exact (IHn p gasA' gasB' m1 ltac:(lia) ltac:(lia) ltac:(lia) Hp).
      + exact (IHn q gasA' gasB' m2 ltac:(lia) ltac:(lia) ltac:(lia) Hq).
    - intros m' Hc Hp.
      pose proof (IHn p gasB' gasA' m' ltac:(lia) ltac:(lia) ltac:(lia) Hp)
        as Hp_src.
      exact (IHn q gasA' gasB' (res_product m' m0 Hc)
        ltac:(lia) ltac:(lia) ltac:(lia) (Hmodel m' Hc Hp_src)).
    - destruct Hmodel as [m1 [m2 [Hdef [Hsum [Hp Hq]]]]].
      exists m1, m2, Hdef. split; [exact Hsum |]. split.
      + exact (IHn p gasA' gasB' m1 ltac:(lia) ltac:(lia) ltac:(lia) Hp).
      + exact (IHn q gasA' gasB' m2 ltac:(lia) ltac:(lia) ltac:(lia) Hq).
    - destruct Hmodel as [L Hforall].
      exists L.
      intros y Hy F HFin HFout my Hext.
      exact (IHn (formula_open 0 y p) gasA' gasB' my
        ltac:(rewrite formula_open_preserves_measure; lia)
        ltac:(rewrite formula_open_preserves_measure; lia)
        ltac:(rewrite formula_open_preserves_measure; lia)
        (Hforall y Hy F HFin HFout my Hext)).
    - destruct Hmodel as [m' [Hsub Hp]].
      exists m'. split; [exact Hsub |].
      exact (IHn p gasA' gasB' m' ltac:(lia) ltac:(lia) ltac:(lia) Hp).
    - destruct Hmodel as [m' [Hsub Hp]].
      exists m'. split; [exact Hsub |].
      exact (IHn p gasA' gasB' m' ltac:(lia) ltac:(lia) ltac:(lia) Hp).
	    - destruct Hmodel as [Hlc Hfib]. split; [exact Hlc |].
	      intros σ mfib Hproj.
	      exact (IHn (formula_msubst_store σ p) gasA' gasB' mfib
	        ltac:(rewrite formula_msubst_store_preserves_measure; lia)
	        ltac:(rewrite formula_msubst_store_preserves_measure; lia)
	        ltac:(rewrite formula_msubst_store_preserves_measure; lia)
	        (Hfib σ mfib Hproj)).
  }
  eapply Hstrong with (n := formula_measure φ); eauto.
Qed.

Lemma res_restrict_scope_eq
    (m : WfWorldT) (X : aset) :
  X ⊆ world_dom (m : WorldT) →
  res_restrict m X = res_restrict (res_restrict m X) X.
Proof.
  intros HX.
  rewrite res_restrict_restrict_eq.
  replace (X ∩ X) with X by set_solver.
  reflexivity.
Qed.

Lemma formula_scoped_projection_on
    (m n : WfWorldT) (φ : FormulaT) (X : aset) :
  formula_fv φ ⊆ X →
  res_restrict m X = res_restrict n X →
  formula_scoped_in_world m φ →
  formula_scoped_in_world n φ.
Proof.
  unfold formula_scoped_in_world.
  intros HfvX Hproj Hscope.
  pose proof (f_equal (fun w : WfWorldT => world_dom (w : WorldT)) Hproj)
    as Hdom.
  simpl in Hdom. set_solver.
Qed.

Lemma extension_applicable_for_open
    (m : WfWorldT) (F : fiber_extension) (φ : FormulaT) (y : atom) :
  formula_scoped_in_world m φ →
  y ∉ world_dom (m : WorldT) →
  ext_in F = formula_fv φ →
  ext_out F = {[y]} →
  extension_applicable F m.
Proof.
  intros Hscope Hy HFin HFout.
  constructor.
  - unfold ext_in in HFin. rewrite HFin. exact Hscope.
  - unfold ext_out in HFout. rewrite HFout.
    apply elem_of_disjoint. intros z Hzout Hzm.
    apply elem_of_singleton in Hzout. subst z. set_solver.
Qed.

Lemma res_extend_by_open_projection_eq
    (m n my ny : WfWorldT) (F : fiber_extension)
    (φ : FormulaT) (y : atom) :
  ext_in F = formula_fv φ →
  ext_out F = {[y]} →
  res_restrict m (formula_fv φ) = res_restrict n (formula_fv φ) →
  res_extend_by m F my →
  res_extend_by n F ny →
  res_restrict my (formula_fv (formula_open 0 y φ)) =
  res_restrict ny (formula_fv (formula_open 0 y φ)).
Proof.
  intros HFin HFout Hproj Hmy Hny.
  assert (HprojF :
      res_restrict m (ext_in F) =
      res_restrict n (ext_in F)).
  { rewrite HFin. exact Hproj. }
  pose proof (res_extend_by_projection_eq m n F my ny HprojF Hmy Hny)
    as Hext_proj.
  eapply res_restrict_eq_subset.
  - pose proof (formula_open_fv_subset 0 y φ) as Hopen.
    exact Hopen.
  - rewrite <- HFin, <- HFout.
    exact Hext_proj.
Qed.

Lemma res_models_fuel_projection
    (gas : nat) (m n : WfWorldT) (φ : FormulaT) :
  res_restrict m (formula_fv φ) = res_restrict n (formula_fv φ) →
  res_models_fuel gas m φ →
  res_models_fuel gas n φ.
Proof.
  revert m n φ.
  induction gas as [|gas IH]; intros m n φ Hproj Hmodel; simpl in *.
  { exact Hmodel. }
  destruct Hmodel as [Hscope Hmodel].
  split.
  {
    eapply formula_scoped_projection_on; [| exact Hproj | exact Hscope].
    set_solver.
  }
  destruct φ as [| |a|p q|p q|p q|p q|p q|p q|p|p|p|D p];
    simpl in *.
  - exact I.
  - exact Hmodel.
  - apply (proj1 (logic_qualifier_denote_restrict a n (lqual_fv a) ltac:(set_solver))).
    change (res_restrict m (lqual_fv a) = res_restrict n (lqual_fv a)) in Hproj.
    replace (res_restrict n (lqual_fv a)) with (res_restrict m (lqual_fv a))
      by exact Hproj.
    apply (proj2 (logic_qualifier_denote_restrict a m (lqual_fv a) ltac:(set_solver))).
    exact Hmodel.
  - formula_fv_syntax_norm_in Hproj.
    destruct Hmodel as [Hp Hq]. split.
    + eapply IH; [| exact Hp].
      eapply res_restrict_eq_subset; [| exact Hproj]. set_solver.
    + eapply IH; [| exact Hq].
      eapply res_restrict_eq_subset; [| exact Hproj]. set_solver.
  - formula_fv_syntax_norm_in Hproj.
    destruct Hmodel as [Hp | Hq].
    + left. eapply IH; [| exact Hp].
      eapply res_restrict_eq_subset; [| exact Hproj]. set_solver.
    + right. eapply IH; [| exact Hq].
      eapply res_restrict_eq_subset; [| exact Hproj]. set_solver.
  - formula_fv_syntax_norm_in Hproj.
    intros n' Hle_n Hpn'.
    assert (Hscope_n : formula_scoped_in_world n (FImpl p q)).
    {
      eapply formula_scoped_projection_on; [| exact Hproj | exact Hscope].
      formula_fv_syntax_norm. set_solver.
    }
    apply (proj1 (formula_scoped_impl_iff n p q)) in Hscope_n
      as [Hp_scope_n Hq_scope_n].
    assert (Hproj_p_nm : res_restrict n' (formula_fv p) =
      res_restrict m (formula_fv p)).
    {
      transitivity (res_restrict n (formula_fv p)).
      - symmetry. apply res_restrict_le_eq; [exact Hle_n | exact Hp_scope_n].
      - symmetry. eapply res_restrict_eq_subset; [| exact Hproj]. set_solver.
    }
    pose proof (IH n' m p Hproj_p_nm Hpn') as Hpm.
    pose proof (Hmodel m (reflexivity _) Hpm) as Hqm.
    eapply IH; [| exact Hqm].
    transitivity (res_restrict n (formula_fv q)).
    + eapply res_restrict_eq_subset; [| exact Hproj]. set_solver.
    + apply res_restrict_le_eq; [exact Hle_n | exact Hq_scope_n].
  - formula_fv_syntax_norm_in Hproj.
    destruct Hmodel as [m1 [m2 [Hc [Hprod [Hp Hq]]]]].
    set (X := formula_fv (FStar p q)).
    assert (HprojX : res_restrict m X = res_restrict n X).
    { subst X. formula_fv_syntax_norm. exact Hproj. }
    destruct (res_product_restrict_same_le m m1 m2 X Hc Hprod) as [HcX HprodX].
    exists (res_restrict m1 X), (res_restrict m2 X), HcX.
    split.
    {
      etrans; [exact HprodX |].
      rewrite HprojX. apply res_restrict_le.
    }
    split.
    + eapply IH; [| exact Hp].
      rewrite res_restrict_restrict_eq.
      replace (X ∩ formula_fv p) with (formula_fv p)
        by (subst X; formula_fv_syntax_norm; set_solver).
      reflexivity.
    + eapply IH; [| exact Hq].
      rewrite res_restrict_restrict_eq.
      replace (X ∩ formula_fv q) with (formula_fv q)
        by (subst X; formula_fv_syntax_norm; set_solver).
      reflexivity.
  - formula_fv_syntax_norm_in Hproj.
    intros narg Hc_n Hpnarg.
    set (X := formula_fv (FWand p q)).
    assert (HprojX : res_restrict m X = res_restrict n X).
    { subst X. formula_fv_syntax_norm. exact Hproj. }
    assert (Hc_mid : world_compat narg (res_restrict m X)).
    {
      rewrite HprojX.
      eapply world_compat_le_r.
      - apply res_restrict_le.
      - exact Hc_n.
    }
    assert (Hc_small : world_compat (res_restrict narg (formula_fv p)) m).
    {
      eapply world_compat_restrict_l_full_r with (S := X).
      - subst X. formula_fv_syntax_norm. set_solver.
      - exact Hc_mid.
    }
    assert (Hp_small : res_models_fuel gas (res_restrict narg (formula_fv p)) p).
    {
      eapply IH; [| exact Hpnarg].
      rewrite res_restrict_restrict_eq.
      replace (formula_fv p ∩ formula_fv p) with (formula_fv p) by set_solver.
      reflexivity.
    }
    pose proof (Hmodel (res_restrict narg (formula_fv p)) Hc_small Hp_small)
      as Hq_orig.
    set (orig := res_product (res_restrict narg (formula_fv p)) m Hc_small).
    set (target := res_product narg n Hc_n).
    assert (Hle_orig_target :
      res_restrict orig (formula_fv q) ⊑ target).
    {
      subst orig target.
      etrans.
      - eapply (res_product_restrict_wand_le narg m X (formula_fv p) (formula_fv q)
          Hc_small Hc_mid).
        + subst X.
          formula_fv_syntax_norm. set_solver.
        + apply (proj1 (formula_scoped_wand_iff m p q)) in Hscope.
          exact (proj2 Hscope).
      - eapply res_product_le_mono; [reflexivity |].
        rewrite HprojX. apply res_restrict_le.
    }
    eapply IH; [| exact Hq_orig].
    transitivity (res_restrict (res_restrict orig (formula_fv q)) (formula_fv q)).
    + rewrite res_restrict_restrict_eq.
      replace (formula_fv q ∩ formula_fv q) with (formula_fv q) by set_solver.
      reflexivity.
    + apply res_restrict_le_eq.
      * exact Hle_orig_target.
      * pose proof (res_models_fuel_scoped gas orig q Hq_orig) as Hscope_orig.
        unfold formula_scoped_in_world in Hscope_orig. simpl. set_solver.
  - formula_fv_syntax_norm_in Hproj.
    destruct Hmodel as [m1 [m2 [Hdef [Hsum [Hp Hq]]]]].
    set (X := formula_fv (FPlus p q)).
    assert (HprojX : res_restrict m X = res_restrict n X).
    { subst X. formula_fv_syntax_norm. exact Hproj. }
    destruct (res_sum_restrict_same_le m m1 m2 X Hdef Hsum) as [HdefX HsumX].
    exists (res_restrict m1 X), (res_restrict m2 X), HdefX.
    split.
    {
      etrans; [exact HsumX |].
      rewrite HprojX. apply res_restrict_le.
    }
    split.
    + eapply IH; [| exact Hp].
      rewrite res_restrict_restrict_eq.
      replace (X ∩ formula_fv p) with (formula_fv p)
        by (subst X; formula_fv_syntax_norm; set_solver).
      reflexivity.
    + eapply IH; [| exact Hq].
      rewrite res_restrict_restrict_eq.
      replace (X ∩ formula_fv q) with (formula_fv q)
        by (subst X; formula_fv_syntax_norm; set_solver).
      reflexivity.
  - destruct Hmodel as [L Hforall].
    exists (L ∪ world_dom (m : WorldT)).
    intros y Hy F HFin HFout ny Hny.
    assert (Happ_m : extension_applicable F m).
    {
      eapply extension_applicable_for_open; eauto.
      set_solver.
    }
    destruct (res_extend_by_exists m F Happ_m) as [my Hmy].
    pose proof (Hforall y ltac:(set_solver) F HFin HFout my Hmy) as Hpmy.
    eapply IH; [| exact Hpmy].
    eapply res_extend_by_open_projection_eq; eauto.
  - destruct Hmodel as [m' [Hsub Hp]].
    set (X := formula_fv p).
    change (res_restrict m X = res_restrict n X) in Hproj.
    destruct (res_subset_lift_over_projection_on m n m' X Hproj Hsub)
      as [n' [Hsub_n Hle_X]].
    exists n'. split; [exact Hsub_n |].
    assert (HpX : res_models_fuel gas (res_restrict m' X) p).
    {
      eapply IH; [| exact Hp].
      subst X. rewrite res_restrict_restrict_eq.
      replace (formula_fv p ∩ formula_fv p) with (formula_fv p) by set_solver.
      reflexivity.
    }
    eapply IH; [| exact HpX].
    apply res_restrict_le_eq.
    + exact Hle_X.
    + subst X. eapply res_models_fuel_scoped; exact HpX.
  - destruct Hmodel as [m' [Hsub Hp]].
    set (X := formula_fv p).
    change (res_restrict m X = res_restrict n X) in Hproj.
    destruct (res_subset_lift_under_projection_on m n m' X Hproj Hsub)
      as [n' [Hsub_n Hle_X]].
    exists n'. split; [exact Hsub_n |].
    assert (HpX : res_models_fuel gas (res_restrict m' X) p).
    {
      eapply IH; [| exact Hp].
      subst X. rewrite res_restrict_restrict_eq.
      replace (formula_fv p ∩ formula_fv p) with (formula_fv p) by set_solver.
      reflexivity.
    }
    eapply IH; [| exact HpX].
    apply res_restrict_le_eq.
    + exact Hle_X.
    + subst X. eapply res_models_fuel_scoped; exact HpX.
  - formula_fv_syntax_norm_in Hproj.
    destruct Hmodel as [Hlc Hfib]. split; [exact Hlc |].
	    intros σ nfib Hproj_n.
	    set (Dfv := lvars_fv D).
	    assert (HDfvX : Dfv ⊆ Dfv ∪ formula_fv p) by set_solver.
    assert (HDfvm : Dfv ⊆ world_dom (m : WorldT)).
    {
      unfold formula_scoped_in_world, formula_fv in Hscope.
      formula_fv_syntax_norm_in Hscope.
      subst Dfv. set_solver.
    }
    assert (HprojX :
      res_restrict m (Dfv ∪ formula_fv p) =
      res_restrict n (Dfv ∪ formula_fv p)).
    { unfold Dfv, formula_fv. exact Hproj. }
	    pose proof (res_fiber_from_projection_transport_on
	      m n nfib σ Dfv (Dfv ∪ formula_fv p)
	      HDfvX HDfvm HprojX Hproj_n) as Htransport.
	    destruct Htransport as [mfib [Hproj_m Hfib_proj]].
	    pose proof (Hfib σ mfib Hproj_m) as Hpm.
	    apply (IH mfib nfib (formula_msubst_store σ p)).
	    + eapply res_restrict_eq_subset; [| exact Hfib_proj].
	      pose proof (formula_msubst_store_fv_subset σ p). set_solver.
	    + exact Hpm.
Qed.

Lemma res_models_fuel_restrict_fv
    (gas : nat) (m : WfWorldT) (φ : FormulaT) :
  res_models_fuel gas m φ →
  res_models_fuel gas (res_restrict m (formula_fv φ)) φ.
Proof.
  intros Hmodel.
  eapply res_models_fuel_projection; [| exact Hmodel].
  apply res_restrict_scope_eq.
  eapply res_models_fuel_scoped; exact Hmodel.
Qed.

Lemma res_models_fuel_kripke
    (gas : nat) (m n : WfWorldT) (φ : FormulaT) :
  m ⊑ n →
  res_models_fuel gas m φ →
  res_models_fuel gas n φ.
Proof.
  intros Hle Hmodel.
  eapply res_models_fuel_projection; [| exact Hmodel].
  apply res_restrict_le_eq.
  - exact Hle.
  - eapply res_models_fuel_scoped; exact Hmodel.
Qed.

Definition res_models (m : WfWorldT) (φ : FormulaT) : Prop :=
  res_models_fuel (formula_measure φ) m φ.

Lemma res_models_scoped (m : WfWorldT) (φ : FormulaT) :
  res_models m φ ->
  formula_scoped_in_world m φ.
Proof.
  unfold res_models. apply res_models_fuel_scoped.
Qed.

Definition entails (φ ψ : FormulaT) : Prop :=
  ∀ m, res_models m φ → res_models m ψ.

Lemma res_models_kripke
    (m n : WfWorldT) (φ : FormulaT) :
  m ⊑ n →
  res_models m φ →
  res_models n φ.
Proof.
  unfold res_models. apply res_models_fuel_kripke.
Qed.

Lemma res_models_restrict_fv (m : WfWorldT) (φ : FormulaT) :
  res_models m φ →
  res_models (res_restrict m (formula_fv φ)) φ.
Proof.
  unfold res_models. apply res_models_fuel_restrict_fv.
Qed.

Lemma res_models_minimal_on (S : aset) (m : WfWorldT) (φ : FormulaT) :
  formula_fv φ ⊆ S →
  res_models m φ ↔ res_models (res_restrict m S) φ.
Proof.
  intros Hfv. split.
  - intros Hm.
    eapply res_models_kripke.
    + apply res_restrict_mono. exact Hfv.
    + apply res_models_restrict_fv. exact Hm.
  - intros Hm.
    eapply res_models_kripke; [apply res_restrict_le | exact Hm].
Qed.

Lemma res_models_restrict_fv_iff (m : WfWorldT) (φ : FormulaT) :
  res_models m φ ↔ res_models (res_restrict m (formula_fv φ)) φ.
Proof.
  apply res_models_minimal_on. set_solver.
Qed.

Lemma res_models_formula_msubst_store_agree_fv
    (σ1 σ2 : Store (V := V)) (φ : FormulaT) (m : WfWorldT) :
  store_restrict σ1 (formula_fv φ) =
  store_restrict σ2 (formula_fv φ) ->
  res_models m (formula_msubst_store σ1 φ) ->
  res_models m (formula_msubst_store σ2 φ).
Proof.
  intros Hagree Hmodels.
  rewrite <- (formula_msubst_store_agree_fv σ1 σ2 φ Hagree).
  exact Hmodels.
Qed.

Lemma res_models_impl_refl (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m φ →
  res_models m (FImpl φ φ).
Proof.
  unfold res_models. simpl. intros Hscope. split.
  - apply (proj2 (formula_scoped_impl_iff m φ φ)). split; exact Hscope.
  - intros m' _ Hφ. eapply res_models_fuel_irrel; [| | exact Hφ]; lia.
Qed.

Lemma res_models_and_elim_l (m : WfWorldT) (φ ψ : FormulaT) :
  res_models m (FAnd φ ψ) →
  res_models m φ.
Proof.
  unfold res_models. simpl. intros [_ [Hφ _]].
  eapply res_models_fuel_irrel; [| | exact Hφ]; lia.
Qed.

Lemma res_models_and_elim_r (m : WfWorldT) (φ ψ : FormulaT) :
  res_models m (FAnd φ ψ) →
  res_models m ψ.
Proof.
  unfold res_models. simpl. intros [_ [_ Hψ]].
  eapply res_models_fuel_irrel; [| | exact Hψ]; lia.
Qed.

Lemma res_models_and_intro (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FAnd φ ψ) →
  res_models m φ →
  res_models m ψ →
  res_models m (FAnd φ ψ).
Proof.
  unfold res_models. simpl. intros Hscope Hφ Hψ. split; [exact Hscope |].
  split.
  - eapply res_models_fuel_irrel; [| | exact Hφ]; lia.
  - eapply res_models_fuel_irrel; [| | exact Hψ]; lia.
Qed.

Lemma res_models_or_intro_l (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FOr φ ψ) →
  res_models m φ →
  res_models m (FOr φ ψ).
Proof.
  unfold res_models. simpl. intros Hscope Hφ. split; [exact Hscope |].
  left. eapply res_models_fuel_irrel; [| | exact Hφ]; lia.
Qed.

Lemma res_models_or_intro_r (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FOr φ ψ) →
  res_models m ψ →
  res_models m (FOr φ ψ).
Proof.
  unfold res_models. simpl. intros Hscope Hψ. split; [exact Hscope |].
  right. eapply res_models_fuel_irrel; [| | exact Hψ]; lia.
Qed.

End Formula.

(** * ContextLogic.FormulaSemantics *)


Ltac models_fuel_finish :=
  rewrite ?formula_open_preserves_measure;
  rewrite ?formula_mlsubst_preserves_measure;
  rewrite ?formula_msubst_store_preserves_measure;
  simpl; lia.

Tactic Notation "models_fuel_irrel" constr(H) :=
  eapply res_models_fuel_irrel; [| | exact H]; models_fuel_finish.

Ltac models_fuel_irrel_auto :=
  eapply res_models_fuel_irrel; [| | eassumption]; models_fuel_finish.

Ltac formula_scope_syntax_norm :=
  rewrite ?formula_scoped_true_iff, ?formula_scoped_false_iff;
  rewrite ?formula_scoped_atom_iff;
  rewrite ?formula_scoped_and_iff, ?formula_scoped_or_iff;
  rewrite ?formula_scoped_impl_iff;
  rewrite ?formula_scoped_star_iff, ?formula_scoped_wand_iff;
  rewrite ?formula_scoped_plus_iff;
  rewrite ?formula_scoped_forall_iff;
  rewrite ?formula_scoped_over_iff, ?formula_scoped_under_iff;
  rewrite ?formula_scoped_fibvars_iff.

Ltac formula_scope_syntax_norm_in H :=
  rewrite ?formula_scoped_true_iff in H;
  rewrite ?formula_scoped_false_iff in H;
  rewrite ?formula_scoped_atom_iff in H;
  rewrite ?formula_scoped_and_iff in H;
  rewrite ?formula_scoped_or_iff in H;
  rewrite ?formula_scoped_impl_iff in H;
  rewrite ?formula_scoped_star_iff in H;
  rewrite ?formula_scoped_wand_iff in H;
  rewrite ?formula_scoped_plus_iff in H;
  rewrite ?formula_scoped_forall_iff in H;
  rewrite ?formula_scoped_over_iff in H;
  rewrite ?formula_scoped_under_iff in H;
  rewrite ?formula_scoped_fibvars_iff in H.

Ltac formula_semantics_norm :=
  formula_syntax_norm;
  formula_scope_syntax_norm.

Ltac formula_semantics_norm_in H :=
  formula_syntax_norm_in H;
  formula_scope_syntax_norm_in H.

Ltac formula_scope_step :=
  match goal with
  | Hscope : formula_scoped_in_world ?m (FAnd ?p ?q)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_and_l; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FAnd ?p ?q)
    |- formula_scoped_in_world ?m ?q =>
      eapply formula_scoped_and_r; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FOr ?p ?q)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_or_l; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FOr ?p ?q)
    |- formula_scoped_in_world ?m ?q =>
      eapply formula_scoped_or_r; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FImpl ?p ?q)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_impl_l; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FImpl ?p ?q)
    |- formula_scoped_in_world ?m ?q =>
      eapply formula_scoped_impl_r; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FStar ?p ?q)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_star_l; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FStar ?p ?q)
    |- formula_scoped_in_world ?m ?q =>
      eapply formula_scoped_star_r; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FWand ?p ?q)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_wand_l; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FWand ?p ?q)
    |- formula_scoped_in_world ?m ?q =>
      eapply formula_scoped_wand_r; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FPlus ?p ?q)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_plus_l; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FPlus ?p ?q)
    |- formula_scoped_in_world ?m ?q =>
      eapply formula_scoped_plus_r; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FForall ?p)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_forall_body; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FOver ?p)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_over_body; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FUnder ?p)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_under_body; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FFibVars ?D ?p)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_fibvars_r; exact Hscope
  end.

Ltac formula_scope_solve :=
  solve [eassumption | formula_scope_step | formula_scope_syntax_norm; tauto].

Ltac pose_formula_scoped_forall_open_from_dom m n y Hscope Hle Hdom :=
  let Hopened := fresh "Hopened_scope_my" in
  pose proof (formula_scoped_forall_open_res_le
    m n y _ Hscope Hle
    ltac:(rewrite Hdom; set_solver)) as Hopened.
