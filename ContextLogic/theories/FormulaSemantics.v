From ContextLogic Require Export FormulaSyntax.
From ContextLogic Require Import FormulaSyntax.
From ContextBase Require Import LogicVarOpenEnv.
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

Arguments formula_scoped_in_world _ _ /.

Lemma formula_scoped_true_iff (m : WfWorldT) :
  formula_scoped_in_world m FTrue ↔ True.
Proof.
  cbn [formula_scoped_in_world].
  rewrite formula_fv_true.
  split; [done|].
  intros _. intros x Hx.
  rewrite elem_of_empty in Hx. contradiction.
Qed.

Lemma formula_scoped_false_iff (m : WfWorldT) :
  formula_scoped_in_world m FFalse ↔ True.
Proof.
  cbn [formula_scoped_in_world].
  rewrite formula_fv_false.
  split; [done|].
  intros _. intros x Hx.
  rewrite elem_of_empty in Hx. contradiction.
Qed.

Lemma formula_scoped_atom_iff (m : WfWorldT) q :
  formula_scoped_in_world m (FAtom q) ↔ qual_dom q ⊆ world_dom (m : WorldT).
Proof.
  cbn [formula_scoped_in_world].
  rewrite formula_fv_atom.
  reflexivity.
Qed.

Lemma formula_scoped_and_iff (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FAnd φ ψ) ↔
  formula_scoped_in_world m φ ∧ formula_scoped_in_world m ψ.
Proof.
  cbn [formula_scoped_in_world].
  rewrite formula_fv_and. set_solver.
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
  cbn [formula_scoped_in_world].
  rewrite formula_fv_or. set_solver.
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
  cbn [formula_scoped_in_world].
  rewrite formula_fv_impl. set_solver.
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
  cbn [formula_scoped_in_world].
  rewrite formula_fv_star. set_solver.
Qed.

Lemma formula_scoped_star_l (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FStar φ ψ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_star_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_star_r (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FStar φ ψ) ->
  formula_scoped_in_world m ψ.
Proof. intros Hscope. apply (proj1 (formula_scoped_star_iff m φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_fbwand_iff (m : WfWorldT) d φ ψ :
  formula_scoped_in_world m (FBWand d φ ψ) ↔
  formula_scoped_in_world m φ ∧ formula_scoped_in_world m ψ.
Proof.
  cbn [formula_scoped_in_world].
  rewrite formula_fv_fbwand.
  rewrite (formula_lvars_at_fv d φ), (formula_lvars_at_fv d ψ).
  set_solver.
Qed.

Lemma formula_scoped_fbwand_l (m : WfWorldT) d φ ψ :
  formula_scoped_in_world m (FBWand d φ ψ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_fbwand_iff m d φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_fbwand_r (m : WfWorldT) d φ ψ :
  formula_scoped_in_world m (FBWand d φ ψ) ->
  formula_scoped_in_world m ψ.
Proof. intros Hscope. apply (proj1 (formula_scoped_fbwand_iff m d φ ψ)) in Hscope. tauto. Qed.

Lemma formula_scoped_plus_iff (m : WfWorldT) φ ψ :
  formula_scoped_in_world m (FPlus φ ψ) ↔
  formula_scoped_in_world m φ ∧ formula_scoped_in_world m ψ.
Proof.
  cbn [formula_scoped_in_world].
  rewrite formula_fv_plus. set_solver.
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
Proof.
  cbn [formula_scoped_in_world].
  rewrite formula_fv_forall, formula_lvars_at_fv. reflexivity.
Qed.

Lemma formula_scoped_forall_body (m : WfWorldT) φ :
  formula_scoped_in_world m (FForall φ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. exact (proj1 (formula_scoped_forall_iff m φ) Hscope). Qed.

Lemma formula_scoped_over_iff (m : WfWorldT) φ :
  formula_scoped_in_world m (FOver φ) ↔
  formula_scoped_in_world m φ.
Proof.
  cbn [formula_scoped_in_world].
  rewrite formula_fv_over. reflexivity.
Qed.

Lemma formula_scoped_over_body (m : WfWorldT) φ :
  formula_scoped_in_world m (FOver φ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. exact (proj1 (formula_scoped_over_iff m φ) Hscope). Qed.

Lemma formula_scoped_under_iff (m : WfWorldT) φ :
  formula_scoped_in_world m (FUnder φ) ↔
  formula_scoped_in_world m φ.
Proof.
  cbn [formula_scoped_in_world].
  rewrite formula_fv_under. reflexivity.
Qed.

Lemma formula_scoped_under_body (m : WfWorldT) φ :
  formula_scoped_in_world m (FUnder φ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. exact (proj1 (formula_scoped_under_iff m φ) Hscope). Qed.

Lemma formula_scoped_persist_iff (m : WfWorldT) φ :
  formula_scoped_in_world m (FPersist φ) ↔
  formula_scoped_in_world m φ.
Proof.
  cbn [formula_scoped_in_world].
  rewrite formula_fv_persist. reflexivity.
Qed.

Lemma formula_scoped_persist_body (m : WfWorldT) φ :
  formula_scoped_in_world m (FPersist φ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. exact (proj1 (formula_scoped_persist_iff m φ) Hscope). Qed.

Lemma formula_scoped_fibvars_iff (m : WfWorldT) D φ :
  formula_scoped_in_world m (FFibVars D φ) ↔
  lvars_fv D ⊆ world_dom (m : WorldT) ∧ formula_scoped_in_world m φ.
Proof.
  cbn [formula_scoped_in_world].
  rewrite formula_fv_fibvars. set_solver.
Qed.

Lemma formula_scoped_fibvars_r (m : WfWorldT) D φ :
  formula_scoped_in_world m (FFibVars D φ) ->
  formula_scoped_in_world m φ.
Proof. intros Hscope. apply (proj1 (formula_scoped_fibvars_iff m D φ)) in Hscope. tauto. Qed.

Lemma formula_scoped_open_from_fv
    (m : WfWorldT) k x φ :
  formula_fv φ ∪ {[x]} ⊆ world_dom (m : WorldT) →
  formula_scoped_in_world m (formula_open k x φ).
Proof.
  intros Hscope.
  pose proof (formula_open_fv_subset k x φ) as Hopen.
  set_solver.
Qed.

Lemma formula_scoped_open_res_le
    (m n : WfWorldT) k x φ :
  formula_scoped_in_world m φ →
  m ⊑ n →
  x ∈ world_dom (n : WorldT) →
  formula_scoped_in_world n (formula_open k x φ).
Proof.
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

Definition open_env_binds (d : nat) (η : gmap nat atom) : Prop :=
  open_env_values_inj η ∧
  ∀ k : nat, k < d ↔ is_Some (η !! k).

Lemma open_env_binds_one_inv η :
  open_env_binds 1 η ->
  exists y, η = <[0 := y]> (∅ : gmap nat atom).
Proof.
  intros [_ Hbind].
  destruct (proj1 (Hbind 0) ltac:(lia)) as [y Hy].
  exists y.
  apply map_eq. intros [|k].
  - rewrite lookup_insert_eq. exact Hy.
  - rewrite lookup_insert_ne by lia.
    rewrite lookup_empty.
    destruct (η !! S k) as [z|] eqn:Hz; [|reflexivity].
    exfalso.
    pose proof (proj2 (Hbind (S k)) (ex_intro _ z Hz)) as Hlt.
    lia.
Qed.

Fixpoint res_models_fuel
    (gas : nat) (m : WfWorldT) (φ : FormulaT) : Prop :=
  match gas with
  | 0 => False
  | S gas' =>
      formula_fv φ ⊆ world_dom (m : WorldT) ∧
      match φ with
      | FTrue => True
      | FFalse => False
      | FAtom a =>
          qualifier_exact_denote a m
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
      | FBWand d p q =>
          ∃ L : aset,
            ∀ (η : gmap nat atom) (m' : WfWorldT)
              (Hc : world_compat m' m),
              open_env_binds d η →
              open_env_atoms η ## L →
              world_dom (res_product m' m Hc : WorldT) =
                world_dom (m : WorldT) ∪ open_env_atoms η →
              res_models_fuel gas' m' (formula_open_env η p) →
              res_models_fuel gas' (res_product m' m Hc)
                (formula_open_env η q)
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
      | FPersist p =>
          ∃ σ : Store (V := V),
            dom (σ : Store (V := V)) = formula_fv p ∧
            res_restrict m (formula_fv p) =
              (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ∧
            res_models_fuel gas'
              (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) p
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
    destruct ψ as [| |a|p q|p q|p q|p q|d p q|p q|p|p|p|p|D p];
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
    - destruct Hmodel as [L Hmodel].
      exists L. intros η m' Hc Hbind Hfresh Hdom Hp.
      pose proof (IHn (formula_open_env η p) gasB' gasA' m'
        ltac:(rewrite formula_open_env_preserves_measure; lia)
        ltac:(rewrite formula_open_env_preserves_measure; lia)
        ltac:(rewrite formula_open_env_preserves_measure; lia) Hp)
        as Hp_src.
      exact (IHn (formula_open_env η q) gasA' gasB'
        (res_product m' m0 Hc)
        ltac:(rewrite formula_open_env_preserves_measure; lia)
        ltac:(rewrite formula_open_env_preserves_measure; lia)
        ltac:(rewrite formula_open_env_preserves_measure; lia)
        (Hmodel η m' Hc Hbind Hfresh Hdom Hp_src)).
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
    - destruct Hmodel as [σ [Hdomσ [Hrestrict Hp]]].
      exists σ. repeat split; try assumption.
      exact (IHn p gasA' gasB'
        (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT)
        ltac:(lia) ltac:(lia) ltac:(lia) Hp).
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

Lemma res_restrict_eq_union_l
    (m n : WfWorldT) (X Y : aset) :
  res_restrict m (X ∪ Y) = res_restrict n (X ∪ Y) ->
  res_restrict m X = res_restrict n X.
Proof.
  intros Hproj.
  eapply res_restrict_eq_subset; [| exact Hproj].
  set_solver.
Qed.

Lemma res_restrict_eq_union_r
    (m n : WfWorldT) (X Y : aset) :
  res_restrict m (X ∪ Y) = res_restrict n (X ∪ Y) ->
  res_restrict m Y = res_restrict n Y.
Proof.
  intros Hproj.
  eapply res_restrict_eq_subset; [| exact Hproj].
  set_solver.
Qed.

Lemma res_models_fuel_projection_fbwand_case
    (gas : nat)
    (IH : forall (m n : WfWorldT) (φ : FormulaT),
      res_restrict m (formula_fv φ) = res_restrict n (formula_fv φ) ->
      res_models_fuel gas m φ ->
      res_models_fuel gas n φ)
    (m n : WfWorldT) d (p q : FormulaT) :
  res_restrict m (formula_fv (FBWand d p q)) =
    res_restrict n (formula_fv (FBWand d p q)) ->
  formula_scoped_in_world m (FBWand d p q) ->
  (exists L : aset,
    forall (η : gmap nat atom) (marg : WfWorldT)
      (Hc : world_compat marg m),
      open_env_binds d η ->
      open_env_atoms η ## L ->
      world_dom (res_product marg m Hc : WorldT) =
        world_dom (m : WorldT) ∪ open_env_atoms η ->
      res_models_fuel gas marg (formula_open_env η p) ->
      res_models_fuel gas
        (res_product marg m Hc)
        (formula_open_env η q)) ->
  exists L : aset,
    forall (η : gmap nat atom) (narg : WfWorldT)
      (Hc : world_compat narg n),
      open_env_binds d η ->
      open_env_atoms η ## L ->
      world_dom (res_product narg n Hc : WorldT) =
        world_dom (n : WorldT) ∪ open_env_atoms η ->
      res_models_fuel gas narg (formula_open_env η p) ->
      res_models_fuel gas
        (res_product narg n Hc)
        (formula_open_env η q).
Proof.
  intros Hproj Hscope [Lsrc Hsrc].
  exists (Lsrc ∪ world_dom (m : WorldT) ∪ world_dom (n : WorldT)).
  intros η narg Hc_tgt Hbind Hfresh Hdom_tgt Harg_tgt.
  set (C := formula_fv (FBWand d p q)).
  set (A := open_env_atoms η).
  set (X := formula_fv (formula_open_env η p) ∪ A).
  set (Y := formula_fv (formula_open_env η q)).
  assert (Hfresh_src : A ## Lsrc) by (subst A; set_solver).
  assert (HAm : A ## world_dom (m : WorldT)) by (subst A; set_solver).
  assert (HAn : A ## world_dom (n : WorldT)) by (subst A; set_solver).
  assert (HCm : C ⊆ world_dom (m : WorldT)).
  { subst C. exact Hscope. }
  assert (HpC : formula_fv p ⊆ C).
  {
    subst C.
    rewrite formula_fv_fbwand.
    rewrite (formula_lvars_at_fv d p).
    set_solver.
  }
  assert (HqC : formula_fv q ⊆ C).
  {
    subst C.
    rewrite formula_fv_fbwand.
    rewrite (formula_lvars_at_fv d q).
    set_solver.
  }
  assert (HX : X ⊆ C ∪ A).
  {
    subst X A.
    pose proof (formula_open_env_fv_subset η p) as Hopen.
    intros z Hz.
    apply elem_of_union in Hz as [Hzp|HzA].
    - pose proof (Hopen z Hzp) as Hzopen.
      apply elem_of_union in Hzopen as [Hzp0|HzA].
      + apply elem_of_union_l.
        apply HpC. exact Hzp0.
      + apply elem_of_union_r. exact HzA.
    - apply elem_of_union_r. exact HzA.
  }
  assert (HAX : A ⊆ X) by (subst X; set_solver).
  assert (HY : Y ⊆ C ∪ A).
  {
    subst Y A.
    pose proof (formula_open_env_fv_subset η q) as Hopen.
    intros z Hz.
    pose proof (Hopen z Hz) as Hzopen.
    apply elem_of_union in Hzopen as [Hzq|HzA].
    - apply elem_of_union_l.
      apply HqC. exact Hzq.
    - apply elem_of_union_r. exact HzA.
  }
  destruct (res_product_restrict_binder_arg_projection
    m n narg C X A Y Hc_tgt Hproj HCm HAm HAn Hdom_tgt
    HX HAX HY) as [Hc_src [Hdom_src Hprod_proj]].
  assert (Harg_src :
      res_models_fuel gas (res_restrict narg X) (formula_open_env η p)).
  {
    eapply (IH narg (res_restrict narg X) (formula_open_env η p)).
    - subst X.
      rewrite res_restrict_restrict_eq.
      replace ((formula_fv (formula_open_env η p) ∪ A) ∩
        formula_fv (formula_open_env η p))
        with (formula_fv (formula_open_env η p)) by set_solver.
      reflexivity.
    - exact Harg_tgt.
  }
  pose proof (Hsrc η (res_restrict narg X) Hc_src
    Hbind Hfresh_src Hdom_src Harg_src) as Hres_src.
  eapply IH.
  - subst Y. exact Hprod_proj.
  - exact Hres_src.
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
  destruct φ as [| |a|p q|p q|p q|p q|d p q|p q|p|p|p|p|D p];
    simpl in *.
  - exact I.
  - exact Hmodel.
  - apply (proj1 (qualifier_exact_denote_restrict a n (qual_dom a) ltac:(set_solver))).
    rewrite formula_fv_atom in Hproj.
    pose proof (proj2 (qualifier_exact_denote_restrict a m (qual_dom a)
      ltac:(set_solver)) Hmodel) as Hm_restrict.
    change (qualifier_exact_denote a (res_restrict n (qual_dom a))).
    assert (Hrn :
      res_restrict n (qual_dom a) = res_restrict m (qual_dom a)).
    {
      unfold qual_dom, qual_vars.
      change
        (res_restrict m (lvars_fv (qual_lvars a)) =
         res_restrict n (lvars_fv (qual_lvars a))) in Hproj.
      symmetry. exact Hproj.
    }
    rewrite Hrn.
    exact Hm_restrict.
  - rewrite formula_fv_and in Hproj.
    destruct Hmodel as [Hp Hq]. split.
    + eapply IH; [| exact Hp].
      eapply res_restrict_eq_union_l. exact Hproj.
    + eapply IH; [| exact Hq].
      eapply res_restrict_eq_union_r. exact Hproj.
  - rewrite formula_fv_or in Hproj.
    destruct Hmodel as [Hp | Hq].
    + left. eapply IH; [| exact Hp].
      eapply res_restrict_eq_union_l. exact Hproj.
    + right. eapply IH; [| exact Hq].
      eapply res_restrict_eq_union_r. exact Hproj.
  - rewrite formula_fv_impl in Hproj.
    intros n' Hle_n Hpn'.
    assert (Hscope_n : formula_scoped_in_world n (FImpl p q)).
    {
      eapply formula_scoped_projection_on; [| exact Hproj | exact Hscope].
      rewrite formula_fv_impl. set_solver.
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
  - rewrite formula_fv_star in Hproj.
    destruct Hmodel as [m1 [m2 [Hc [Hprod [Hp Hq]]]]].
    set (X := formula_fv p ∪ formula_fv q).
    assert (HprojX : res_restrict m X = res_restrict n X).
    { subst X. exact Hproj. }
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
        by (subst X; set_solver).
      reflexivity.
    + eapply IH; [| exact Hq].
      rewrite res_restrict_restrict_eq.
      replace (X ∩ formula_fv q) with (formula_fv q)
        by (subst X; set_solver).
      reflexivity.
  - eapply res_models_fuel_projection_fbwand_case; eauto.
  - rewrite formula_fv_plus in Hproj.
    destruct Hmodel as [m1 [m2 [Hdef [Hsum [Hp Hq]]]]].
    set (X := formula_fv p ∪ formula_fv q).
    assert (HprojX : res_restrict m X = res_restrict n X).
    { subst X. exact Hproj. }
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
        by (subst X; set_solver).
      reflexivity.
    + eapply IH; [| exact Hq].
      rewrite res_restrict_restrict_eq.
      replace (X ∩ formula_fv q) with (formula_fv q)
        by (subst X; set_solver).
      reflexivity.
  - destruct Hmodel as [L Hforall].
    exists (L ∪ world_dom (m : WorldT)).
    intros y Hy F HFin HFout ny Hny.
    assert (Hproj_body :
        res_restrict m (formula_fv p) =
        res_restrict n (formula_fv p)).
    {
      rewrite formula_fv_forall, formula_lvars_at_fv in Hproj.
      exact Hproj.
    }
    assert (Happ_m : extension_applicable F m).
    {
      eapply extension_applicable_for_open.
      - eapply formula_scoped_forall_body. exact Hscope.
      - apply not_elem_of_union in Hy as [_ Hy_m].
        exact Hy_m.
      - exact HFin.
      - exact HFout.
    }
    destruct (res_extend_by_exists m F Happ_m) as [my Hmy].
    pose proof (Hforall y ltac:(set_solver) F HFin HFout my Hmy) as Hpmy.
    eapply IH; [| exact Hpmy].
    eapply res_extend_by_open_projection_eq
      with (F := F) (φ := p) (y := y); eauto.
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
  - destruct Hmodel as [σ [Hdomσ [Hrestrict Hp]]].
    exists σ. split; [exact Hdomσ|].
    split; [|exact Hp].
    change (res_restrict m (formula_fv p) =
      res_restrict n (formula_fv p)) in Hproj.
    rewrite <- Hproj. exact Hrestrict.
  - destruct Hmodel as [Hlc Hfib].
    split; [exact Hlc|].
    intros σ mfib Hfiber.
    rewrite formula_fv_fibvars in Hproj.
    set (X := lvars_fv D ∪ formula_fv p).
    assert (HprojX : res_restrict m X = res_restrict n X).
    { subst X. exact Hproj. }
    assert (HDm : lvars_fv D ⊆ world_dom (m : WorldT)).
    {
      rewrite formula_fv_fibvars in Hscope.
      set_solver.
    }
    destruct (res_fiber_from_projection_transport_on
      m n mfib σ (lvars_fv D) X ltac:(subst X; set_solver)
      HDm HprojX Hfiber) as [mfib_m [Hfiber_m Hmfib_proj]].
    pose proof (Hfib σ mfib_m Hfiber_m) as Hbody_m.
    eapply IH; [| exact Hbody_m].
    eapply res_restrict_eq_subset; [| exact Hmfib_proj].
    subst X.
    pose proof (formula_msubst_store_fv_subset σ p) as Hfv.
    set_solver.
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

Lemma res_models_true (m : WfWorldT) :
  res_models m FTrue.
Proof.
  unfold res_models. cbn.
  split.
  - rewrite formula_fv_true. set_solver.
  - trivial.
Qed.

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

Lemma res_models_projection (m n : WfWorldT) (φ : FormulaT) :
  res_restrict m (formula_fv φ) = res_restrict n (formula_fv φ) ->
  res_models m φ ->
  res_models n φ.
Proof.
  unfold res_models. apply res_models_fuel_projection.
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
  rewrite ?formula_open_env_preserves_measure;
  rewrite ?formula_open_preserves_measure;
  rewrite ?formula_mlsubst_preserves_measure;
  rewrite ?formula_msubst_store_preserves_measure;
  simpl; lia.

Tactic Notation "models_fuel_irrel" constr(H) :=
  eapply res_models_fuel_irrel; [| | exact H]; models_fuel_finish.

Ltac models_fuel_irrel_auto :=
  eapply res_models_fuel_irrel; [| | eassumption]; models_fuel_finish.
