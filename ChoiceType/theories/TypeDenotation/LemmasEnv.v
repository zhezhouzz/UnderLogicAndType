(** * ChoiceType.TypeDenotation.LemmasEnv

    Environment-opening and resource-domain helpers for type denotation. *)

From Stdlib Require Import Logic.FunctionalExtensionality
  Logic.PropExtensionality Lia.
From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps BasicTypingProps
  Sugar.
From ChoiceLogic Require Import FormulaDerived.
From ChoiceType Require Export TypeDenotation.LemmasSyntax.
From ChoiceType Require Import BasicStore BasicTyping LocallyNamelessProps
  TypeDenotation.FormulaEquiv.

Local Notation FQ := FormulaQ.

Lemma closed_resource_lvar_open k x η Σ m :
  closed_resource_lvar ({k ~> x} Σ) η m =
  closed_resource_lvar Σ (<[k := x]> η) m.
Proof.
  unfold closed_resource_lvar.
  change (dom ({k ~> x} Σ)) with (dom (lty_env_open_one k x Σ)).
  rewrite lty_env_open_one_dom.
  rewrite lvars_to_atoms_open.
  reflexivity.
Qed.

Lemma expr_total_lvar_open k x η Σ e ρ m :
  expr_total_lvar ({k ~> x} Σ) ({k ~> x} e) η ρ m =
  expr_total_lvar Σ e (<[k := x]> η) ρ m.
Proof.
  unfold expr_total_lvar.
  change (dom ({k ~> x} Σ)) with (dom (lty_env_open_one k x Σ)).
  rewrite lty_env_open_one_dom.
  rewrite tm_lvars_open.
  replace (lvars_open k x (dom Σ) ∪ lvars_open k x (tm_lvars e))
    with (lvars_open k x (dom Σ ∪ tm_lvars e)).
  2:{ unfold lvars_open. rewrite set_map_union_L. reflexivity. }
  rewrite <- lvars_to_atoms_open.
  change ({k ~> x} e) with (open_tm k (vfvar x) e).
  rewrite open_tm_env_open_tm.
  reflexivity.
Qed.

Lemma lty_env_open_lvars_empty Σ :
  lty_env_open_lvars ∅ Σ = Σ.
Proof.
  unfold lty_env_open_lvars.
  refine (fin_maps.map_fold_ind
    (fun Σ =>
      map_fold (fun v T acc => <[logic_var_open_env ∅ v := T]> acc)
        ∅ Σ = Σ) _ _ Σ).
  - rewrite map_fold_empty. reflexivity.
  - intros v T Σ' Hfresh Hfold IH.
    rewrite Hfold, IH.
    destruct v as [k|y]; cbn [logic_var_open_env].
    + rewrite lookup_empty. reflexivity.
    + reflexivity.
Qed.

Lemma logic_var_open_env_singleton k x v :
  logic_var_open_env (<[k := x]> ∅) v = logic_var_open k x v.
Proof.
  destruct v as [j|y]; cbn [logic_var_open_env logic_var_open].
  - destruct (decide (j = k)) as [->|Hjk].
    + rewrite lookup_insert_eq. reflexivity.
    + rewrite lookup_insert_ne by congruence.
      rewrite lookup_empty. reflexivity.
  - reflexivity.
Qed.

Lemma logic_var_open_env_open_one η k x v :
  logic_var_open_env η (logic_var_open k x v) =
  logic_var_open_env (<[k := x]> η) v.
Proof.
  destruct v as [j|y]; cbn [logic_var_open_env logic_var_open].
  - destruct (decide (j = k)) as [->|Hjk].
    + rewrite lookup_insert_eq. reflexivity.
    + rewrite lookup_insert_ne by congruence. reflexivity.
  - reflexivity.
Qed.

Lemma logic_var_open_env_empty v :
  logic_var_open_env ∅ v = v.
Proof.
  destruct v as [k|x]; cbn [logic_var_open_env].
  - rewrite lookup_empty. reflexivity.
  - reflexivity.
Qed.

Lemma logic_var_open_env_open_fresh η k x v :
  η !! k = None →
  logic_var_open_env η (logic_var_open k x v) =
  logic_var_open k x (logic_var_open_env η v).
Proof.
  intros Hη.
  destruct v as [j|y].
  - destruct (decide (j = k)) as [->|Hjk].
    + cbn [logic_var_open logic_var_open_env].
      rewrite Hη. cbn [logic_var_open].
      destruct (decide (k = k)) as [_|Hbad]; [reflexivity|congruence].
    + cbn [logic_var_open].
      destruct (decide (j = k)) as [Hbad|_]; [congruence|].
      cbn [logic_var_open_env].
      destruct (η !! j) as [z|] eqn:Hηj; cbn [logic_var_open].
      * reflexivity.
      * destruct (decide (j = k)) as [Hbad|_]; [congruence|reflexivity].
  - reflexivity.
Qed.

Lemma logic_var_open_env_insert_fresh η k x v :
  η !! k = None →
  logic_var_open_env (<[k := x]> η) v =
  logic_var_open k x (logic_var_open_env η v).
Proof.
  intros Hη.
  rewrite <- logic_var_open_env_open_fresh by exact Hη.
  symmetry. apply logic_var_open_env_open_one.
Qed.

Lemma lvars_open_env_simul_empty D :
  lvars_open_env_simul ∅ D = D.
Proof.
  unfold lvars_open_env_simul.
  induction D as [|v D Hfresh IH] using set_ind_L.
  - rewrite set_map_empty. reflexivity.
  - rewrite set_map_union_L, set_map_singleton_L, IH.
    rewrite logic_var_open_env_empty. reflexivity.
Qed.

Lemma lvars_open_env_simul_open_fresh η k x D :
  η !! k = None →
  lvars_open_env_simul η (lvars_open k x D) =
  lvars_open k x (lvars_open_env_simul η D).
Proof.
  intros Hη.
  unfold lvars_open_env_simul, lvars_open.
  apply set_eq. intros v.
  rewrite !elem_of_map.
  split.
  - intros [u [-> Hu]].
    apply elem_of_map in Hu as [w [-> Hw]].
    exists (logic_var_open_env η w). split.
    + rewrite logic_var_open_env_open_fresh by exact Hη. reflexivity.
    + apply elem_of_map. eauto.
  - intros [u [-> Hu]].
    apply elem_of_map in Hu as [w [-> Hw]].
    exists (logic_var_open k x w). split.
    + rewrite logic_var_open_env_open_fresh by exact Hη. reflexivity.
    + apply elem_of_map. eauto.
Qed.

Lemma lvars_open_env_simul_insert_fresh η k x D :
  η !! k = None →
  lvars_open_env_simul (<[k := x]> η) D =
  lvars_open k x (lvars_open_env_simul η D).
Proof.
  intros Hη.
  unfold lvars_open_env_simul, lvars_open.
  apply set_eq. intros v.
  rewrite !elem_of_map.
  split.
  - intros [u [-> Hu]].
    exists (logic_var_open_env η u). split.
    + rewrite logic_var_open_env_insert_fresh by exact Hη. reflexivity.
    + apply elem_of_map. eauto.
  - intros [u [-> Hu]].
    apply elem_of_map in Hu as [w [-> Hw]].
    exists w. split; [|exact Hw].
    rewrite logic_var_open_env_insert_fresh by exact Hη. reflexivity.
Qed.

Lemma lvars_open_env_simul_eq η D :
  lvars_open_env_simul η D = lvars_open_env η D.
Proof.
  unfold lvars_open_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      lvars_open_env_simul η D =
      map_fold (fun k x acc => lvars_open k x acc) D η) _ _ η).
  - rewrite map_fold_empty. apply lvars_open_env_simul_empty.
  - intros k x η' Hfresh Hfold IH.
    rewrite Hfold.
    rewrite lvars_open_env_simul_insert_fresh by exact Hfresh.
    rewrite IH. reflexivity.
Qed.

Lemma lvars_fv_mono (D E : lvset) :
  D ⊆ E →
  lvars_fv D ⊆ lvars_fv E.
Proof.
  intros HDE x Hx.
  apply lvars_fv_elem.
  apply lvars_fv_elem in Hx.
  exact (HDE _ Hx).
Qed.

Lemma lvars_open_mono k x (D E : lvset) :
  D ⊆ E →
  lvars_open k x D ⊆ lvars_open k x E.
Proof.
  intros HDE v Hv.
  unfold lvars_open in *.
  apply elem_of_map in Hv as [u [-> Hu]].
  apply elem_of_map. exists u. split; [reflexivity|].
  exact (HDE _ Hu).
Qed.

Lemma lvars_open_env_mono η (D E : lvset) :
  D ⊆ E →
  lvars_open_env η D ⊆ lvars_open_env η E.
Proof.
  unfold lvars_open_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      D ⊆ E →
      map_fold (fun k x acc => lvars_open k x acc) D η ⊆
      map_fold (fun k x acc => lvars_open k x acc) E η) _ _ η).
  - rewrite !map_fold_empty. auto.
  - intros k x η' Hfresh Hfold IH HDE.
    rewrite !Hfold.
    apply lvars_open_mono. apply IH. exact HDE.
Qed.

Lemma open_env_fresh_for_lvars_mono η (D E : lvset) :
  D ⊆ E →
  open_env_fresh_for_lvars η E →
  open_env_fresh_for_lvars η D.
Proof.
  intros HDE Hfresh k x Hkx Hbad.
  eapply Hfresh; [exact Hkx|].
  apply lvars_fv_mono with (D := lvars_open_env (delete k η) D).
  - apply lvars_open_env_mono. exact HDE.
  - exact Hbad.
Qed.

Definition logic_var_open_env_inj_on η (D : lvset) : Prop :=
  ∀ v1 v2,
    v1 ∈ D →
    v2 ∈ D →
    logic_var_open_env η v1 = logic_var_open_env η v2 →
    v1 = v2.

Lemma map_delete_lookup_none `{Countable K} {A} (m : gmap K A) k :
  m !! k = None →
  delete k m = m.
Proof.
  intros Hnone. apply map_eq. intros j.
  destruct (decide (j = k)) as [->|Hjk].
  - rewrite lookup_delete_eq. symmetry. exact Hnone.
  - rewrite lookup_delete_ne by congruence. reflexivity.
Qed.

Lemma lvars_fv_open_env_lookup η D k x :
  η !! k = Some x →
  LVBound k ∈ D →
  x ∈ lvars_fv (lvars_open_env η D).
Proof.
  intros Hη Hk.
  rewrite <- lvars_open_env_simul_eq.
  apply lvars_fv_elem.
  unfold lvars_open_env_simul.
  apply elem_of_map.
  exists (LVBound k). split; [|exact Hk].
  cbn [logic_var_open_env]. rewrite Hη. reflexivity.
Qed.

Lemma lvars_fv_open_env_free η D x :
  LVFree x ∈ D →
  x ∈ lvars_fv (lvars_open_env η D).
Proof.
  intros Hx.
  rewrite <- lvars_open_env_simul_eq.
  apply lvars_fv_elem.
  unfold lvars_open_env_simul.
  apply elem_of_map.
  exists (LVFree x). split; [reflexivity|exact Hx].
Qed.

Lemma open_env_fresh_for_lvars_inj_on η D :
  open_env_fresh_for_lvars η D →
  logic_var_open_env_inj_on η D.
Proof.
  intros Hfresh v1 v2 Hv1 Hv2 Heq.
  destruct v1 as [k1|x1], v2 as [k2|x2];
    cbn [logic_var_open_env] in Heq.
  - destruct (η !! k1) as [x1|] eqn:Hη1;
      destruct (η !! k2) as [x2|] eqn:Hη2.
    + inversion Heq. subst x2.
      destruct (decide (k1 = k2)) as [->|Hne]; [reflexivity|].
      exfalso.
      eapply Hfresh; [exact Hη1|].
      apply lvars_fv_open_env_lookup with (k := k2); [|exact Hv2].
      rewrite lookup_delete_ne by congruence. exact Hη2.
    + discriminate.
    + discriminate.
    + inversion Heq. subst k2. reflexivity.
  - destruct (η !! k1) as [x|] eqn:Hη1; inversion Heq; subst.
    exfalso.
    eapply Hfresh; [exact Hη1|].
    apply lvars_fv_open_env_free. exact Hv2.
  - destruct (η !! k2) as [x|] eqn:Hη2; inversion Heq; subst.
    exfalso.
    eapply Hfresh; [exact Hη2|].
    apply lvars_fv_open_env_free. exact Hv1.
  - inversion Heq. subst x2. reflexivity.
Qed.

Lemma logic_var_open_env_not_free η D k x v :
  η !! k = None →
  x ∉ lvars_fv (lvars_open_env η D) →
  v ∈ D →
  logic_var_open_env η v ≠ LVFree x.
Proof.
  intros Hη Hx Hv Heq.
  apply Hx.
  rewrite <- lvars_open_env_simul_eq.
  apply lvars_fv_elem.
  unfold lvars_open_env_simul.
  apply elem_of_map.
  exists v. split; [symmetry; exact Heq|exact Hv].
Qed.

Lemma logic_var_open_env_inj_on_insert_fresh η k x D :
  η !! k = None →
  x ∉ lvars_fv (lvars_open_env η D) →
  open_env_fresh_for_lvars η D →
  logic_var_open_env_inj_on (<[k := x]> η) D.
Proof.
  intros Hη Hx Hfresh v1 v2 Hv1 Hv2 Heq.
  rewrite !logic_var_open_env_insert_fresh in Heq by exact Hη.
  apply logic_var_open_inj_fresh in Heq.
  - eapply open_env_fresh_for_lvars_inj_on; eauto.
  - eapply logic_var_open_env_not_free; eauto.
  - eapply logic_var_open_env_not_free; eauto.
Qed.

Lemma lty_env_open_lvars_singleton k x Σ :
  lty_env_open_lvars (<[k := x]> ∅) Σ = lty_env_open_one k x Σ.
Proof.
  unfold lty_env_open_lvars, lty_env_open_one.
  refine (fin_maps.map_fold_ind
    (fun Σ =>
      map_fold
        (fun v T acc => <[logic_var_open_env (<[k := x]> ∅) v := T]> acc)
        ∅ Σ =
      map_fold (fun v T acc => <[logic_var_open k x v := T]> acc)
        ∅ Σ) _ _ Σ).
  - rewrite !map_fold_empty. reflexivity.
  - intros v T Σ' Hfresh Hfold IH.
    rewrite !Hfold, IH.
    rewrite logic_var_open_env_singleton. reflexivity.
Qed.

Lemma lty_env_open_lvars_open_one_empty k x Σ :
  lty_env_open_lvars ∅ (lty_env_open_one k x Σ) =
  lty_env_open_lvars (<[k := x]> ∅) Σ.
Proof.
  rewrite lty_env_open_lvars_empty.
  symmetry. apply lty_env_open_lvars_singleton.
Qed.

Lemma lty_env_open_typed_bind_atom_env (Δ : gmap atom ty) T x :
  x ∉ dom Δ →
  {0 ~> x} (typed_lty_env_bind (atom_env_to_lty_env Δ) T) =
    atom_env_to_lty_env (<[x := T]> Δ).
Proof.
  intros Hx.
  unfold typed_lty_env_bind.
  apply lty_env_open_one_bind_atom_env.
  exact Hx.
Qed.

Lemma typed_lty_env_bind_dom Σ T :
  dom (typed_lty_env_bind Σ T) = lvars_shift (dom Σ) ∪ {[LVBound 0]}.
Proof.
  unfold typed_lty_env_bind.
  change (dom (<[LVBound 0 := T]> (lty_env_shift Σ) : lty_env) =
    lvars_shift (dom Σ) ∪ {[LVBound 0]}).
  transitivity ({[LVBound 0]} ∪ dom (lty_env_shift Σ)).
  { apply dom_insert_L. }
  pose proof (dom_kmap_L (Inj0:=logic_var_shift_inj)
    logic_var_shift Σ) as Hshift.
  unfold lty_env_shift in Hshift.
  set_solver.
Qed.

Lemma typed_lty_env_bind_atom_env_insert_dom
    (Δ : gmap atom ty) x Tx Ty :
  x ∉ dom Δ →
  dom (typed_lty_env_bind (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty) =
    dom (typed_lty_env_bind (atom_env_to_lty_env Δ) Ty) ∪
      {[LVFree x]}.
Proof.
  intros Hx.
  rewrite !typed_lty_env_bind_dom.
  rewrite !atom_env_to_lty_env_dom.
  rewrite dom_insert_L.
  rewrite !lvars_shift_of_atoms.
  unfold lvars_of_atoms.
  apply set_eq. intros [n|a].
  - rewrite !elem_of_union, !elem_of_singleton, !elem_of_map.
    split; intros H; set_solver.
  - rewrite !elem_of_union, !elem_of_singleton, !elem_of_map.
    split.
    + intros [[b [Hb HbΔ]] | Hbound].
      * inversion Hb; subst b. set_solver.
      * discriminate.
    + intros [[[b [Hb HbΔ]] | Hbound] | Hxv].
      * inversion Hb; subst b. left. exists a. split; [reflexivity | set_solver].
      * discriminate.
      * inversion Hxv; subst a. left. exists x. split; [reflexivity | set_solver].
Qed.

Lemma lty_env_shift_from_lvars_fv_dom k Σ :
  lvars_fv (dom (↑[k] Σ)) = lvars_fv (dom Σ).
Proof.
  unfold shift_at, shift_lty_env_inst, lty_env_shift_from.
  apply set_eq. intros x.
  rewrite !lvars_fv_elem.
  split.
  - intros Hx.
    apply elem_of_dom in Hx as [T Hlookup].
    apply lookup_kmap_Some in Hlookup as [v [Hv Hlookup]].
    2:{ unfold shift_at, shift_logic_var_inst.
        apply logic_var_shift_from_inj. }
    destruct v as [n|y]; cbn [shift_at shift_logic_var_inst logic_var_shift_from] in Hv.
    + destruct (decide (k <= n)); inversion Hv.
    + inversion Hv. subst.
      apply elem_of_dom. exists T. exact Hlookup.
  - intros Hx.
    apply elem_of_dom in Hx as [T Hlookup].
    apply elem_of_dom.
    exists T.
    change (LVFree x) with ((shift_at k : logic_var -> logic_var) (LVFree x)).
    change ((kmap (shift_at k : logic_var -> logic_var) Σ : lty_env) !!
      (shift_at k : logic_var -> logic_var) (LVFree x) =
      Some T).
    transitivity (Σ !! LVFree x).
    + eapply lookup_kmap.
      unfold shift_at, shift_logic_var_inst.
      apply logic_var_shift_from_inj.
    + exact Hlookup.
Qed.

Lemma typed_lty_env_bind_lvars_fv_dom Σ T :
  lvars_fv (dom (typed_lty_env_bind Σ T)) = lvars_fv (dom Σ).
Proof.
  unfold typed_lty_env_bind.
  apply set_eq. intros x.
  rewrite !lvars_fv_elem.
  split.
  - intros Hx.
    change (LVFree x ∈ dom (<[LVBound 0 := T]> (↑[0] Σ) : lty_env)) in Hx.
    apply elem_of_dom in Hx as Hsome.
    rewrite lookup_insert_is_Some' in Hsome.
    destruct Hsome as [Hbad|Hsome]; [inversion Hbad |].
    apply lvars_fv_elem.
    rewrite <- (lty_env_shift_from_lvars_fv_dom 0 Σ).
    apply lvars_fv_elem.
    apply elem_of_dom. exact Hsome.
  - intros Hx.
    change (LVFree x ∈ dom (<[LVBound 0 := T]> (↑[0] Σ) : lty_env)).
    apply elem_of_dom.
    rewrite lookup_insert_is_Some'.
    right.
    apply elem_of_dom.
    apply lvars_fv_elem.
    rewrite lty_env_shift_from_lvars_fv_dom.
    apply lvars_fv_elem. exact Hx.
Qed.

Lemma lty_env_open_lvars_dom η Σ :
  dom (lty_env_open_lvars η Σ) = lvars_open_env_simul η (dom Σ).
Proof.
  unfold lty_env_open_lvars, lvars_open_env_simul.
  refine (fin_maps.map_fold_ind
    (fun Σ =>
      dom (map_fold
        (fun v T acc => <[logic_var_open_env η v := T]> acc) ∅ Σ) =
      set_map (logic_var_open_env η) (dom Σ)) _ _ Σ).
  - rewrite map_fold_empty, dom_empty_L, set_map_empty. reflexivity.
  - intros v T Σ' Hfresh Hfold IH.
    rewrite Hfold.
    rewrite (dom_insert_L
      (map_fold
        (fun v0 T0 (acc : lty_env) => <[logic_var_open_env η v0 := T0]> acc)
        ∅ Σ') (logic_var_open_env η v) T).
    replace (dom (map_fold
        (fun v0 T0 (acc : lty_env) => <[logic_var_open_env η v0 := T0]> acc)
        ∅ Σ'))
      with (set_map (C:=lvset) (D:=lvset)
        (logic_var_open_env η) (dom Σ')) by (symmetry; exact IH).
    rewrite dom_insert_L.
    change ({[v]} ∪ dom Σ') with (({[v]} : lvset) ∪ dom Σ').
    rewrite set_map_union_L, set_map_singleton_L.
    reflexivity.
Qed.

Lemma lty_env_open_lvars_lookup_fresh η v T Σ :
  Σ !! v = None →
  open_env_fresh_for_lvars η (dom (<[v := T]> Σ)) →
  lty_env_open_lvars η Σ !! logic_var_open_env η v = None.
Proof.
  intros Hlookup Hfresh.
  apply not_elem_of_dom.
  rewrite lty_env_open_lvars_dom.
  intros Hbad.
  unfold lvars_open_env_simul in Hbad.
  apply elem_of_map in Hbad as [u [Hu HuΣ]].
  assert (Hinj : logic_var_open_env_inj_on η (dom (<[v := T]> Σ))).
  { apply open_env_fresh_for_lvars_inj_on. exact Hfresh. }
  assert (Hv : v ∈ dom (<[v := T]> Σ)).
  { apply elem_of_dom. exists T. apply lookup_insert_eq. }
  assert (Hu' : u ∈ dom (<[v := T]> Σ)).
  {
    set_solver.
  }
  specialize (Hinj u v Hu' Hv (eq_sym Hu)). subst u.
  apply not_elem_of_dom in Hlookup. contradiction.
Qed.

Lemma lty_env_open_lvars_insert_entry η v T Σ :
  Σ !! v = None →
  logic_var_open_env_inj_on η (dom (<[v := T]> Σ)) →
  lty_env_open_lvars η (<[v := T]> Σ) =
  <[logic_var_open_env η v := T]> (lty_env_open_lvars η Σ).
Proof.
  intros Hlookup Hinj.
  unfold lty_env_open_lvars.
  refine (map_fold_insert_L
    (fun (v : logic_var) (T : ty) (acc : lty_env) =>
      <[logic_var_open_env η v := T]> acc)
    (∅ : lty_env) v T Σ _ Hlookup).
  intros v1 v2 T1 T2 acc Hne Hlookup1 Hlookup2.
  assert (Hv1 : v1 ∈ dom (<[v := T]> Σ)).
  {
    apply elem_of_dom_2 in Hlookup1. set_solver.
  }
  assert (Hv2 : v2 ∈ dom (<[v := T]> Σ)).
  {
    apply elem_of_dom_2 in Hlookup2. set_solver.
  }
  assert (Hopen_ne : logic_var_open_env η v1 ≠ logic_var_open_env η v2).
  { intros Heq. apply Hne. eapply Hinj; eauto. }
  apply insert_insert_ne. exact Hopen_ne.
Qed.

Lemma logic_var_to_atom_empty_open_env η v :
  logic_var_to_atom ∅ (logic_var_open_env η v) =
  logic_var_to_atom η v.
Proof.
  destruct v as [k|x]; cbn [logic_var_open_env logic_var_to_atom].
  - destruct (η !! k); reflexivity.
  - reflexivity.
Qed.

Lemma lvars_to_atoms_open_env_simul η D :
  lvars_to_atoms ∅ (lvars_open_env_simul η D) =
  lvars_to_atoms η D.
Proof.
  apply set_eq. intros x.
  rewrite !lvars_to_atoms_elem.
  unfold lvars_open_env_simul.
  split.
  - intros [v [Hv Hatom]].
    apply elem_of_map in Hv as [u [-> Hu]].
    exists u. split; [exact Hu|].
    rewrite <- logic_var_to_atom_empty_open_env. exact Hatom.
  - intros [v [Hv Hatom]].
    exists (logic_var_open_env η v). split.
    + apply elem_of_map. eauto.
    + rewrite logic_var_to_atom_empty_open_env. exact Hatom.
Qed.

Lemma lvars_to_atoms_union η D E :
  lvars_to_atoms η (D ∪ E) =
  lvars_to_atoms η D ∪ lvars_to_atoms η E.
Proof.
  apply set_eq. intros x.
  rewrite !lvars_to_atoms_elem.
  split.
  - intros [v [Hv Hatom]].
    apply elem_of_union in Hv as [Hv|Hv].
    + apply elem_of_union. left.
      apply lvars_to_atoms_elem. eauto.
    + apply elem_of_union. right.
      apply lvars_to_atoms_elem. eauto.
  - intros Hx.
    apply elem_of_union in Hx as [Hx|Hx].
    + apply lvars_to_atoms_elem in Hx as [v [Hv Hatom]].
      exists v; split; [set_solver|exact Hatom].
    + apply lvars_to_atoms_elem in Hx as [v [Hv Hatom]].
      exists v; split; [set_solver|exact Hatom].
Qed.

Lemma lvars_to_atoms_open_env_simul_union η D E :
  lvars_to_atoms ∅ (lvars_open_env_simul η D ∪ lvars_open_env η E) =
  lvars_to_atoms η (D ∪ E).
Proof.
  rewrite !lvars_to_atoms_union.
  rewrite lvars_to_atoms_open_env_simul.
  rewrite lvars_to_atoms_open_env.
  rewrite open_env_precompose_empty_r.
  reflexivity.
Qed.

Lemma closed_resource_lvar_open_env_empty η Σ m :
  closed_resource_lvar (lty_env_open_lvars η Σ) ∅ m =
  closed_resource_lvar Σ η m.
Proof.
  unfold closed_resource_lvar.
  rewrite lty_env_open_lvars_dom.
  rewrite lvars_to_atoms_open_env_simul.
  reflexivity.
Qed.

Lemma expr_total_lvar_open_env_empty η Σ e ρ m :
  expr_total_lvar (lty_env_open_lvars η Σ) (open_tm_env η e) ∅ ρ m =
  expr_total_lvar Σ e η ρ m.
Proof.
  unfold expr_total_lvar.
  rewrite lty_env_open_lvars_dom.
  rewrite tm_lvars_open_env.
  rewrite lvars_to_atoms_open_env_simul_union.
  rewrite open_tm_env_empty.
  reflexivity.
Qed.

Lemma lvars_open_env_bv_notin η k D :
  k ∉ lvars_bv D →
  k ∉ lvars_bv (lvars_open_env η D).
Proof.
  unfold lvars_open_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      k ∉ lvars_bv D →
      k ∉ lvars_bv
        (map_fold (fun j x acc => lvars_open j x acc) D η)) _ _ η).
  - rewrite map_fold_empty. auto.
  - intros j x η' Hfresh Hfold IH Hnot.
    rewrite Hfold.
    rewrite lvars_bv_open.
    set_solver.
Qed.

Lemma lvars_open_env_simul_bv_notin η k D :
  k ∉ lvars_bv D →
  k ∉ lvars_bv (lvars_open_env_simul η D).
Proof.
  rewrite !lvars_bv_elem.
  unfold lvars_open_env_simul.
  intros Hnot Hbad.
  apply elem_of_map in Hbad as [v [Hv HvD]].
  destruct v as [j|y]; cbn [logic_var_open_env] in Hv.
  - destruct (η !! j) as [z|] eqn:Hηj.
    + discriminate.
    + inversion Hv. subst j. contradiction.
  - discriminate.
Qed.

Lemma lvars_fv_open_env_simul η D :
  lvars_fv (lvars_open_env_simul η D) =
  lvars_fv (lvars_open_env η D).
Proof.
  rewrite lvars_open_env_simul_eq. reflexivity.
Qed.

Lemma lty_env_open_lvars_no_bv η k x Σ :
  k ∉ lvars_bv (dom Σ) →
  lty_env_open_one k x (lty_env_open_lvars η Σ) =
  lty_env_open_lvars η Σ.
Proof.
  intros Hnot.
  apply lty_env_open_one_no_bv.
  rewrite lty_env_open_lvars_dom.
  apply lvars_open_env_simul_bv_notin. exact Hnot.
Qed.

Lemma lvars_open_same_index_absorb k x y D :
  lvars_open k y (lvars_open k x D) = lvars_open k x D.
Proof.
  apply lvars_open_no_bv.
  rewrite lvars_bv_open. set_solver.
Qed.

Lemma lvars_open_env_open_fresh η k x D :
  η !! k = None →
  lvars_open_env η (lvars_open k x D) =
  lvars_open k x (lvars_open_env η D).
Proof.
  intros Hη.
  unfold lvars_open_env.
  revert Hη.
  refine (fin_maps.map_fold_ind
    (fun η =>
      η !! k = None →
      map_fold (fun j y acc => lvars_open j y acc) (lvars_open k x D) η =
      lvars_open k x
        (map_fold (fun j y acc => lvars_open j y acc) D η)) _ _ η).
  - intros _. rewrite !map_fold_empty. reflexivity.
  - intros j y η' Hfresh Hfold IH Hη.
    rewrite !Hfold.
    assert (Hjk : j ≠ k).
    {
      intros ->.
      rewrite lookup_insert in Hη.
      destruct (decide (k = k)); congruence.
    }
    assert (Hη' : η' !! k = None).
    {
      rewrite lookup_insert_ne in Hη by congruence.
      exact Hη.
    }
    rewrite IH by exact Hη'.
    apply lvars_open_commute_fvar. congruence.
Qed.

Lemma lvars_open_env_open_one η k x D :
  lvars_open_env η (lvars_open k x D) =
  lvars_open_env (<[k := x]> η) D.
Proof.
  destruct (η !! k) as [y|] eqn:Hηk.
  - rewrite <-(insert_delete_id η k y Hηk) at 1.
    rewrite lvars_open_env_insert_fresh by apply lookup_delete_eq.
    rewrite lvars_open_env_open_fresh by apply lookup_delete_eq.
    rewrite lvars_open_same_index_absorb.
    replace (<[k:=x]> η) with (<[k:=x]> (delete k η)).
    2:{
      apply map_eq. intro j.
      destruct (decide (j = k)) as [->|Hjk].
      - rewrite !lookup_insert. destruct (decide (k = k)); congruence.
      - rewrite !lookup_insert_ne by congruence.
        rewrite lookup_delete_ne by congruence. reflexivity.
    }
    rewrite lvars_open_env_insert_fresh.
    + reflexivity.
    + apply lookup_delete_eq.
  - rewrite lvars_open_env_open_fresh by exact Hηk.
    symmetry. apply lvars_open_env_insert_fresh. exact Hηk.
Qed.

Lemma lvars_open_env_simul_open_one η k x D :
  lvars_open_env_simul η (lvars_open k x D) =
  lvars_open_env_simul (<[k := x]> η) D.
Proof.
  unfold lvars_open_env_simul, lvars_open.
  apply set_eq. intros v.
  rewrite !elem_of_map.
  split.
  - intros [u [-> Hu]].
    apply elem_of_map in Hu as [w [-> Hw]].
    exists w. split; [|exact Hw].
    apply logic_var_open_env_open_one.
  - intros [u [-> Hu]].
    exists (logic_var_open k x u). split.
    + rewrite logic_var_open_env_open_one. reflexivity.
    + apply elem_of_map. eauto.
Qed.

Lemma lty_env_open_lvars_open_one_dom η k x Σ :
  dom (lty_env_open_lvars η (lty_env_open_one k x Σ)) =
  dom (lty_env_open_lvars (<[k := x]> η) Σ).
Proof.
  rewrite !lty_env_open_lvars_dom.
  rewrite lty_env_open_one_dom.
  apply lvars_open_env_simul_open_one.
Qed.

Lemma lty_env_open_one_free_notin_other k y x Σ :
  x ≠ y →
  LVFree x ∉ dom Σ →
  LVFree x ∉ dom (lty_env_open_one k y Σ).
Proof.
  intros Hxy Hfresh.
  rewrite lty_env_open_one_dom.
  intros Hbad.
  unfold lvars_open in Hbad.
  apply elem_of_map in Hbad as [v [Hv HvΣ]].
  destruct v as [j|z]; cbn [logic_var_open] in Hv.
  - destruct (decide (j = k)) as [_|_]; inversion Hv; subst.
    congruence.
  - inversion Hv. subst. contradiction.
Qed.

Lemma lty_env_open_one_lookup_fresh k x v T Σ :
  Σ !! v = None →
  LVFree x ∉ dom (<[v := T]> Σ) →
  lty_env_open_one k x Σ !! logic_var_open k x v = None.
Proof.
  intros Hlookup Hfresh.
  apply not_elem_of_dom.
  rewrite lty_env_open_one_dom.
  intros Hbad.
  unfold lvars_open in Hbad.
  apply elem_of_map in Hbad as [u [Hu HuΣ]].
  apply logic_var_open_inj_fresh in Hu.
  - subst u. apply not_elem_of_dom in Hlookup. contradiction.
  - intros ->. apply Hfresh. apply elem_of_dom. exists T. apply lookup_insert_eq.
  - intros ->. apply Hfresh. set_solver.
Qed.

Lemma lty_env_open_one_commute_fresh i j x y Σ :
  i ≠ j →
  x ≠ y →
  LVFree x ∉ dom Σ →
  LVFree y ∉ dom Σ →
  lty_env_open_one i x (lty_env_open_one j y Σ) =
  lty_env_open_one j y (lty_env_open_one i x Σ).
Proof.
  intros Hij Hxy Hx Hy.
  induction Σ as [|v T Σ Hlookup IH] using map_ind.
  - reflexivity.
  - assert (Hjx :
      lty_env_open_one j y (<[v := T]> Σ) =
      <[logic_var_open j y v := T]> (lty_env_open_one j y Σ)).
    { apply lty_env_open_one_insert_fresh; [exact Hlookup | set_solver]. }
    assert (Hix :
      lty_env_open_one i x (<[v := T]> Σ) =
      <[logic_var_open i x v := T]> (lty_env_open_one i x Σ)).
    { apply lty_env_open_one_insert_fresh; [exact Hlookup | set_solver]. }
    rewrite Hjx, Hix.
    assert (Hleft :
      lty_env_open_one i x
        (<[logic_var_open j y v := T]> (lty_env_open_one j y Σ)) =
      <[logic_var_open i x (logic_var_open j y v) := T]>
        (lty_env_open_one i x (lty_env_open_one j y Σ))).
    {
      apply lty_env_open_one_insert_fresh.
      - apply lty_env_open_one_lookup_fresh with (T:=T);
          [exact Hlookup | set_solver].
      - intros Hbad.
        apply elem_of_dom in Hbad as [U Hbad].
        apply lookup_insert_Some in Hbad as [[Hbad _]|[Hne Hbad]].
        + destruct v as [n|z]; cbn [logic_var_open] in Hbad.
          * destruct (decide (n = j)) as [->|Hnj].
            -- inversion Hbad. subst. congruence.
            -- discriminate.
          * inversion Hbad. subst z.
            apply Hx. apply elem_of_dom. exists T. apply lookup_insert_eq.
        + apply (lty_env_open_one_free_notin_other j y x Σ).
          * congruence.
          * set_solver.
          * apply elem_of_dom. exists U. exact Hbad.
    }
    assert (Hright :
      lty_env_open_one j y
        (<[logic_var_open i x v := T]> (lty_env_open_one i x Σ)) =
      <[logic_var_open j y (logic_var_open i x v) := T]>
        (lty_env_open_one j y (lty_env_open_one i x Σ))).
    {
      apply lty_env_open_one_insert_fresh.
      - apply lty_env_open_one_lookup_fresh with (T:=T);
          [exact Hlookup | set_solver].
      - intros Hbad.
        apply elem_of_dom in Hbad as [U Hbad].
        apply lookup_insert_Some in Hbad as [[Hbad _]|[Hne Hbad]].
        + destruct v as [n|z]; cbn [logic_var_open] in Hbad.
          * destruct (decide (n = i)) as [->|Hni].
            -- inversion Hbad. subst. congruence.
            -- discriminate.
          * inversion Hbad. subst z.
            apply Hy. apply elem_of_dom. exists T. apply lookup_insert_eq.
        + apply (lty_env_open_one_free_notin_other i x y Σ).
          * congruence.
          * set_solver.
          * apply elem_of_dom. exists U. exact Hbad.
    }
    rewrite Hleft, Hright.
    rewrite logic_var_open_commute_fvar by exact Hij.
    rewrite IH by set_solver.
    reflexivity.
Qed.

Lemma lty_env_open_lvars_insert_fresh η k x Σ :
  η !! k = None →
  x ∉ lvars_fv (lvars_open_env η (dom Σ)) →
  open_env_fresh_for_lvars η (dom Σ) →
  lty_env_open_lvars (<[k := x]> η) Σ =
  lty_env_open_one k x (lty_env_open_lvars η Σ).
Proof.
  intros Hη Hx Hfresh.
  induction Σ as [|v T Σ Hlookup IH] using map_ind.
  - reflexivity.
  - assert (Hinj_insert :
      logic_var_open_env_inj_on (<[k := x]> η) (dom (<[v := T]> Σ))).
    { eapply logic_var_open_env_inj_on_insert_fresh; eauto. }
    assert (Hinj :
      logic_var_open_env_inj_on η (dom (<[v := T]> Σ))).
    { apply open_env_fresh_for_lvars_inj_on. exact Hfresh. }
    assert (Hfresh_tail : open_env_fresh_for_lvars η (dom Σ)).
    { eapply open_env_fresh_for_lvars_mono; [|exact Hfresh]. set_solver. }
    assert (Hx_tail : x ∉ lvars_fv (lvars_open_env η (dom Σ))).
    {
      intros Hbad. apply Hx.
      apply lvars_fv_mono with (D := lvars_open_env η (dom Σ)).
      - apply lvars_open_env_mono. set_solver.
      - exact Hbad.
    }
    replace (lty_env_open_lvars (<[k := x]> η) (<[v := T]> Σ))
      with (<[logic_var_open_env (<[k := x]> η) v := T]>
        (lty_env_open_lvars (<[k := x]> η) Σ)).
    2:{
      symmetry. apply lty_env_open_lvars_insert_entry;
        [exact Hlookup|exact Hinj_insert].
    }
    replace (lty_env_open_lvars η (<[v := T]> Σ))
      with (<[logic_var_open_env η v := T]> (lty_env_open_lvars η Σ)).
    2:{
      symmetry. apply lty_env_open_lvars_insert_entry;
        [exact Hlookup|exact Hinj].
    }
    rewrite logic_var_open_env_insert_fresh by exact Hη.
    rewrite IH by assumption.
    rewrite lty_env_open_one_insert_fresh.
    + reflexivity.
    + apply lty_env_open_lvars_lookup_fresh with (T := T).
      * exact Hlookup.
      * exact Hfresh.
    + intros Hbad.
      apply elem_of_dom in Hbad as [U Hbad].
      apply lookup_insert_Some in Hbad as [[Hbad _]|[Hne Hbad]].
      * inversion Hbad. subst.
        eapply (logic_var_open_env_not_free
          η (dom (<[v := T]> Σ)) k x v); eauto.
        apply elem_of_dom. exists T. apply lookup_insert_eq.
      * apply Hx_tail.
        rewrite <- lvars_open_env_simul_eq.
        apply lvars_fv_elem.
        rewrite <- lty_env_open_lvars_dom.
        apply elem_of_dom. exists U. exact Hbad.
Qed.
