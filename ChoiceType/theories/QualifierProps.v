(** * ChoiceType.QualifierProps

    Lemmas about shallow type qualifiers.  The definitions live in
    [Qualifier.v]; proof-oriented facts are kept here so the core syntax layer
    stays light. *)

From ChoiceType Require Export Qualifier.
From LocallyNameless Require Import Classes.
From Stdlib Require Import Classes.RelationClasses Classes.Morphisms.

Lemma qual_open_atom_dom_subset k x q :
  qual_dom (qual_open_atom k x q) ⊆ qual_dom q ∪ {[x]}.
Proof.
  destruct q as [D p]. unfold qual_open_atom, qual_dom, qual_bvars.
  destruct decide; simpl.
  - pose proof (lvars_fv_open_subset k x D). set_solver.
  - set_solver.
Qed.

Lemma lvars_bv_elem D k :
  k ∈ lvars_bv D ↔ LVBound k ∈ D.
Proof.
  unfold lvars_bv.
  refine (set_fold_ind_L
    (fun acc D => ∀ k, k ∈ acc ↔ LVBound k ∈ D)
    (fun v acc => logic_var_bv v ∪ acc) ∅ _ _ D k).
  - intros j. set_solver.
  - intros v D' acc Hfresh IH j.
    pose proof (IH j) as IHj.
    destruct v as [i|y]; cbn [logic_var_bv].
    + split.
      * intros Hj.
        apply elem_of_union in Hj as [Hj|Hj].
        -- apply elem_of_singleton in Hj. subst j. set_solver.
        -- apply IHj in Hj. set_solver.
      * intros Hj.
        apply elem_of_union in Hj as [Hj|Hj].
        -- apply elem_of_singleton in Hj. inversion Hj. subst j.
           apply elem_of_union. left. set_solver.
        -- apply elem_of_union. right. apply IHj. exact Hj.
    + split.
      * intros Hj.
        apply elem_of_union in Hj as [Hempty|Hj].
        -- set_solver.
        -- apply IHj in Hj. set_solver.
      * intros Hj.
        apply elem_of_union in Hj as [Hj|Hj].
        -- apply elem_of_singleton in Hj. discriminate.
        -- apply elem_of_union. right. apply IHj. exact Hj.
Qed.

Lemma lvars_open_no_bv k x D :
  k ∉ lvars_bv D →
  lvars_open k x D = D.
Proof.
  intros Hnot.
  apply set_eq. intros v.
  split.
  - intros Hv.
    unfold lvars_open in Hv.
    apply elem_of_map in Hv as [u [-> Hu]].
    destruct u as [j|y]; cbn [logic_var_open].
    + destruct (decide (j = k)) as [->|Hjk].
      * exfalso. apply Hnot. apply lvars_bv_elem. exact Hu.
      * exact Hu.
    + exact Hu.
  - intros Hv.
    unfold lvars_open.
    apply elem_of_map.
    exists v. split; [| exact Hv].
    destruct v as [j|y]; cbn [logic_var_open].
    + destruct (decide (j = k)) as [->|Hjk].
      * exfalso. apply Hnot. apply lvars_bv_elem. exact Hv.
      * reflexivity.
    + reflexivity.
Qed.

Lemma lvars_bv_open k x D :
  lvars_bv (lvars_open k x D) = lvars_bv D ∖ {[k]}.
Proof.
  apply set_eq. intros j.
  rewrite lvars_bv_elem.
  split.
  - intros Hj.
    unfold lvars_open in Hj.
    apply elem_of_map in Hj as [v [Hvopen HvD]].
    destruct v as [i|y]; cbn [logic_var_open] in Hvopen.
    + destruct (decide (i = k)) as [->|Hik].
      * congruence.
      * inversion Hvopen. subst j.
        apply elem_of_difference. split.
        -- apply lvars_bv_elem. exact HvD.
        -- set_solver.
    + congruence.
  - intros Hj.
    apply elem_of_difference in Hj as [HjD Hjk].
    apply lvars_bv_elem in HjD.
    unfold lvars_open.
    apply elem_of_map.
    exists (LVBound j). split; [| exact HjD].
    cbn [logic_var_open].
    destruct (decide (j = k)) as [->|Hne]; [set_solver | reflexivity].
Qed.

Lemma qual_vars_open_atom k x q :
  qual_vars (qual_open_atom k x q) =
  lvars_open k x (qual_vars q).
Proof.
  destruct q as [D p]. unfold qual_open_atom, qual_vars, qual_bvars.
  destruct (decide (k ∈ lvars_bv D)) as [Hin|Hnot]; simpl.
  - reflexivity.
  - symmetry. apply lvars_open_no_bv. exact Hnot.
Qed.

(** ** Key interpretation lemmas *)

Lemma qual_interp_and q1 q2 σ :
  qual_interp σ (q1 &q q2) ↔ qual_interp σ q1 ∧ qual_interp σ q2.
Proof.
  destruct q1 as [D1 p1], q2 as [D2 p2].
  unfold qual_interp, qual_interp_full, qual_and.
  rewrite !map_restrict_restrict.
  rewrite !store_restrict_restrict.
  rewrite !lvars_fv_union.
  replace ((lvars_fv D1 ∪ lvars_fv D2) ∩ lvars_fv D1) with
    (lvars_fv D1) by set_solver.
  replace ((lvars_fv D1 ∪ lvars_fv D2) ∩ lvars_fv D2) with
    (lvars_fv D2) by set_solver.
  repeat match goal with
  | |- context[map_restrict value ∅ ?X] =>
      rewrite (map_restrict_idemp (∅ : gmap nat value) X) by set_solver
  end.
  reflexivity.
Qed.

Lemma qual_interp_open_eq_const x c σ :
  qual_interp σ (qual_open_atom 0 x (mk_q_eq (vbvar 0) (vconst c))) ↔
  σ !! x = Some (vconst c).
Proof.
  unfold qual_interp, qual_interp_full, qual_open_atom, mk_q_eq,
    qual_bvars, qual_vars, qual_prop, denote_value.
  destruct decide as [_|Hbad].
  - cbn [bv_value fv_value].
    change (set_map LVBound ({[0]} ∪ ∅)) with
      (lvars_of_bvars ({[0]} ∪ ∅)).
    rewrite lvars_fv_open.
    rewrite !lvars_fv_union, !lvars_fv_of_bvars, !lvars_fv_of_atoms.
    destruct decide as [_|Hbad_open].
    2:{
      exfalso. apply Hbad_open.
      apply lvars_bv_elem.
      apply elem_of_union_l.
      unfold lvars_of_bvars.
      apply elem_of_map.
      exists 0. split; [reflexivity | set_solver].
    }
    rewrite store_restrict_lookup.
    destruct decide as [_|Hnotx]; [| set_solver].
    split.
    + intros [v [Hx Hv]]. simpl in Hv.
      rewrite lookup_insert in Hv.
      destruct decide as [_|Hbad]; [| congruence].
      inversion Hv. subst. exact Hx.
    + intros Hx. exists (vconst c). split; [exact Hx |].
      simpl. rewrite lookup_insert.
      destruct decide as [_|Hbad]; [reflexivity | congruence].
  - exfalso. apply Hbad.
    apply lvars_bv_elem.
    apply elem_of_union_l.
    unfold bv_value, lvars_of_bvars.
    apply elem_of_map.
    exists 0. split; [reflexivity | set_solver].
Qed.

(** ** Shared locally-nameless class instances

    Keep these next to the qualifier lemmas they wrap.  A separate tiny
    instances file forces downstream files to reload this whole layer just to
    register typeclasses. *)

#[global] Instance OpenFv_qualifier : OpenFv atom type_qualifier.
Proof.
  intros q x k.
  pose proof (qual_open_atom_dom_subset k x q) as Hsub.
  intros z Hz.
  apply Hsub in Hz.
  simpl in Hz |- *.
  apply elem_of_union in Hz as [Hz|Hz].
  - apply elem_of_union_r. exact Hz.
  - apply elem_of_union_l. exact Hz.
Qed.

#[global] Instance OpenFvPrime_qualifier : OpenFvPrime atom type_qualifier.
Proof.
  intros [D p] x k.
  change (lvars_fv D ⊆ qual_dom (qual_open_atom k x (qual D p))).
  unfold qual_dom, qual_open_atom, qual_bvars.
  destruct (decide (k ∈ lvars_bv D)) as [Hin|Hnot].
  - intros z Hz.
    rewrite lvars_fv_open.
    apply elem_of_union_l. exact Hz.
  - intros z Hz. exact Hz.
Qed.

#[global] Instance Fact1_qualifier : Fact1 atom type_qualifier.
Proof.
  intros x y q i j Hij Hopen.
  destruct q as [D p].
  change (qual_open_atom i x (qual D p) = qual D p).
  change (qual_open_atom i x (qual_open_atom j y (qual D p)) =
    qual_open_atom j y (qual D p)) in Hopen.
  unfold qual_open_atom at 1. cbn [qual_bvars].
  destruct (decide (i ∈ lvars_bv D)) as [Hi|Hi]; [| reflexivity].
  exfalso.
  pose proof (f_equal (fun q => lvars_bv (qual_vars q)) Hopen) as Hb.
  cbn beta in Hb.
  rewrite !qual_vars_open_atom in Hb.
  rewrite !lvars_bv_open in Hb.
  set_solver.
Qed.

#[global] Instance OpenRecLc_qualifier : OpenRecLc atom type_qualifier.
Proof.
  intros q Hlc k x.
  destruct q as [D p].
  change (lc_qualifier (qual D p)) in Hlc.
  unfold lc_qualifier, qual_bvars in Hlc.
  change (qual_open_atom k x (qual D p) = qual D p).
  unfold qual_open_atom, qual_bvars.
  destruct (decide (k ∈ lvars_bv D)) as [Hin|Hnot]; [set_solver | reflexivity].
Qed.

#[global] Instance OpenLcRespect_qualifier : OpenLcRespect atom type_qualifier.
Proof.
  intros q x y k Hlc _ _.
  destruct q as [D p].
  change (lc_qualifier (qual_open_atom k x (qual D p))) in Hlc.
  change (lc_qualifier (qual_open_atom k y (qual D p))).
  unfold lc_qualifier, qual_open_atom, qual_bvars in *.
  destruct (decide (k ∈ lvars_bv D)) as [Hin|Hnot]; simpl in *.
  - rewrite lvars_bv_open in *. exact Hlc.
  - exact Hlc.
Qed.

(** MIGRATION NOTE(TypeLanguage): [OpenIdemp] is a legacy class instance for
    the old opening operation.  The new qualifier opening is modeled as a
    swap/open-back operation, so the reusable fact is involutivity/commutation,
    not idempotence.  Do not migrate this instance as a TypeLanguage lemma. *)

#[global] Instance OpenIdemp_qualifier : OpenIdemp atom type_qualifier.
Proof.
  intros q x y k _.
  destruct q as [D p].
  change (qual_open_atom k x (qual_open_atom k y (qual D p)) =
    qual_open_atom k y (qual D p)).
  unfold qual_open_atom, qual_bvars.
  destruct (decide (k ∈ lvars_bv D)) as [Hin|Hnot].
  2:{
    destruct (decide (k ∈ lvars_bv D)) as [Hin'|Hnot']; [set_solver | reflexivity].
  }
  rewrite lvars_bv_open.
  destruct decide as [Hbad|_]; [set_solver | reflexivity].
Qed.
