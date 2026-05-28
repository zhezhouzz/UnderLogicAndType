(** * ContextTypeLanguage.Qualifier

    Type-level qualifiers are locally-nameless predicates over lvar-keyed
    stores.  This mirrors [LogicQualifier]'s dependent-domain design, except
    the payload is an [LStore] rather than an [LWorld].

    The core language operation is opening.  Opening is implemented as a swap
    between a bound lvar and a free atom, with the predicate interpreting its
    input after swapping the store back. *)

From CoreLang Require Export Prelude Syntax.
From ContextBase Require Export Prelude LogicVar.
From ContextStore Require Export Store.
From Stdlib Require Import Logic.FunctionalExtensionality
  Logic.ProofIrrelevance Logic.PropExtensionality.

Local Notation LStoreT := (LStore (V := value)) (only parsing).
Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).
Record type_qualifier : Type := tqual {
  qual_lvars : lvset;
  qual_prop : LStoreOnT qual_lvars -> Prop;
}.

Definition qual_vars (q : type_qualifier) : lvset :=
  qual_lvars q.

Definition qual_dom (q : type_qualifier) : aset :=
  lvars_fv (qual_lvars q).

Definition qual_bvars (q : type_qualifier) : gset nat :=
  lvars_bv (qual_lvars q).

Definition qual_open_atom
    (k : nat) (x : atom) (q : type_qualifier) : type_qualifier :=
  match q with
  | tqual D P =>
      tqual (lvars_open k x D)
        (fun s => P (lstore_on_open_back k x D s))
  end.

Definition qual_top : type_qualifier :=
  tqual ∅ (fun _ => True).

Definition qual_and (q1 q2 : type_qualifier) : type_qualifier :=
  match q1, q2 with
  | tqual D1 P1, tqual D2 P2 =>
      tqual (D1 ∪ D2)
        (fun s =>
           P1 (lstore_on_restrict D1 s ltac:(set_solver)) /\
           P2 (lstore_on_restrict D2 s ltac:(set_solver)))
  end.

Definition lc_qualifier (q : type_qualifier) : Prop :=
  lc_lvars (qual_lvars q).

Definition body_qualifier (q : type_qualifier) : Prop :=
  exists L : aset, forall x : atom, x ∉ L -> lc_qualifier (qual_open_atom 0 x q).

#[global] Instance stale_qualifier : Stale type_qualifier := qual_dom.
Arguments stale_qualifier /.

#[global] Instance open_qual_atom_inst : Open atom type_qualifier := qual_open_atom.
Arguments open_qual_atom_inst /.

#[global] Instance lc_qual_inst : Lc type_qualifier := lc_qualifier.
Arguments lc_qual_inst /.

Notation "q '^q^' x" := (qual_open_atom 0 x q) (at level 20).
Notation "q1 '&q' q2" := (qual_and q1 q2) (at level 40).
Notation "⊤q" := qual_top.

Lemma qual_ext (q1 q2 : type_qualifier) :
  qual_lvars q1 = qual_lvars q2 ->
  (forall (s1 : LStoreOnT (qual_lvars q1))
          (s2 : LStoreOnT (qual_lvars q2)),
      lso_store s1 = lso_store s2 ->
      qual_prop q1 s1 <-> qual_prop q2 s2) ->
  q1 = q2.
Proof.
  destruct q1 as [D1 P1], q2 as [D2 P2]. simpl.
  intros HD HP. subst D2. f_equal.
  apply functional_extensionality. intros s.
  apply propositional_extensionality.
  apply HP. reflexivity.
Qed.

Lemma qual_open_atom_vars k x q :
  qual_vars (qual_open_atom k x q) = lvars_open k x (qual_vars q).
Proof.
  destruct q. reflexivity.
Qed.

Lemma lvars_fv_qual_vars q :
  lvars_fv (qual_vars q) = qual_dom q.
Proof. reflexivity. Qed.

Lemma lvars_fv_qual_vars_difference_free q x :
  lvars_fv (qual_vars q ∖ {[LVFree x]}) = qual_dom q ∖ {[x]}.
Proof.
  rewrite lvars_fv_difference_singleton_free.
  rewrite lvars_fv_qual_vars. reflexivity.
Qed.

Lemma lvars_open_qual_vars_difference_bound k x q :
  lvars_open k x (qual_vars q ∖ {[LVBound k]}) =
  qual_vars (qual_open_atom k x q) ∖ {[LVFree x]}.
Proof.
  rewrite qual_open_atom_vars.
  apply lvars_open_difference_bound.
Qed.

Lemma lvars_open_qual_vars_difference_bound0 x q :
  lvars_open 0 x (qual_vars q ∖ {[LVBound 0]}) =
  qual_vars (qual_open_atom 0 x q) ∖ {[LVFree x]}.
Proof.
  apply lvars_open_qual_vars_difference_bound.
Qed.

Lemma qual_open_atom_dom_subset k x q :
  qual_dom (qual_open_atom k x q) ⊆ qual_dom q ∪ {[x]}.
Proof.
  destruct q as [D P]. cbn [qual_dom qual_open_atom qual_lvars].
  apply lvars_fv_open_subset.
Qed.

Lemma qual_open_atom_dom_fresh_ne k x y q :
  x ∉ qual_dom q ->
  x <> y ->
  x ∉ qual_dom (qual_open_atom k y q).
Proof.
  intros Hx Hy Hbad.
  pose proof (qual_open_atom_dom_subset k y q x Hbad).
  set_solver.
Qed.

Lemma qual_open_atom_bvars k x q :
  qual_bvars (qual_open_atom k x q) =
    lvars_bv (lvars_open k x (qual_vars q)).
Proof.
  destruct q. reflexivity.
Qed.

Lemma qual_open_atom_lc_fresh k x q :
  lc_qualifier q ->
  x ∉ qual_dom q ->
  qual_open_atom k x q = q.
Proof.
  intros Hlc Hx.
  destruct q as [D P].
  apply qual_ext; cbn [qual_lvars qual_prop qual_open_atom qual_dom] in *.
  - apply lvars_open_fresh_index.
    + intros Hk. rewrite lvars_bv_elem in Hk. exact (Hlc _ Hk).
    + exact Hx.
  - intros s1 s2 Hs.
    assert (HD : lvars_open k x D = D).
    { apply lvars_open_fresh_index.
      - intros Hk. rewrite lvars_bv_elem in Hk. exact (Hlc _ Hk).
      - exact Hx. }
    assert (Hbound : LVBound k ∉ dom (lso_store s1 : LStoreT)).
    { rewrite (lso_dom s1), HD. intros Hbad.
      exact (Hlc _ Hbad). }
    assert (Hfree : LVFree x ∉ dom (lso_store s1 : LStoreT)).
    { rewrite (lso_dom s1), HD. intros Hbad.
      apply Hx. apply lvars_fv_elem. exact Hbad. }
    split; intros HP; cbn [lstore_on_open_back lso_store] in *.
    + replace (lstore_on_open_back k x D s1) with s2 in HP; [exact HP|].
      symmetry. apply lstore_on_ext. cbn [lso_store].
      unfold lstore_on_open_back. cbn [lso_store].
      transitivity (lso_store s1).
      * apply lstore_swap_fresh; assumption.
      * exact Hs.
    + replace (lstore_on_open_back k x D s1) with s2; [exact HP|].
      symmetry. apply lstore_on_ext. cbn [lso_store].
      unfold lstore_on_open_back. cbn [lso_store].
      transitivity (lso_store s1).
      * apply lstore_swap_fresh; assumption.
      * exact Hs.
Qed.

Lemma qual_open_atom_fresh_index k x q :
  k ∉ qual_bvars q ->
  x ∉ qual_dom q ->
  qual_open_atom k x q = q.
Proof.
  intros Hk Hx.
  destruct q as [D P].
  apply qual_ext; cbn [qual_lvars qual_prop qual_open_atom qual_dom qual_bvars] in *.
  - apply lvars_open_fresh_index; assumption.
  - intros s1 s2 Hs.
    assert (HD : lvars_open k x D = D) by
      (apply lvars_open_fresh_index; assumption).
    assert (Hbound : LVBound k ∉ dom (lso_store s1 : LStoreT)).
    { rewrite (lso_dom s1), HD. intros Hbad.
      apply Hk. apply lvars_bv_elem. exact Hbad. }
    assert (Hfree : LVFree x ∉ dom (lso_store s1 : LStoreT)).
    { rewrite (lso_dom s1), HD. intros Hbad.
      apply Hx. apply lvars_fv_elem. exact Hbad. }
    split; intros HP; cbn [lstore_on_open_back lso_store] in *.
    + replace (lstore_on_open_back k x D s1) with s2 in HP; [exact HP|].
      symmetry. apply lstore_on_ext. cbn [lso_store].
      unfold lstore_on_open_back. cbn [lso_store].
      transitivity (lso_store s1).
      * apply lstore_swap_fresh; assumption.
      * exact Hs.
    + replace (lstore_on_open_back k x D s1) with s2; [exact HP|].
      symmetry. apply lstore_on_ext. cbn [lso_store].
      unfold lstore_on_open_back. cbn [lso_store].
      transitivity (lso_store s1).
      * apply lstore_swap_fresh; assumption.
      * exact Hs.
Qed.

Lemma qual_open_same_index_absorb k x y q :
  x <> y ->
  x ∉ qual_dom q ->
  y ∉ qual_dom q ->
  qual_open_atom k y (qual_open_atom k x q) =
  qual_open_atom k x q.
Proof.
  intros Hxy Hx Hy.
  apply qual_open_atom_fresh_index.
  - rewrite qual_open_atom_bvars, lvars_bv_elem.
    rewrite lvars_open_unfold, set_swap_elem.
    unfold swap.
    repeat destruct decide; try congruence.
    intros Hbad. apply Hx. apply lvars_fv_elem. exact Hbad.
  - intros Hyopen.
    pose proof (qual_open_atom_dom_subset k x q y Hyopen) as Hycases.
    apply elem_of_union in Hycases as [HyD | Hyx].
    + exact (Hy HyD).
    + rewrite elem_of_singleton in Hyx. congruence.
Qed.

Lemma qual_open_commute_fvar i j x y q :
  i <> j ->
  x <> y ->
  qual_open_atom i x (qual_open_atom j y q) =
  qual_open_atom j y (qual_open_atom i x q).
Proof.
  intros Hij Hxy.
  destruct q as [D P].
  apply qual_ext.
  - cbn [qual_lvars qual_open_atom].
    rewrite !lvars_open_unfold.
    rewrite set_swap_conjugate.
    replace (swap (LVBound i) (LVFree x) (LVBound j))
      with (LVBound j).
    2:{ symmetry. apply swap_fresh; congruence. }
    replace (swap (LVBound i) (LVFree x) (LVFree y))
      with (LVFree y).
    2:{ symmetry. apply swap_fresh; congruence. }
    reflexivity.
  - intros s1 s2 Hs.
    cbn [qual_prop qual_open_atom].
    assert (Hback :
      lstore_on_open_back j y D
        (lstore_on_open_back i x (lvars_open j y D) s1) =
      lstore_on_open_back i x D
        (lstore_on_open_back j y (lvars_open i x D) s2)).
    {
      apply lstore_on_ext.
      cbn [lso_store].
      unfold lstore_on_open_back. cbn [lso_store].
      change (lstore_swap (LVBound j) (LVFree y)
          (lstore_swap (LVBound i) (LVFree x) (lso_store s1)) =
        lstore_swap (LVBound i) (LVFree x)
          (lstore_swap (LVBound j) (LVFree y) (lso_store s2))).
      rewrite <- Hs.
      symmetry.
      apply lstore_swap_commute_fresh; congruence.
    }
    rewrite Hback. tauto.
Qed.

Lemma qual_top_lc :
  lc_qualifier qual_top.
Proof.
  unfold lc_qualifier, qual_top. cbn [qual_lvars].
  intros v Hv. set_solver.
Qed.
