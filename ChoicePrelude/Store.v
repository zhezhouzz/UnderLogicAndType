(** * Stores and polymorphic finite-map restriction *)

From ChoicePrelude Require Export Prelude MapFilterDom.

(** ** Polymorphic finite-map compatibility and restriction *)

Section MapOps.

Context `{Countable K}.
Context {A : Type}.

Definition map_compat (m1 m2 : gmap K A) : Prop :=
  ∀ x v1 v2, m1 !! x = Some v1 → m2 !! x = Some v2 → v1 = v2.

Definition map_restrict (m : gmap K A) (X : gset K) : gmap K A :=
  filter (λ '(k, _), k ∈ X) m.

Lemma map_compat_refl m : map_compat m m.
Proof.
  unfold map_compat. intros x v1 v2 H1 H2. hauto.
Qed.

Lemma map_compat_sym m1 m2 :
  map_compat m1 m2 → map_compat m2 m1.
Proof. unfold map_compat. intros Hc x v1 v2 H1 H2. hauto. Qed.

Lemma map_compat_union m1 m2 :
  map_compat m1 m2 →
  map_compat (m1 ∪ m2) (m1 ∪ m2).
Proof. unfold map_compat. intros Hc x v1 v2 H1 H2. hauto. Qed.

Lemma map_restrict_dom m X :
  dom (map_restrict m X) = dom m ∩ X.
Proof.
  unfold map_restrict. apply dom_gmap_filter_key_in_pair.
Qed.

Lemma map_restrict_idemp m X :
  dom m ⊆ X → map_restrict m X = m.
Proof.
  unfold map_restrict. intros Hsub. apply map_filter_id.
  intros i x Hx. apply elem_of_dom_2 in Hx. set_solver.
Qed.

Lemma map_restrict_restrict m X Y :
  map_restrict (map_restrict m X) Y = map_restrict m (X ∩ Y).
Proof.
  unfold map_restrict.
  setoid_rewrite map_filter_filter.
  apply map_filter_ext.
  intros i x Hx. apply elem_of_dom_2 in Hx. set_solver.
Qed.

Lemma map_restrict_lookup_some m X x y :
  map_restrict m X !! x = Some y → x ∈ X ∧ m !! x = Some y.
Proof.
  unfold map_restrict. intro Hlookup.
  apply map_lookup_filter_Some in Hlookup.
  destruct Hlookup as [H1 H2]. split; [exact H2 | exact H1].
Qed.

End MapOps.

Arguments map_compat {_ _ _} _ _ /.
Arguments map_restrict {_ _ _} _ _ /.

(** ** Atom-keyed stores *)

Definition atom_rename (x y z : atom) : atom :=
  if decide (z = x) then y else z.

Definition aset_rename (x y : atom) (X : aset) : aset :=
  (if decide (x ∈ X) then {[y]} else ∅) ∪ (X ∖ {[x]}).

Section Store.

Context {V : Type} `{ValueSig V}.

Definition Store : Type := gmap atom V.

Definition store_compat (s1 s2 : Store) : Prop := map_compat V s1 s2.

Definition store_restrict (s : Store) (X : aset) : Store := map_restrict V s X.

Definition store_rename_atom (x y : atom) (s : Store) : Store :=
  match s !! x with
  | Some v => <[y := v]> (delete x s)
  | None => delete y s
  end.

Lemma store_rename_atom_dom x y s :
  dom (store_rename_atom x y s) = aset_rename x y (dom s).
Proof. Admitted.

Lemma store_compat_refl s : store_compat s s.
Proof.
  unfold store_compat. intros x v1 v2 H1 H2. hauto.
Qed.

Lemma store_compat_sym s1 s2 :
  store_compat s1 s2 → store_compat s2 s1.
Proof. unfold store_compat. intros Hc x v1 v2 H1 H2. hauto. Qed.

Lemma store_compat_union s1 s2 :
  store_compat s1 s2 →
  store_compat (s1 ∪ s2) (s1 ∪ s2).
Proof. unfold store_compat. intros Hc x v1 v2 H1 H2. hauto. Qed.

Lemma store_union_comm s1 s2 :
  store_compat s1 s2 →
  s1 ∪ s2 = s2 ∪ s1.
Proof.
  intros Hcompat. apply map_eq. intros i.
  rewrite option_eq. intros v.
  setoid_rewrite lookup_union_Some_raw.
  split.
  - intros [H1 | [H1 H2]].
    + destruct (s2 !! i) as [v2|] eqn:H2.
      * left.
        assert (Hv : v = v2) by (eapply Hcompat; eauto).
        subst. exact H2.
      * right. split; [exact H2 | exact H1].
    + left. exact H2.
  - intros [H2 | [H2 H1]].
    + destruct (s1 !! i) as [v1|] eqn:H1.
      * left.
        assert (Hv : v1 = v) by (eapply Hcompat; eauto).
        subst. exact H1.
      * right. split; [exact H1 | exact H2].
    + left. exact H1.
Qed.

Lemma store_restrict_dom s X :
  dom (store_restrict s X) = dom s ∩ X.
Proof.
  unfold store_restrict. apply dom_gmap_filter_key_in_pair.
Qed.

Lemma store_restrict_idemp s X :
  dom s ⊆ X → store_restrict s X = s.
Proof.
  unfold store_restrict. intros Hsub. apply map_filter_id.
  intros i x Hx. apply elem_of_dom_2 in Hx. set_solver.
Qed.

Lemma store_restrict_restrict s X Y :
  store_restrict (store_restrict s X) Y = store_restrict s (X ∩ Y).
Proof.
  unfold store_restrict, map_restrict.
  setoid_rewrite map_filter_filter.
  apply map_filter_ext.
  intros i x Hx. apply elem_of_dom_2 in Hx. set_solver.
Qed.

Lemma store_union_dom s1 s2 :
  store_compat s1 s2 →
  dom (s1 ∪ s2) = dom s1 ∪ dom s2.
Proof.
  intros Hcomp. setoid_rewrite dom_union_L. auto.
Qed.

Lemma store_restrict_induce_disjoint s1 s2 :
  s1 ##ₘ (store_restrict s2 (dom s2 ∖ dom s1)) ∧
  s1 ∪ s2 = s1 ∪ (store_restrict s2 (dom s2 ∖ dom s1)).
Proof.
  pose (s2' := store_restrict s2 (dom s2 ∖ dom s1)).
  split.
  - rewrite map_disjoint_alt. intros i.
    destruct (decide (i ∈ dom s1)).
    + right.
      apply map_lookup_filter_None_2. right.
      intros x Hx Hi%elem_of_difference.
      destruct Hi as [_ Hi']. by apply Hi'.
    + left. by apply not_elem_of_dom.
  - apply map_eq. intros i.
    destruct (s1 !! i) as [x|] eqn:E1.
    + rewrite (lookup_union_l' s1 s2 i) by (by exists x; exact E1).
      rewrite (lookup_union_l' s1 s2' i) by (by exists x; exact E1).
      reflexivity.
    + rewrite (lookup_union_r s1 s2 i) by done.
      rewrite (lookup_union_r s1 s2' i) by done.
      destruct (s2 !! i) as [y|] eqn:E2.
      * etrans.
        -- exact E2.
        -- symmetry. unfold s2', store_restrict.
           apply map_lookup_filter_Some_2; first exact E2.
           apply elem_of_difference. split.
           ++ by apply elem_of_dom; exists y.
           ++ by apply not_elem_of_dom.
      * apply eq_trans with (@None V); first exact E2.
        symmetry. unfold s2', store_restrict.
        apply map_lookup_filter_None. left. exact E2.
Qed.

Lemma store_restrict_union s1 s2 X :
  store_compat s1 s2 →
  store_restrict (s1 ∪ s2) X = store_restrict s1 X ∪ store_restrict s2 X.
Proof.
  intros Hcomp.
  unfold store_restrict, map_restrict.
  setoid_rewrite gmap_filter_key_pair.
  apply map_eq. intros i.
  rewrite option_eq. intros x.
  setoid_rewrite map_lookup_filter_Some.
  setoid_rewrite lookup_union_Some_raw.
  setoid_rewrite map_lookup_filter_Some.
  setoid_rewrite map_lookup_filter_None.
  simpl. split.
  - intros [[H1|[H1 H2]] HP].
    + left. eauto.
    + right. split. { left. exact H1. } eauto.
  - intros [[H1 HP]|[[H1|H1] [H2 HP]]].
    + split. { left. exact H1. } exact HP.
    + split. { right. eauto. } exact HP.
    + destruct (s1 !! i) as [y|] eqn:Ey.
      * exfalso. exact (H1 y Ey HP).
      * split. { right. eauto. } exact HP.
Qed.

Lemma store_restrict_lookup_some s X x y :
  store_restrict s X !! x = Some y → x ∈ X ∧ s !! x = Some y.
Proof.
  unfold store_restrict. intro Hlookup.
  apply map_lookup_filter_Some in Hlookup.
  destruct Hlookup as [H1 H2]. split; [exact H2 | exact H1].
Qed.

Lemma store_restrict_lookup_some_2 s X x y :
  s !! x = Some y →
  x ∈ X →
  store_restrict s X !! x = Some y.
Proof.
  unfold store_restrict, map_restrict. intros Hlookup Hin.
  apply map_lookup_filter_Some_2; [exact Hlookup | exact Hin].
Qed.

Lemma disj_dom_store_compat s1 s2 :
  dom s1 ∩ dom s2 = ∅ → store_compat s1 s2.
Proof.
  intros Hdisj.
  unfold store_compat, map_compat.
  intros x v1 v2 H1 H2.
  assert (x ∈ dom s1 ∩ dom s2) as Hin.
  { apply elem_of_intersection. split; apply elem_of_dom; eauto. }
  set_solver.
Qed.

Lemma store_compat_restrict s1 s2 X :
  store_compat s1 s2 → store_compat (store_restrict s1 X) (store_restrict s2 X).
Proof.
  unfold store_compat. intros Hcomp x y z H2 H3.
  apply store_restrict_lookup_some in H2.
  apply store_restrict_lookup_some in H3.
  hauto.
Qed.

Lemma store_compat_restrict_eq s1 s2 :
  store_compat s1 s2 →
  dom s1 ⊆ dom s2 →
  store_restrict s2 (dom s1) = s1.
Proof.
  unfold store_compat. intros Hcomp Hsub.
  apply map_eq. intros i.
  destruct (s1 !! i) as [v1|] eqn:H1.
  - assert (i ∈ dom s2) as Hin2 by (apply Hsub; apply elem_of_dom; eauto).
    pose (H2 := lookup_lookup_total_dom s2 i Hin2).
    assert (H2' : s2 !! i = Some v1).
    { transitivity (Some (s2 !!! i)); first exact H2.
      f_equal. symmetry. exact (Hcomp i v1 (s2 !!! i) H1 H2). }
    etrans.
    + unfold store_restrict, map_restrict.
      apply map_lookup_filter_Some_2; last by apply elem_of_dom; eauto.
      exact H2'.
    + symmetry. exact H1.
  - unfold store_restrict, map_restrict.
    etrans.
    + apply map_lookup_filter_None. right.
      intros v2 H2 Hin.
      apply not_elem_of_dom in H1. set_solver.
    + symmetry. exact H1.
Qed.

Lemma store_compat_spec s1 s2 :
  store_compat s1 s2 ↔
  store_restrict s1 (dom s1 ∩ dom s2) =
  store_restrict s2 (dom s1 ∩ dom s2).
Proof.
  split.
  - intros Hcompat.
    apply map_eq. intros x.
    rewrite option_eq. intros v.
    unfold store_restrict, map_restrict.
    setoid_rewrite map_lookup_filter_Some.
    simpl. split.
    + intros [Hs1 Hin].
      apply elem_of_intersection in Hin as [Hin1 Hin2].
      pose proof (lookup_lookup_total_dom s2 x Hin2) as Hs2.
      assert (Hv : v = s2 !!! x) by (eapply Hcompat; eauto).
      subst. split; [exact Hs2 |].
      apply elem_of_intersection. split; [exact Hin1 | exact Hin2].
    + intros [Hs2 Hin].
      apply elem_of_intersection in Hin as [Hin1 Hin2].
      pose proof (lookup_lookup_total_dom s1 x Hin1) as Hs1.
      assert (Hv : s1 !!! x = v) by (eapply Hcompat; eauto).
      subst. split; [exact Hs1 |].
      apply elem_of_intersection. split; [exact Hin1 | exact Hin2].
  - intros Heq.
    unfold store_compat, map_compat.
    intros x v1 v2 H1 H2.
    assert (Hin : x ∈ dom s1 ∩ dom s2).
    { apply elem_of_intersection. split; apply elem_of_dom; eauto. }
    assert (Hr1 : store_restrict s1 (dom s1 ∩ dom s2) !! x = Some v1).
    { apply store_restrict_lookup_some_2; [exact H1 | exact Hin]. }
    assert (Hr2 : store_restrict s2 (dom s1 ∩ dom s2) !! x = Some v2).
    { apply store_restrict_lookup_some_2; [exact H2 | exact Hin]. }
    rewrite Heq in Hr1. rewrite Hr2 in Hr1. by inversion Hr1.
Qed.

End Store.

#[global] Instance stale_store {A} : Stale (gmap atom A) := dom.
Arguments stale_store /.
