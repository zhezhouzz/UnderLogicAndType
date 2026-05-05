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
  if decide (x ∈ X) then {[y]} ∪ (X ∖ {[x]}) else X ∖ {[y]}.

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
Proof.
  unfold store_rename_atom, aset_rename.
  destruct (s !! x) as [v|] eqn:Hx.
  - destruct (decide (x ∈ dom s)) as [_|Hnotin].
    + apply set_eq. intros z.
      change (z ∈ dom (<[y := v]> (delete x s) : gmap atom V) <->
        z ∈ ({[y]} ∪ dom (s : gmap atom V) ∖ {[x]} : aset)).
      rewrite elem_of_dom, lookup_insert_is_Some, lookup_delete_is_Some.
      rewrite elem_of_union, elem_of_singleton, elem_of_difference,
        elem_of_singleton, elem_of_dom.
      split.
      * intros [Hy | [Hny [Hnx His]]].
        -- left. symmetry. exact Hy.
        -- right. split; [exact His | congruence].
      * intros [Hzy | [His Hnx]].
        -- left. symmetry. exact Hzy.
        -- destruct (decide (z = y)) as [->|Hzy].
           ++ left. reflexivity.
           ++ right. repeat split; eauto; congruence.
    + exfalso. apply Hnotin. by apply elem_of_dom; exists v.
  - destruct (decide (x ∈ dom s)) as [Hin|_].
    + exfalso. apply not_elem_of_dom in Hx. set_solver.
    + apply set_eq. intros z.
      change (z ∈ dom (delete y s : gmap atom V) <->
        z ∈ (dom (s : gmap atom V) ∖ {[y]} : aset)).
      rewrite elem_of_dom, lookup_delete_is_Some.
      rewrite elem_of_difference, elem_of_singleton, elem_of_dom.
      firstorder congruence.
Qed.

Lemma elem_of_aset_rename x y z X :
  z ∈ aset_rename x y X ↔
    (z = y ∧ x ∈ X) ∨ (z ≠ y ∧ z ≠ x ∧ z ∈ X).
Proof.
  unfold aset_rename.
  destruct (decide (x ∈ X)) as [Hx|Hx].
  - rewrite elem_of_union, elem_of_singleton, elem_of_difference,
      elem_of_singleton.
    split.
    + intros [Hzy | [HzX Hzx]].
      * left. split; [exact Hzy | exact Hx].
      * destruct (decide (z = y)) as [Hzy|Hzy].
        -- left. split; [exact Hzy | exact Hx].
        -- right. repeat split; assumption.
    + intros [[Hzy _] | [Hzy [Hzx HzX]]].
      * left. exact Hzy.
      * right. set_solver.
  - rewrite elem_of_difference, elem_of_singleton.
    split.
    + intros [HzX Hzy]. right. set_solver.
    + intros [[-> HyX] | [Hzy [Hzx HzX]]]; set_solver.
Qed.

Lemma store_rename_atom_lookup x y s z :
  store_rename_atom x y s !! z =
    if decide (z = y)
    then s !! x
    else if decide (z = x)
         then None
         else s !! z.
Proof.
  unfold store_rename_atom.
  destruct (s !! x) as [vx|] eqn:Hx.
  - destruct (decide (z = y)) as [->|Hzy].
    + destruct (decide (y = y)); [|congruence].
      change ((<[y := vx]> (delete x s) : gmap atom V) !! y = Some vx).
      apply lookup_insert_eq.
    + change ((<[y := vx]> (delete x s) : gmap atom V) !! z =
        if decide (z = x) then None else s !! z).
      rewrite (lookup_insert_ne (delete x s) y z vx) by congruence.
      destruct (decide (z = y)); [congruence |].
      destruct (decide (z = x)) as [->|Hzx].
      * change ((delete x s : gmap atom V) !! x = None). apply lookup_delete_eq.
      * change ((delete x s : gmap atom V) !! z = s !! z).
        apply lookup_delete_ne. congruence.
  - destruct (decide (z = y)) as [->|Hzy].
    + destruct (decide (y = y)); [|congruence].
      change ((delete y s : gmap atom V) !! y = None).
      apply lookup_delete_eq.
    + change ((delete y s : gmap atom V) !! z =
        if decide (z = x) then None else s !! z).
      destruct (decide (z = y)); [congruence |].
      destruct (decide (z = x)) as [->|Hzx].
      * transitivity (s !! x).
        -- apply lookup_delete_ne. congruence.
        -- exact Hx.
      * change ((delete y s : gmap atom V) !! z = s !! z).
        apply lookup_delete_ne. congruence.
Qed.

Lemma store_restrict_lookup s X z :
  store_restrict s X !! z = if decide (z ∈ X) then s !! z else None.
Proof.
  unfold store_restrict, map_restrict.
  destruct (decide (z ∈ X)) as [Hz|Hz].
  - destruct (s !! z) eqn:Hs.
    + apply map_lookup_filter_Some_2; [exact Hs | exact Hz].
    + apply map_lookup_filter_None. left. exact Hs.
  - apply map_lookup_filter_None. right. intros v _ Hin. contradiction.
Qed.

Lemma store_restrict_rename_atom x y s X :
  store_restrict (store_rename_atom y x s) X =
  store_rename_atom y x (store_restrict s (aset_rename x y X)).
Proof.
  apply map_eq. intros z.
  rewrite store_restrict_lookup, !store_rename_atom_lookup.
  destruct (decide (z = x)) as [->|Hzx].
  - destruct (decide (x ∈ X)) as [HxX|HxX].
    + destruct (decide (y = y)); [|congruence].
      rewrite store_restrict_lookup.
      destruct (decide (y ∈ aset_rename x y X)) as [_|Hy].
      * reflexivity.
      * exfalso. apply Hy. rewrite elem_of_aset_rename. left. split; [reflexivity | exact HxX].
    + destruct (decide (y = y)); [|congruence].
      rewrite store_restrict_lookup.
      destruct (decide (y ∈ aset_rename x y X)) as [Hy|_].
      * rewrite elem_of_aset_rename in Hy. set_solver.
      * reflexivity.
  - destruct (decide (z = y)) as [->|Hzy].
    + destruct (decide (y ∈ X)) as [HyX|HyX].
      * destruct (decide (y = x)); [congruence |].
        destruct (decide (y = y)); [reflexivity | congruence].
      * destruct (decide (y = x)); [congruence |].
        destruct (decide (y = y)); [reflexivity | congruence].
    + destruct (decide (z ∈ X)) as [HzX|HzX].
      * rewrite store_restrict_lookup.
        destruct (decide (z ∈ aset_rename x y X)) as [_|Hzren].
        -- destruct (decide (z = y)); [congruence |].
           destruct (decide (z = x)); [congruence |].
           reflexivity.
        -- exfalso. apply Hzren. rewrite elem_of_aset_rename. right. set_solver.
      * rewrite store_restrict_lookup.
        destruct (decide (z ∈ aset_rename x y X)) as [Hzren|_].
        -- rewrite elem_of_aset_rename in Hzren. set_solver.
        -- destruct (decide (z = y)); [congruence |].
           destruct (decide (z = x)); [congruence |].
           reflexivity.
Qed.

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

Lemma store_compat_union_inv_l s1 s2 s3 :
  store_compat (s1 ∪ s2) s3 →
  store_compat s1 s3.
Proof.
  unfold store_compat. intros Hc i v1 v3 H1 H3.
  eapply Hc; [| exact H3].
  rewrite lookup_union_Some_raw. left. exact H1.
Qed.

Lemma store_compat_union_inv_r s1 s2 s3 :
  store_compat s1 s2 →
  store_compat (s1 ∪ s2) s3 →
  store_compat s2 s3.
Proof.
  unfold store_compat. intros H12 Hc i v2 v3 H2 H3.
  destruct (s1 !! i) as [v1|] eqn:H1.
  - assert (Hv : v1 = v3).
    { eapply Hc; [| exact H3].
      rewrite lookup_union_Some_raw. left. exact H1. }
    assert (Hv' : v1 = v2) by (eapply H12; eauto).
    congruence.
  - eapply Hc; [| exact H3].
    rewrite lookup_union_Some_raw. right. split; [exact H1 | exact H2].
Qed.

Lemma store_compat_union_intro_r s1 s2 s3 :
  store_compat s1 s2 →
  store_compat s1 s3 →
  store_compat s1 (s2 ∪ s3).
Proof.
  unfold store_compat. intros H12 H13 i v1 v23 H1 H23.
  rewrite lookup_union_Some_raw in H23.
  destruct H23 as [H2 | [H2none H3]].
  - eapply H12; eauto.
  - eapply H13; eauto.
Qed.

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

Lemma store_union_absorb_l s1 s2 :
  store_compat s1 s2 →
  dom s2 ⊆ dom s1 →
  s1 ∪ s2 = s1.
Proof.
  intros Hcompat Hsub. apply map_eq. intros i.
  rewrite option_eq. intros v.
  rewrite lookup_union_Some_raw.
  split.
  - intros [H1 | [H1 H2]]; [exact H1 |].
    exfalso. apply not_elem_of_dom in H1.
    apply H1. apply Hsub. by apply elem_of_dom; exists v.
  - intros H1. left. exact H1.
Qed.

Lemma store_restrict_dom s X :
  dom (store_restrict s X) = dom s ∩ X.
Proof.
  unfold store_restrict. apply dom_gmap_filter_key_in_pair.
Qed.

Lemma store_restrict_dom_subset s X :
  dom (store_restrict s X) ⊆ X.
Proof.
  rewrite store_restrict_dom. set_solver.
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

Lemma store_restrict_union_cover s1 s2 X1 X2 :
  store_compat s1 s2 →
  X1 ⊆ dom s1 →
  X2 ⊆ dom s2 →
  store_restrict (s1 ∪ s2) (X1 ∪ X2) =
  store_restrict s1 X1 ∪ store_restrict s2 X2.
Proof.
  intros Hcompat Hcover1 Hcover2.
  apply map_eq. intros i.
  change (map_restrict V (s1 ∪ s2) (X1 ∪ X2) !! i =
    (map_restrict V s1 X1 ∪ map_restrict V s2 X2) !! i).
  destruct (decide (i ∈ X1)) as [Hi1 | Hni1].
  - assert (i ∈ dom s1) as Hidom1 by set_solver.
    apply elem_of_dom in Hidom1 as [v1 Hlookup1].
    assert (Hrestrict1 : map_restrict V s1 X1 !! i = Some v1).
    {
      unfold map_restrict.
      apply map_lookup_filter_Some_2; [exact Hlookup1 | exact Hi1].
    }
    transitivity (Some v1).
    + unfold map_restrict.
      apply map_lookup_filter_Some_2; last set_solver.
      rewrite lookup_union_Some_raw. left. exact Hlookup1.
    + symmetry. rewrite lookup_union_l' by (eexists; exact Hrestrict1).
      exact Hrestrict1.
  - destruct (decide (i ∈ X2)) as [Hi2 | Hni2].
    + assert (i ∈ dom s2) as Hidom2 by set_solver.
      apply elem_of_dom in Hidom2 as [v2 Hlookup2].
      assert (Hleft_none : map_restrict V s1 X1 !! i = None).
      {
        unfold map_restrict.
        apply map_lookup_filter_None. right. intros v Hlookup Hin. set_solver.
      }
      rewrite lookup_union_r by exact Hleft_none.
      assert (Hrestrict2 : map_restrict V s2 X2 !! i = Some v2).
      {
        unfold map_restrict.
        apply map_lookup_filter_Some_2; [exact Hlookup2 | exact Hi2].
      }
      transitivity (Some v2).
      * unfold map_restrict.
        apply map_lookup_filter_Some_2; last set_solver.
        destruct (s1 !! i) as [v1|] eqn:Hlookup1.
        -- rewrite lookup_union_Some_raw. left.
           assert (v1 = v2) by (eapply Hcompat; eauto). subst. exact Hlookup1.
        -- rewrite lookup_union_Some_raw. right. exact (conj Hlookup1 Hlookup2).
      * symmetry. exact Hrestrict2.
    + assert (Hnotin : i ∉ X1 ∪ X2) by set_solver.
      assert (Hleft_none : map_restrict V s1 X1 !! i = None).
      {
        unfold map_restrict.
        apply map_lookup_filter_None. right. intros v Hlookup Hin. set_solver.
      }
      assert (Hright_none : map_restrict V s2 X2 !! i = None).
      {
        unfold map_restrict.
        apply map_lookup_filter_None. right. intros v Hlookup Hin. set_solver.
      }
      transitivity (@None V).
      * unfold map_restrict.
        apply map_lookup_filter_None. right.
        intros v Hlookup Hin. set_solver.
      * symmetry. rewrite lookup_union_r by exact Hleft_none. exact Hright_none.
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

Lemma store_restrict_union_partition s X Y :
  dom s ⊆ X ∪ Y →
  X ∩ Y = ∅ →
  store_restrict s X ∪ store_restrict s Y = s.
Proof.
  intros Hcover Hdisj.
  apply map_eq. intros i.
  change ((map_restrict V s X ∪ map_restrict V s Y) !! i = s !! i).
  destruct (s !! i) as [v|] eqn:Hi.
  - assert (Hi_dom : i ∈ dom s) by (apply elem_of_dom; eauto).
    specialize (Hcover _ Hi_dom).
    apply elem_of_union in Hcover as [HiX|HiY].
    + rewrite lookup_union_l'.
      * apply store_restrict_lookup_some_2; [exact Hi | exact HiX].
      * eexists. apply store_restrict_lookup_some_2; [exact Hi | exact HiX].
    + assert (Hleft_none : store_restrict s X !! i = None).
      {
        unfold store_restrict, map_restrict.
        apply map_lookup_filter_None. right.
        intros v' _ HiX.
        assert (HiXY : i ∈ X ∩ Y).
        { apply elem_of_intersection. split; [exact HiX | exact HiY]. }
        rewrite Hdisj in HiXY. apply elem_of_empty in HiXY. contradiction.
      }
      rewrite lookup_union_r by exact Hleft_none.
      apply store_restrict_lookup_some_2; [exact Hi | exact HiY].
  - assert (Hleft_none : store_restrict s X !! i = None).
    {
      unfold store_restrict, map_restrict.
      apply map_lookup_filter_None. left. exact Hi.
    }
    rewrite lookup_union_r by exact Hleft_none.
    unfold store_restrict, map_restrict.
    apply map_lookup_filter_None. left. exact Hi.
Qed.

Lemma store_restrict_union_piece_l s1 s2 X Y :
  store_compat s1 s2 →
  dom s1 ⊆ X →
  dom s2 ⊆ Y →
  Y ∩ X = ∅ →
  store_restrict (s1 ∪ s2) X = s1.
Proof.
  intros Hcompat Hdom1 Hdom2 Hdisj.
  apply map_eq. intros i.
  change (map_restrict V (s1 ∪ s2) X !! i = s1 !! i).
  destruct (s1 !! i) as [v1|] eqn:H1.
  - unfold map_restrict.
    apply map_lookup_filter_Some_2.
    + rewrite (lookup_union_l' s1 s2 i) by eauto. exact H1.
    + apply Hdom1. apply elem_of_dom. eauto.
  - unfold map_restrict.
    apply map_lookup_filter_None.
    destruct (decide (i ∈ X)) as [HiX|HiX].
    + left. change ((s1 ∪ s2) !! i = None).
      apply lookup_union_None. split; [exact H1 |].
      apply not_elem_of_dom. intros Hi2.
      assert (HiY : i ∈ Y) by set_solver.
      assert (HiYX : i ∈ Y ∩ X).
      { apply elem_of_intersection. split; [exact HiY | exact HiX]. }
      rewrite Hdisj in HiYX. apply elem_of_empty in HiYX. contradiction.
    + right. intros v Hlookup Hin. contradiction.
Qed.

Lemma store_restrict_union_piece_r s1 s2 X Y :
  store_compat s1 s2 →
  dom s1 ⊆ X →
  dom s2 ⊆ Y →
  X ∩ Y = ∅ →
  store_restrict (s1 ∪ s2) Y = s2.
Proof.
  intros Hcompat Hdom1 Hdom2 Hdisj.
  rewrite store_union_comm by exact Hcompat.
  apply (store_restrict_union_piece_l s2 s1 Y X).
  - apply store_compat_sym. exact Hcompat.
  - exact Hdom2.
  - exact Hdom1.
  - apply set_eq. intros i. split.
    + intros Hi.
      apply elem_of_intersection in Hi as [HiY HiX].
      assert (HiXY : i ∈ X ∩ Y).
      { apply elem_of_intersection. split; [exact HiY | exact HiX]. }
      rewrite Hdisj in HiXY. apply elem_of_empty in HiXY. contradiction.
    + intros Hi. apply elem_of_empty in Hi. contradiction.
Qed.

Lemma store_restrict_union_base_singleton s1 s2 D y :
  D ⊆ dom s1 →
  dom s2 = D ∪ {[y]} →
  y ∉ dom s1 →
  store_restrict s1 D = store_restrict s2 D →
  store_restrict (s1 ∪ store_restrict s2 {[y]}) (D ∪ {[y]}) = s2.
Proof.
  intros HDs1 Hdom2 Hy Hagree.
  apply map_eq. intros i.
  change (map_restrict V (s1 ∪ map_restrict V s2 {[y]}) (D ∪ {[y]}) !! i =
    s2 !! i).
  destruct (decide (i ∈ D)) as [HiD|HiD].
  - assert (Hi_s1 : i ∈ dom s1) by set_solver.
    apply elem_of_dom in Hi_s1 as [v1 Hs1].
    assert (Hs1D : store_restrict s1 D !! i = Some v1).
    { apply store_restrict_lookup_some_2; [exact Hs1 | exact HiD]. }
    rewrite Hagree in Hs1D.
    apply store_restrict_lookup_some in Hs1D as [_ Hs2].
    transitivity (Some v1); [| symmetry; exact Hs2].
    apply store_restrict_lookup_some_2; last set_solver.
    rewrite (lookup_union_l' s1 (store_restrict s2 {[y]}) i) by eauto.
    exact Hs1.
  - destruct (decide (i = y)) as [->|Hiy].
    + destruct (s2 !! y) as [vy|] eqn:Hs2y.
      * transitivity (Some vy); [| reflexivity].
        apply store_restrict_lookup_some_2; last set_solver.
        change ((s1 ∪ map_restrict V s2 {[y]}) !! y = Some vy).
        rewrite (lookup_union_r s1 (map_restrict V s2 {[y]}) y).
        -- apply store_restrict_lookup_some_2; [exact Hs2y | set_solver].
        -- by apply not_elem_of_dom.
      * assert (Hy_dom : y ∈ dom s2) by (rewrite Hdom2; set_solver).
        apply not_elem_of_dom in Hs2y. contradiction.
    + assert (Hi_not_dom2 : i ∉ dom s2).
      { rewrite Hdom2. set_solver. }
      apply not_elem_of_dom in Hi_not_dom2.
      transitivity (@None V); [| symmetry; exact Hi_not_dom2].
      unfold map_restrict.
      apply map_lookup_filter_None.
      right. intros v _ Hin. set_solver.
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

Lemma store_compat_restrict_singleton_fresh s1 s2 y :
  y ∉ dom s1 →
  store_compat s1 (store_restrict s2 {[y]}).
Proof.
  intros Hy.
  apply disj_dom_store_compat.
  apply set_eq. intros z. split.
  - intros Hz.
    apply elem_of_intersection in Hz as [Hz1 Hz2].
    pose proof (store_restrict_dom_subset s2 {[y]} z Hz2) as Hzy.
    rewrite elem_of_singleton in Hzy. subst. contradiction.
  - intros Hz. apply elem_of_empty in Hz. contradiction.
Qed.

Lemma store_compat_restrict s1 s2 X :
  store_compat s1 s2 → store_compat (store_restrict s1 X) (store_restrict s2 X).
Proof.
  unfold store_compat. intros Hcomp x y z H2 H3.
  apply store_restrict_lookup_some in H2.
  apply store_restrict_lookup_some in H3.
  hauto.
Qed.

Lemma store_compat_restrict_r s1 s2 X :
  store_compat s1 s2 → store_compat s1 (store_restrict s2 X).
Proof.
  unfold store_compat. intros Hcomp x y z H2 H3.
  apply store_restrict_lookup_some in H3. hauto.
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
