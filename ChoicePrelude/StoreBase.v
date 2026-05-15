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

Lemma map_restrict_agree (m1 m2 : gmap K A) X :
  (∀ x, x ∈ X → m1 !! x = m2 !! x) →
  map_restrict m1 X = map_restrict m2 X.
Proof.
  intros Hagree. apply map_eq. intros x.
  destruct (decide (x ∈ X)) as [Hx | Hx].
  - unfold map_restrict.
    destruct (m1 !! x) as [v1|] eqn:H1.
    + transitivity (Some v1).
      * apply map_lookup_filter_Some_2; [exact H1 | exact Hx].
      * symmetry. apply map_lookup_filter_Some_2; [rewrite <- (Hagree x Hx); exact H1 | exact Hx].
    + transitivity (@None A).
      * apply map_lookup_filter_None_2. left. exact H1.
      * symmetry. apply map_lookup_filter_None_2. left.
        rewrite <- (Hagree x Hx). exact H1.
  - unfold map_restrict.
    transitivity (@None A).
    + apply map_lookup_filter_None_2. right. intros v _ Hin. exact (Hx Hin).
    + symmetry. apply map_lookup_filter_None_2. right. intros v _ Hin. exact (Hx Hin).
Qed.

End MapOps.

Arguments map_compat {_ _ _} _ _ /.
Arguments map_restrict {_ _ _} _ _ /.

(** ** Atom-keyed stores *)

Definition atom_rename (x y z : atom) : atom :=
  if decide (z = x) then y else z.

Definition aset_rename (x y : atom) (X : aset) : aset :=
  if decide (x ∈ X) then {[y]} ∪ (X ∖ {[x]}) else X ∖ {[y]}.

Definition atom_swap (x y z : atom) : atom :=
  if decide (z = x) then y else if decide (z = y) then x else z.

Definition aset_swap (x y : atom) (X : aset) : aset :=
  set_map (atom_swap x y) X.

Lemma lvars_fv_swap x y (D : lvset) :
  lvars_fv (lvars_swap x y D) = aset_swap x y (lvars_fv D).
Proof.
Admitted.

Lemma atom_swap_involutive x y z :
  atom_swap x y (atom_swap x y z) = z.
Proof.
  unfold atom_swap. repeat destruct decide; congruence.
Qed.

Lemma atom_swap_fresh x y z :
  z ≠ x →
  z ≠ y →
  atom_swap x y z = z.
Proof.
  unfold atom_swap. repeat destruct decide; congruence.
Qed.

Lemma atom_swap_conjugate a b x y z :
  atom_swap a b (atom_swap x y z) =
  atom_swap (atom_swap a b x) (atom_swap a b y) (atom_swap a b z).
Proof.
  unfold atom_swap. repeat destruct decide; congruence.
Qed.

Lemma atom_swap_conjugate_inv a b x y z :
  atom_swap x y (atom_swap a b z) =
  atom_swap a b (atom_swap (atom_swap a b x) (atom_swap a b y) z).
Proof.
  unfold atom_swap. repeat destruct decide; congruence.
Qed.

Lemma atom_swap_sym x y z :
  atom_swap x y z = atom_swap y x z.
Proof.
  unfold atom_swap. repeat destruct decide; congruence.
Qed.

Lemma elem_of_aset_swap x y z X :
  z ∈ aset_swap x y X ↔ atom_swap x y z ∈ X.
Proof.
  unfold aset_swap. split.
  - intros [z0 [-> Hz0]]%elem_of_map.
    rewrite atom_swap_involutive. exact Hz0.
  - intros Hz.
    apply elem_of_map. exists (atom_swap x y z). split; [symmetry; apply atom_swap_involutive | exact Hz].
Qed.

Lemma aset_swap_involutive x y X :
  aset_swap x y (aset_swap x y X) = X.
Proof.
  apply set_eq. intros z. rewrite elem_of_aset_swap, elem_of_aset_swap.
  rewrite atom_swap_involutive. reflexivity.
Qed.

Lemma aset_swap_sym x y X :
  aset_swap x y X = aset_swap y x X.
Proof.
  apply set_eq. intros z.
  rewrite !elem_of_aset_swap, atom_swap_sym. reflexivity.
Qed.

Lemma aset_swap_fresh x y X :
  x ∉ X →
  y ∉ X →
  aset_swap x y X = X.
Proof.
  intros Hx Hy. apply set_eq. intros z.
  rewrite elem_of_aset_swap.
  split; intros Hz.
  - destruct (decide (z = x)) as [Hzx_eq|Hzx].
    { subst z. unfold atom_swap in Hz.
      destruct (decide (x = x)) as [_|Hxx]; [|congruence].
      exfalso. apply Hy. exact Hz. }
    destruct (decide (z = y)) as [Hzy_eq|Hzy].
    { subst z. unfold atom_swap in Hz.
      destruct (decide (y = x)) as [Hyx|_].
      - subst y. exfalso. apply Hx. exact Hz.
      - destruct (decide (y = y)) as [_|Hyy]; [|congruence].
        exfalso. apply Hx. exact Hz. }
    rewrite atom_swap_fresh in Hz by congruence. exact Hz.
  - rewrite atom_swap_fresh by set_solver. exact Hz.
Qed.

Lemma aset_swap_union x y X Y :
  aset_swap x y (X ∪ Y) = aset_swap x y X ∪ aset_swap x y Y.
Proof.
  apply set_eq. intros z.
  rewrite elem_of_aset_swap, !elem_of_union.
  rewrite !elem_of_aset_swap.
  tauto.
Qed.

Lemma aset_swap_empty x y :
  aset_swap x y ∅ = ∅.
Proof.
  apply set_eq. intros z. rewrite elem_of_aset_swap. set_solver.
Qed.

Lemma aset_swap_intersection x y X Y :
  aset_swap x y (X ∩ Y) = aset_swap x y X ∩ aset_swap x y Y.
Proof.
  apply set_eq. intros z.
  rewrite elem_of_aset_swap, !elem_of_intersection, !elem_of_aset_swap.
  tauto.
Qed.

Lemma aset_swap_disjoint x y X Y :
  aset_swap x y X ## aset_swap x y Y ↔ X ## Y.
Proof.
  unfold disjoint, set_disjoint_instance. split; intros Hdis z HzX HzY.
  - apply (Hdis (atom_swap x y z)).
    + rewrite elem_of_aset_swap, atom_swap_involutive. exact HzX.
    + rewrite elem_of_aset_swap, atom_swap_involutive. exact HzY.
  - rewrite elem_of_aset_swap in HzX.
    rewrite elem_of_aset_swap in HzY.
    exact (Hdis _ HzX HzY).
Qed.

Lemma aset_swap_singleton x y z :
  aset_swap x y ({[z]}) = {[atom_swap x y z]}.
Proof.
  apply set_eq. intros a.
  rewrite elem_of_aset_swap, !elem_of_singleton.
  split.
  - intros Ha.
    rewrite <- Ha. symmetry. apply atom_swap_involutive.
  - intros ->. apply atom_swap_involutive.
Qed.

Lemma aset_swap_conjugate a b x y X :
  aset_swap a b (aset_swap x y X) =
  aset_swap (atom_swap a b x) (atom_swap a b y) (aset_swap a b X).
Proof.
  apply set_eq. intros z.
  rewrite !elem_of_aset_swap.
  rewrite atom_swap_conjugate_inv. reflexivity.
Qed.

Lemma aset_swap_conjugate_inv a b x y X :
  aset_swap x y (aset_swap a b X) =
  aset_swap a b (aset_swap (atom_swap a b x) (atom_swap a b y) X).
Proof.
  apply set_eq. intros z.
  rewrite !elem_of_aset_swap.
  rewrite atom_swap_conjugate. reflexivity.
Qed.

Lemma aset_swap_difference_singleton x y z X :
  aset_swap x y (X ∖ {[z]}) =
  aset_swap x y X ∖ {[atom_swap x y z]}.
Proof.
  apply set_eq. intros a.
  rewrite elem_of_aset_swap, elem_of_difference, elem_of_singleton.
  rewrite elem_of_difference, elem_of_singleton, elem_of_aset_swap.
  split.
  - intros [Ha Hne]. split; [exact Ha |].
    intros Heq. apply Hne.
    rewrite <- (atom_swap_involutive x y z).
    by rewrite <- Heq.
  - intros [Ha Hne]. split; [exact Ha |].
    intros Heq. apply Hne.
    rewrite <- (atom_swap_involutive x y a).
    by rewrite Heq.
Qed.

Lemma aset_swap_difference x y X Y :
  aset_swap x y (X ∖ Y) =
  aset_swap x y X ∖ aset_swap x y Y.
Proof.
  apply set_eq. intros z.
  rewrite elem_of_aset_swap, !elem_of_difference, elem_of_aset_swap.
  split.
  - intros [HzX HzY]. split; [exact HzX |].
    intros HzswapY. apply HzY.
    rewrite elem_of_aset_swap in HzswapY.
    exact HzswapY.
  - intros [HzX HzY]. split; [exact HzX |].
    intros HzY'. apply HzY.
    rewrite elem_of_aset_swap.
    exact HzY'.
Qed.
