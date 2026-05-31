(** * ContextTypeLanguage.Qualifier

    Type-level qualifiers are locally-nameless predicates over lvar-keyed
    stores.  This mirrors [LogicQualifier]'s dependent-domain design, except
    the payload is an [LStore] rather than an [LWorld].

    The core language operation is opening.  Opening is implemented as a swap
    between a bound lvar and a free atom, with the predicate interpreting its
    input after swapping the store back. *)

From CoreLang Require Export Prelude Syntax.
From ContextBase Require Export Prelude LogicVar LogicVarShift BaseTactics.
From ContextStore Require Export Store.
From Stdlib Require Import Logic.FunctionalExtensionality
  Logic.ProofIrrelevance Logic.PropExtensionality.

Local Notation LStoreT := (LStore (V := value)) (only parsing).
Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).
Local Notation StoreT := (Store (V := value)) (only parsing).
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

Definition qual_mlsubst (ρ : LStoreT) (q : type_qualifier) : type_qualifier :=
  match q with
  | tqual D P =>
      tqual (D ∖ dom (ρ : gmap logic_var value))
        (fun s => P (lstore_on_mlsubst_back D ρ s))
  end.

Definition qual_msubst_store (σ : StoreT) (q : type_qualifier) :
    type_qualifier :=
  qual_mlsubst (atom_store_to_lvar_store σ) q.

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

Lemma qual_mlsubst_vars ρ q :
  qual_vars (qual_mlsubst ρ q) =
  qual_vars q ∖ dom (ρ : gmap logic_var value).
Proof.
  destruct q. reflexivity.
Qed.

Lemma qual_msubst_store_vars σ q :
  qual_vars (qual_msubst_store σ q) =
  qual_vars q ∖ lvars_of_atoms (dom (σ : gmap atom value)).
Proof.
  unfold qual_msubst_store.
  rewrite qual_mlsubst_vars, atom_store_to_lvar_store_dom.
  reflexivity.
Qed.

Lemma atom_store_to_lvar_store_restrict_lvars_subset_eq
    (σ : StoreT) (D : lvset) (X : aset) :
  lvars_fv D ⊆ X ->
  storeA_restrict (atom_store_to_lvar_store (store_restrict σ X)) D =
  storeA_restrict (atom_store_to_lvar_store σ : LStoreT) D.
Proof.
  intros HDX.
  apply storeA_map_eq. intros v.
  destruct (decide (v ∈ D)) as [HvD|HvD].
  2:{
    transitivity (@None value).
    - apply storeA_restrict_lookup_none_r. exact HvD.
    - symmetry. apply storeA_restrict_lookup_none_r. exact HvD.
  }
  destruct v as [k|x].
  - transitivity (@None value).
    + apply storeA_restrict_lookup_none_l.
      apply atom_store_to_lvar_store_lookup_bound_none.
    + symmetry. apply storeA_restrict_lookup_none_l.
      apply atom_store_to_lvar_store_lookup_bound_none.
  - assert (HxX : x ∈ X).
    { apply HDX. apply lvars_fv_elem. exact HvD. }
    destruct ((σ : gmap atom value) !! x) as [v|] eqn:Hσx.
    + transitivity (Some v).
      * apply storeA_restrict_lookup_some_2; [|exact HvD].
        rewrite atom_store_to_lvar_store_lookup_free.
        apply storeA_restrict_lookup_some_2; [exact Hσx|exact HxX].
      * symmetry. apply storeA_restrict_lookup_some_2; [|exact HvD].
        rewrite atom_store_to_lvar_store_lookup_free. exact Hσx.
    + transitivity (@None value).
      * apply storeA_restrict_lookup_none_l.
        rewrite atom_store_to_lvar_store_lookup_free.
        apply storeA_restrict_lookup_none_l. exact Hσx.
      * symmetry. apply storeA_restrict_lookup_none_l.
        rewrite atom_store_to_lvar_store_lookup_free. exact Hσx.
Qed.

Lemma qual_msubst_store_restrict_subset
    (σ : StoreT) (q : type_qualifier) (X : aset) :
  qual_dom q ⊆ X ->
  qual_msubst_store σ q =
  qual_msubst_store (store_restrict σ X) q.
Proof.
  intros Hsub.
  destruct q as [D P].
  cbn [qual_msubst_store qual_mlsubst qual_dom qual_vars qual_lvars].
  assert (HρD :
    storeA_restrict (atom_store_to_lvar_store (store_restrict σ X)) D =
    storeA_restrict (atom_store_to_lvar_store σ : LStoreT) D).
  { apply atom_store_to_lvar_store_restrict_lvars_subset_eq. exact Hsub. }
  apply qual_ext.
  - change (D ∖ dom (atom_store_to_lvar_store σ : LStoreT) =
      D ∖ dom (atom_store_to_lvar_store (store_restrict σ X) : LStoreT)).
    pose proof (f_equal (fun s : gmap logic_var value => dom s) HρD)
      as Hdom.
    rewrite !storeA_restrict_dom in Hdom.
    apply set_eq. intros v.
    rewrite !elem_of_difference.
    set_solver.
  - intros s1 s2 Hs. cbn [qual_prop].
    enough (lstore_on_mlsubst_back D (atom_store_to_lvar_store σ) s1 =
      lstore_on_mlsubst_back D (atom_store_to_lvar_store (store_restrict σ X)) s2)
      as ->.
    { reflexivity. }
    apply lstore_on_mlsubst_back_restrict_eq; [symmetry; exact HρD|exact Hs].
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
      * unfold lstore_swap, lstore_rekey. apply storeA_swap_fresh; assumption.
      * exact Hs.
    + replace (lstore_on_open_back k x D s1) with s2; [exact HP|].
      symmetry. apply lstore_on_ext. cbn [lso_store].
      unfold lstore_on_open_back. cbn [lso_store].
      transitivity (lso_store s1).
      * unfold lstore_swap, lstore_rekey. apply storeA_swap_fresh; assumption.
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
      * unfold lstore_swap, lstore_rekey. apply storeA_swap_fresh; assumption.
      * exact Hs.
    + replace (lstore_on_open_back k x D s1) with s2; [exact HP|].
      symmetry. apply lstore_on_ext. cbn [lso_store].
      unfold lstore_on_open_back. cbn [lso_store].
      transitivity (lso_store s1).
      * unfold lstore_swap, lstore_rekey. apply storeA_swap_fresh; assumption.
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
    rewrite set_swap_elem.
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
    rewrite set_swap_conjugate.
    replace (swap (LVBound i) (LVFree x) (LVBound j))
      with (LVBound j).
    2:{ better_base_solver. }
    replace (swap (LVBound i) (LVFree x) (LVFree y))
      with (LVFree y).
    2:{ better_base_solver. }
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
      unfold lstore_swap, lstore_rekey.
      apply storeA_swap_commute_fresh; congruence.
    }
    rewrite Hback. tauto.
Qed.

Lemma qual_top_lc :
  lc_qualifier qual_top.
Proof.
  unfold lc_qualifier, qual_top. cbn [qual_lvars].
  intros v Hv. set_solver.
Qed.

(** * ContextTypeLanguage.Qualifier

    Qualifier transport for type qualifiers.

    Opening remains the primitive operation in [Qualifier.v], because it is the
    same involutive swap used by logic qualifiers.  Context-type denotation also needs
    binder-depth shifts; those are represented here as a renaming transport:
    the domain is renamed, and the new predicate holds exactly when the input
    store is the renamed image of an old input store satisfying the old
    predicate. *)

Definition qual_rename
    (f : logic_var -> logic_var) (Hf : Inj (=) (=) f)
    (q : type_qualifier) : type_qualifier :=
  match q with
  | tqual D P =>
      tqual (set_map f D)
        (fun s' =>
           exists s : LStoreOnT D,
             lstore_on_rekey f Hf s = s' /\ P s)
  end.

Definition qual_shift_from (k : nat) (q : type_qualifier) : type_qualifier :=
  qual_rename (logic_var_shift_from k) (logic_var_shift_from_inj k) q.

#[global] Instance shift_qual_inst : Shift type_qualifier :=
  qual_shift_from.

Lemma qual_shift_from_vars k q :
  qual_vars (qual_shift_from k q) = lvars_shift_from k (qual_vars q).
Proof.
  destruct q. reflexivity.
Qed.

Lemma qual_shift_from_dom k q :
  qual_dom (qual_shift_from k q) = qual_dom q.
Proof.
  destruct q as [D P].
  cbn [qual_dom qual_shift_from qual_rename qual_lvars].
  apply lvars_shift_from_fv.
Qed.

Lemma qual_shift_from_lc k q :
  lc_qualifier q ->
  lc_qualifier (qual_shift_from k q).
Proof.
  destruct q as [D P]. cbn [lc_qualifier qual_shift_from qual_rename qual_lvars].
  intros Hlc v Hv.
  unfold lvars_shift_from in Hv.
  apply elem_of_map in Hv as [u [-> Hu]].
  destruct u as [n|x]; cbn [logic_var_shift_from].
  - exfalso. exact (Hlc (LVBound n) Hu).
  - exact I.
Qed.

Lemma qual_shift_from_below_id k q :
  (forall n, n ∈ qual_bvars q -> n < k) ->
  qual_shift_from k q = q.
Proof.
  intros Hbelow.
  destruct q as [D P].
  apply qual_ext; cbn [qual_lvars qual_bvars qual_shift_from qual_rename].
  - apply lvars_shift_from_below_id. exact Hbelow.
  - intros s1 s2 Hs.
    split.
    + intros [s [Hs1 HP]].
      replace s with s2 in HP; [exact HP|].
      apply lstore_on_ext.
      rewrite <- Hs.
      rewrite <- Hs1.
      apply lstore_shift_from_below_id. exact Hbelow.
    + intros HP.
      exists s2. split; [|exact HP].
      apply lstore_on_ext.
      change (lso_store (lstore_on_shift_from k s2) = lso_store s1).
      rewrite (lstore_shift_from_below_id k D s2 Hbelow).
      symmetry. exact Hs.
Qed.

Lemma qual_open_shift_from_under_gen j k x q :
  j <= k ->
  qual_open_atom (S k) x (qual_shift_from j q) =
  qual_shift_from j (qual_open_atom k x q).
Proof.
  intros Hjk.
  destruct q as [D P].
  apply qual_ext; cbn [qual_lvars qual_prop qual_open_atom qual_shift_from
    qual_rename].
  - apply lvars_open_shift_from_under_gen. exact Hjk.
  - intros s1 s2 Hs.
    split.
    + intros [s [Hshift HP]].
      exists (lstore_on_open_front k x s). split.
      * apply lstore_on_ext.
        rewrite <- Hs.
        change (lso_store (lstore_on_shift_from j (lstore_on_open_front k x s)) =
          lso_store s1).
        rewrite lstore_on_shift_from_open_front by exact Hjk.
        replace (lstore_on_shift_from j s) with
          (lstore_on_open_back (S k) x
            (set_map (logic_var_shift_from j) D) s1)
          by (symmetry; exact Hshift).
        rewrite lstore_on_open_front_back. reflexivity.
      * rewrite lstore_on_open_back_front. exact HP.
    + intros [s [Hshift HP]].
      exists (lstore_on_open_back k x D s). split.
      * apply lstore_on_ext.
        change (lso_store (lstore_on_shift_from j (lstore_on_open_back k x D s)) =
          lso_store (lstore_on_open_back (S k) x
            (set_map (logic_var_shift_from j) D) s1)).
        rewrite lstore_on_shift_from_open_back by exact Hjk.
        replace (lso_store (lstore_on_shift_from j s)) with (lso_store s2)
          by (rewrite <- Hshift; reflexivity).
        transitivity (lstore_swap (LVBound (S k)) (LVFree x) (lso_store s1)).
        -- rewrite Hs. reflexivity.
        -- unfold lstore_on_open_back. cbn [lso_store]. reflexivity.
      * exact HP.
Qed.

Lemma qual_open_shift_from_under j k x q :
  j <= k ->
  qual_open_atom (S (S k)) x (qual_shift_from (S j) q) =
  qual_shift_from (S j) (qual_open_atom (S k) x q).
Proof.
  intros Hjk. apply qual_open_shift_from_under_gen. lia.
Qed.

Lemma qual_shift_open_commute k x q :
  qual_open_atom (S (S k)) x (qual_shift_from (S k) q) =
  qual_shift_from (S k) (qual_open_atom (S k) x q).
Proof.
  apply qual_open_shift_from_under_gen. lia.
Qed.

Lemma lvars_open_qual_vars_difference_bound0_under k y q :
  lvars_open (S k) y (qual_vars q ∖ {[LVBound 0]}) =
  qual_vars (qual_open_atom (S k) y q) ∖ {[LVBound 0]}.
Proof.
  rewrite qual_open_atom_vars.
  apply set_eq. intros v.
  rewrite set_swap_elem.
  rewrite elem_of_difference, elem_of_difference.
  split.
  - intros [Hv Hnot]. split.
    + rewrite set_swap_elem. exact Hv.
    + intros Hbad. apply Hnot.
      rewrite elem_of_singleton in Hbad |- *.
      subst v.
      unfold swap. repeat destruct decide; try lia; try congruence.
  - intros [Hv Hnot]. split.
    + rewrite set_swap_elem in Hv. exact Hv.
    + intros Hbad. apply Hnot.
      rewrite elem_of_singleton in Hbad |- *.
      destruct v as [n|a]; cbn in Hbad;
        unfold swap in Hbad;
        repeat destruct decide; try lia; try congruence.
Qed.
