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

Lemma qual_open_atom_dom_subset k x q :
  qual_dom (qual_open_atom k x q) ⊆ qual_dom q ∪ {[x]}.
Proof.
  destruct q as [D P]. cbn [qual_dom qual_open_atom qual_lvars].
  apply lvars_fv_open_subset.
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

(** ** Qualifier Renaming

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
Arguments shift_qual_inst /.

Lemma qual_shift_from_vars k q :
  qual_vars (qual_shift_from k q) = lvars_shift_from k (qual_vars q).
Proof.
  destruct q. reflexivity.
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

Lemma qual_open_shift_from_lc_fresh k x q :
  lvars_lc_at k (qual_vars q) ->
  x ∉ qual_dom q ->
  qual_open_atom k x (qual_shift_from k q) = q.
Proof.
  intros Hlc Hx.
  destruct q as [D P].
  apply qual_ext; cbn [qual_vars qual_dom qual_lvars qual_prop
    qual_open_atom qual_shift_from qual_rename].
  - apply lvars_open_shift_from_lc_at_fresh; assumption.
  - intros s1 s2 Hs.
    assert (Hshift_id : forall (s : LStoreOnT D),
      lso_store (lstore_on_shift_from k s) = lso_store s).
    {
      intros s.
      apply lstore_shift_from_below_id. exact Hlc.
    }
    assert (Hopen_id :
      lso_store
        (lstore_on_open_back k x (lvars_shift_from k D) s1) =
      lso_store s1).
    {
      apply storeA_swap_fresh.
      - intros Hbad.
        pose proof Hbad as HbadD.
        pose proof (lso_dom s1) as Hdoms1.
        change (LVBound k ∈ dom (lso_store s1 : LStoreT)) in HbadD.
        rewrite Hdoms1 in HbadD.
        apply elem_of_set_swap in HbadD.
        unfold swap in HbadD.
        rewrite decide_True in HbadD by reflexivity.
        destruct (decide (LVFree x = LVBound k)) as [Hbad_eq|_];
          [discriminate|].
        apply elem_of_map in HbadD as [v [Hv HvD]].
        destruct v as [n|a]; cbn [logic_var_shift_from] in Hv.
        + repeat case_decide; inversion Hv.
        + inversion Hv. subst a.
          apply Hx. apply lvars_fv_elem. exact HvD.
      - intros Hbad.
        pose proof Hbad as HbadD.
        pose proof (lso_dom s1) as Hdoms1.
        change (LVFree x ∈ dom (lso_store s1 : LStoreT)) in HbadD.
        rewrite Hdoms1 in HbadD.
        apply elem_of_set_swap in HbadD.
        unfold swap in HbadD.
        destruct (decide (LVBound k = LVFree x)) as [Hbad_eq|Hneq];
          [discriminate|].
        rewrite decide_False in HbadD by (intros Heq; apply Hneq; symmetry; exact Heq).
        rewrite decide_True in HbadD by reflexivity.
        apply elem_of_map in HbadD as [v [Hv HvD]].
        destruct v as [n|a]; cbn [logic_var_shift_from] in Hv.
        + destruct (decide (k <= n)) as [Hkn|Hkn].
          * inversion Hv. lia.
          * inversion Hv. subst n.
            specialize (Hlc k ltac:(apply lvars_bv_elem; exact HvD)).
            lia.
        + discriminate.
    }
    split.
    + intros [s [Hshift HP]].
      pose proof (f_equal (@lso_store value _) Hshift) as Hshift_store.
      assert (Hs_eq : s = s2).
      {
        apply lstore_on_ext.
        transitivity (lso_store (lstore_on_shift_from k s)).
        - symmetry. apply Hshift_id.
        - transitivity
            (lso_store (lstore_on_open_back k x (lvars_shift_from k D) s1)).
          + exact Hshift_store.
          + rewrite Hopen_id. exact Hs.
      }
      subst s. exact HP.
    + intros HP.
      exists s2. split; [|exact HP].
      apply lstore_on_ext.
      transitivity (lso_store s2).
      { apply Hshift_id. }
      transitivity (lso_store s1).
      { symmetry. exact Hs. }
      symmetry. exact Hopen_id.
Qed.

Lemma qual_open_atom_fresh_lc_at k x q :
  (forall n, n ∈ lvars_bv (qual_vars q) -> n < k) ->
  x ∉ qual_dom q ->
  qual_open_atom k x q = q.
Proof.
  intros Hbelow Hx.
  destruct q as [D P].
  apply qual_ext; cbn [qual_vars qual_dom qual_lvars qual_prop
    qual_open_atom].
  - apply lvars_open_fresh_index.
    + intros Hk. specialize (Hbelow k Hk). lia.
    + exact Hx.
  - intros s1 s2 Hs.
    assert (Hopen_id :
      lso_store (lstore_on_open_back k x D s1) = lso_store s1).
    {
      apply storeA_swap_fresh.
      - intros Hbad.
        pose proof Hbad as HbadD.
        change (LVBound k ∈ dom (lso_store s1 : LStoreT)) in HbadD.
        rewrite (lso_dom s1) in HbadD.
        apply elem_of_set_swap in HbadD.
        unfold swap in HbadD.
        rewrite decide_True in HbadD by reflexivity.
        destruct (decide (LVFree x = LVBound k)) as [Hbad_eq|_];
          [discriminate|].
        apply Hx. apply lvars_fv_elem. exact HbadD.
      - intros Hbad.
        pose proof Hbad as HbadD.
        change (LVFree x ∈ dom (lso_store s1 : LStoreT)) in HbadD.
        rewrite (lso_dom s1) in HbadD.
        apply elem_of_set_swap in HbadD.
        unfold swap in HbadD.
        destruct (decide (LVBound k = LVFree x)) as [Hbad_eq|Hneq];
          [discriminate|].
        rewrite decide_False in HbadD by
          (intros Heq; apply Hneq; symmetry; exact Heq).
        rewrite decide_True in HbadD by reflexivity.
        specialize (Hbelow k ltac:(apply lvars_bv_elem; exact HbadD)).
        lia.
    }
    assert (Hback_eq : lstore_on_open_back k x D s1 = s2).
    {
      apply lstore_on_ext.
      rewrite Hopen_id. exact Hs.
    }
    split.
    + intros HP.
      rewrite Hback_eq in HP. exact HP.
    + intros HP.
      rewrite Hback_eq. exact HP.
Qed.
