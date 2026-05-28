(** * ContextTypeLanguage.Renaming

    Renaming transport for type qualifiers.

    Opening remains the primitive operation in [Qualifier.v], because it is the
    same involutive swap used by logic qualifiers.  Context-type denotation also needs
    binder-depth shifts; those are represented here as a renaming transport:
    the domain is renamed, and the new predicate holds exactly when the input
    store is the renamed image of an old input store satisfying the old
    predicate. *)

From ContextBase Require Export LogicVarShift.
From ContextTypeLanguage Require Export Qualifier.

Local Notation LStoreT := (LStore (V := value)) (only parsing).
Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Definition lstore_shift_from (k : nat) (s : LStoreT) : LStoreT :=
  lstore_rekey (logic_var_shift_from k) s.

Definition lstore_on_shift_from
    (k : nat) {D : lvset} (s : LStoreOnT D)
    : LStoreOnT (lvars_shift_from k D) :=
  lstore_on_rekey (logic_var_shift_from k) (logic_var_shift_from_inj k) s.

Lemma lstore_shift_from_below_id k D (s : LStoreOnT D) :
  (forall n, n ∈ lvars_bv D -> n < k) ->
  lso_store (lstore_on_shift_from k s) = lso_store s.
Proof.
  intros Hbelow.
  apply lstore_on_rekey_id_on_dom.
  intros [n|x] Hin; cbn [logic_var_shift_from].
  - destruct (decide (k <= n)) as [Hbad|_].
    + exfalso. pose proof (Hbelow n ltac:(apply lvars_bv_elem; exact Hin)).
      lia.
    + reflexivity.
  - reflexivity.
Qed.

Lemma lstore_shift_from_open_swap j k x (s : LStoreT) :
  j <= k ->
  lstore_shift_from j (lstore_swap (LVBound k) (LVFree x) s) =
  lstore_swap (LVBound (S k)) (LVFree x) (lstore_shift_from j s).
Proof.
  intros Hjk.
  unfold lstore_shift_from, lstore_swap, lstore_rekey.
  rewrite !storeA_rekey_compose;
    try apply logic_var_shift_from_inj;
    try apply swap_inj.
  apply storeA_rekey_ext_on_dom. intros v _.
  symmetry. apply logic_var_open_shift_from_under_gen. exact Hjk.
Qed.

Lemma lstore_on_shift_from_open_front j k x D (s : LStoreOnT D) :
  j <= k ->
  lso_store (lstore_on_shift_from j (lstore_on_open_front k x s)) =
  lso_store (lstore_on_open_front (S k) x (lstore_on_shift_from j s)).
Proof.
  intros Hjk.
  destruct s as [s Hdom]. simpl.
  unfold lstore_on_shift_from, lstore_on_open_front, lstore_on_rekey,
    storeA_on_rekey.
  cbn [lso_store storeAO_store].
  apply lstore_shift_from_open_swap. exact Hjk.
Qed.

Lemma lstore_on_shift_from_open_back j k x D
    (s : LStoreOnT (lvars_open k x D)) :
  j <= k ->
  lso_store (lstore_on_shift_from j (lstore_on_open_back k x D s)) =
  lstore_swap (LVBound (S k)) (LVFree x)
    (lso_store (lstore_on_shift_from j s)).
Proof.
  intros Hjk.
  destruct s as [s Hdom]. simpl.
  unfold lstore_on_shift_from, lstore_on_open_back, lstore_on_rekey,
    storeA_on_rekey.
  cbn [lso_store storeAO_store].
  apply lstore_shift_from_open_swap. exact Hjk.
Qed.

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
