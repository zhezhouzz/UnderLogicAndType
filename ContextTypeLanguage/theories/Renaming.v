(** * ContextTypeLanguage.Renaming

    Renaming transport for type qualifiers.

    Opening remains the primitive operation in [Qualifier.v], because it is the
    same involutive swap used by logic qualifiers.  Context-type denotation also needs
    binder-depth shifts; those are represented here as a renaming transport:
    the domain is renamed, and the new predicate holds exactly when the input
    store is the renamed image of an old input store satisfying the old
    predicate. *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From ContextTypeLanguage Require Export Qualifier.

Local Notation LStoreT := (LStore (V := value)) (only parsing).
Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Class Shift A := shift_from : nat -> A -> A.
Notation "'↑[' k ']'" := (shift_from k)
  (at level 10, k constr, format "↑[ k ]").

Definition logic_var_shift_from (k : nat) (v : logic_var) : logic_var :=
  match v with
  | LVFree x => LVFree x
  | LVBound n => if decide (k <= n) then LVBound (S n) else LVBound n
  end.

Lemma logic_var_shift_from_lt k n :
  n < k ->
  logic_var_shift_from k (LVBound n) = LVBound n.
Proof.
  intros Hlt. cbn [logic_var_shift_from].
  destruct (decide (k <= n)) as [Hbad|_]; [lia|reflexivity].
Qed.

Lemma logic_var_shift_from_ge k n :
  k <= n ->
  logic_var_shift_from k (LVBound n) = LVBound (S n).
Proof.
  intros Hge. cbn [logic_var_shift_from].
  destruct (decide (k <= n)) as [_|Hbad]; [reflexivity|lia].
Qed.

Lemma logic_var_open_shift_from_under_gen j k x v :
  j <= k ->
  logic_var_open (S k) x (logic_var_shift_from j v) =
  logic_var_shift_from j (logic_var_open k x v).
Proof.
  intros Hjk.
  destruct v as [n|y];
    unfold logic_var_open, swap, swap, logic_var_shift_from;
    repeat (destruct (decide _) as [?|?]; subst;
      simpl in *;
      repeat match goal with
      | H : LVBound _ = LVBound _ |- _ => inversion H; subst; clear H
      | H : LVFree _ = LVFree _ |- _ => inversion H; subst; clear H
      end;
      try discriminate; try congruence; try lia; try reflexivity);
    repeat match goal with
    | H : LVBound _ = LVBound _ |- _ => inversion H; subst; clear H
    | H : LVFree _ = LVFree _ |- _ => inversion H; subst; clear H
    end;
    try discriminate; try congruence; try lia; reflexivity.
Qed.

Lemma logic_var_open_shift_from_under j k x v :
  j <= k ->
  logic_var_open (S (S k)) x (logic_var_shift_from (S j) v) =
  logic_var_shift_from (S j) (logic_var_open (S k) x v).
Proof.
  intros Hjk. apply logic_var_open_shift_from_under_gen. lia.
Qed.

Lemma logic_var_shift_from_inj k :
  Inj (=) (=) (logic_var_shift_from k).
Proof.
  intros v1 v2 Hv.
  destruct v1 as [n1|x1], v2 as [n2|x2];
    cbn [logic_var_shift_from] in Hv.
  - destruct (decide (k <= n1)) as [Hn1|Hn1];
      destruct (decide (k <= n2)) as [Hn2|Hn2];
      inversion Hv; subst; try reflexivity; lia.
  - destruct (decide (k <= n1)); inversion Hv.
  - destruct (decide (k <= n2)); inversion Hv.
  - inversion Hv. subst. reflexivity.
Qed.

Definition open_env_shift_key_from (k n : nat) : nat :=
  if decide (n < k) then n else S n.

Definition open_env_shift_from (k : nat) (η : gmap nat atom) : gmap nat atom :=
  kmap (open_env_shift_key_from k) η.

Lemma open_env_shift_key_from_inj k :
  Inj (=) (=) (open_env_shift_key_from k).
Proof.
  intros i j Hij.
  unfold open_env_shift_key_from in Hij.
  repeat destruct decide; lia.
Qed.

Lemma open_env_shift_key_from_zero n :
  open_env_shift_key_from 0 n = S n.
Proof.
  unfold open_env_shift_key_from.
  destruct (decide (n < 0)) as [Hbad|_]; [lia|reflexivity].
Qed.

Lemma open_env_shift_from_zero η :
  open_env_shift_from 0 η = (kmap S η).
Proof.
  unfold open_env_shift_from.
  assert (Hkey : open_env_shift_key_from 0 = S).
  { apply functional_extensionality. apply open_env_shift_key_from_zero. }
  rewrite Hkey. reflexivity.
Qed.

Lemma open_env_shift_from_lookup k η n :
  open_env_shift_from k η !! open_env_shift_key_from k n = η !! n.
Proof.
  unfold open_env_shift_from.
  rewrite (lookup_kmap (M1:=gmap nat) (M2:=gmap nat)
    (Inj0:=open_env_shift_key_from_inj k)
    (open_env_shift_key_from k) η n).
  reflexivity.
Qed.

Lemma logic_var_open_env_shift_from k η v :
  logic_var_open_env (open_env_shift_from k η) (logic_var_shift_from k v) =
  logic_var_shift_from k (logic_var_open_env η v).
Proof.
  destruct v as [n|x]; cbn [logic_var_shift_from logic_var_open_env].
  - destruct (decide (k <= n)) as [Hkn|Hkn].
    + assert (Hkey : open_env_shift_key_from k n = S n).
      { unfold open_env_shift_key_from.
        destruct (decide (n < k)) as [Hbad|_]; [lia|reflexivity]. }
      cbn [logic_var_open_env].
      pose proof (open_env_shift_from_lookup k η n) as Hlook.
      rewrite Hkey in Hlook. rewrite Hlook.
      destruct (η !! n); cbn [logic_var_shift_from].
      * reflexivity.
      * destruct (decide (k <= n)) as [_|Hbad]; [reflexivity|lia].
    + assert (Hnk : n < k) by lia.
      assert (Hkey : open_env_shift_key_from k n = n).
      { unfold open_env_shift_key_from.
        destruct (decide (n < k)) as [_|Hbad]; [reflexivity|lia]. }
      cbn [logic_var_open_env].
      pose proof (open_env_shift_from_lookup k η n) as Hlook.
      rewrite Hkey in Hlook. rewrite Hlook.
      destruct (η !! n); cbn [logic_var_shift_from].
      * reflexivity.
      * destruct (decide (k <= n)) as [Hbad|_]; [lia|reflexivity].
  - reflexivity.
Qed.

Definition lvars_shift_from (k : nat) (D : lvset) : lvset :=
  set_map (logic_var_shift_from k) D.

#[global] Instance shift_logic_var_inst : Shift logic_var :=
  logic_var_shift_from.

#[global] Instance shift_lvars_inst : Shift lvset :=
  lvars_shift_from.

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

Lemma lvars_shift_from_fv k D :
  lvars_fv (lvars_shift_from k D) = lvars_fv D.
Proof.
  induction D as [|v D Hfresh IH] using set_ind_L.
  - unfold lvars_shift_from. rewrite set_map_empty. reflexivity.
  - unfold lvars_shift_from in *.
    rewrite set_map_union_L, set_map_singleton_L.
    rewrite !lvars_fv_union, IH.
    destruct v as [n|x]; cbn [logic_var_shift_from].
    + destruct (decide (k <= n));
        rewrite !lvars_fv_singleton_bound; reflexivity.
    + rewrite !lvars_fv_singleton_free. reflexivity.
Qed.

Lemma lvars_shift_from_bv k D :
  lvars_bv (lvars_shift_from k D) =
    set_map (fun n => if decide (k <= n) then S n else n) (lvars_bv D).
Proof.
  apply set_eq. intros n.
  rewrite lvars_bv_elem.
  unfold lvars_shift_from.
  rewrite elem_of_map.
  split.
  - intros [v [Hv HvD]].
    destruct v as [m|x]; cbn [logic_var_shift_from] in Hv; try discriminate.
    destruct (decide (k <= m)) as [Hkm|Hkm].
    + inversion Hv. subst n.
      apply elem_of_map. exists m. split.
      * destruct (decide (k <= m)) as [_|Hbad]; [reflexivity|lia].
      * rewrite lvars_bv_elem. exact HvD.
    + inversion Hv. subst n.
      apply elem_of_map. exists m. split.
      * destruct (decide (k <= m)) as [Hbad|_]; [lia|reflexivity].
      * rewrite lvars_bv_elem. exact HvD.
  - intros Hn.
    apply elem_of_map in Hn as [m [Hn Hm]].
    rewrite lvars_bv_elem in Hm.
    exists (LVBound m). split.
    + cbn [logic_var_shift_from].
      destruct (decide (k <= m)); subst n; reflexivity.
    + exact Hm.
Qed.

Lemma lvars_shift_from_mono k D E :
  D ⊆ E ->
  lvars_shift_from k D ⊆ lvars_shift_from k E.
Proof.
  intros HDE v Hv.
  unfold lvars_shift_from in *.
  apply elem_of_map in Hv as [u [-> Hu]].
  apply elem_of_map. exists u. split; [reflexivity|].
  apply HDE. exact Hu.
Qed.

Lemma lvars_shift_from_union k D E :
  lvars_shift_from k (D ∪ E) =
  lvars_shift_from k D ∪ lvars_shift_from k E.
Proof.
  unfold lvars_shift_from. apply set_map_union_L.
Qed.

Lemma lvars_shift_from_below_id k D :
  (forall n, n ∈ lvars_bv D -> n < k) ->
  lvars_shift_from k D = D.
Proof.
  intros Hbelow.
  apply set_eq. intros v.
  split.
  - intros Hv.
    unfold lvars_shift_from in Hv.
    apply elem_of_map in Hv as [u [-> Hu]].
    destruct u as [n|a]; cbn [logic_var_shift_from].
    + destruct (decide (k <= n)) as [Hbad|_].
      * exfalso. pose proof (Hbelow n ltac:(apply lvars_bv_elem; exact Hu)).
        lia.
      * exact Hu.
    + exact Hu.
  - intros Hv.
    unfold lvars_shift_from.
    apply elem_of_map.
    exists v. split; [| exact Hv].
    destruct v as [n|a]; cbn [logic_var_shift_from].
    + destruct (decide (k <= n)) as [Hbad|_].
      * exfalso. pose proof (Hbelow n ltac:(apply lvars_bv_elem; exact Hv)).
        lia.
      * reflexivity.
    + reflexivity.
Qed.

Lemma lvars_open_env_shift_from k η D :
  lvars_open_env (open_env_shift_from k η) (lvars_shift_from k D) =
  lvars_shift_from k (lvars_open_env η D).
Proof.
  apply set_eq. intros z.
  unfold lvars_open_env, lvars_shift_from.
  rewrite !elem_of_map.
  split.
  - intros [u [Hz Hu]].
    apply elem_of_map in Hu as [v [Hu Hv]].
    exists (logic_var_open_env η v). split.
    + subst z u. apply logic_var_open_env_shift_from.
    + apply elem_of_map. exists v. split; [reflexivity|exact Hv].
  - intros [u [Hz Hu]].
    apply elem_of_map in Hu as [v [Hu Hv]].
    exists (logic_var_shift_from k v). split.
    + subst z u. symmetry. apply logic_var_open_env_shift_from.
    + apply elem_of_map. exists v. split; [reflexivity|exact Hv].
Qed.

Lemma open_env_shift_from_fresh_for_lvars k η D :
  open_env_fresh_for_lvars η D ->
  open_env_fresh_for_lvars (open_env_shift_from k η) (lvars_shift_from k D).
Proof.
  intros Hfresh j x Hjx Hbad.
  unfold open_env_shift_from in Hjx.
  apply lookup_kmap_Some in Hjx as [i [-> Hix]].
  2:{ apply open_env_shift_key_from_inj. }
  eapply Hfresh; [exact Hix|].
  replace (delete (open_env_shift_key_from k i) (open_env_shift_from k η)) with
    (open_env_shift_from k (delete i η)) in Hbad
    by (unfold open_env_shift_from;
        refine (@kmap_delete nat (gmap nat) _ _ _ _ _ _ _ _ _
          nat (gmap nat) _ _ _ _ _ _ _ _ _
          (open_env_shift_key_from k) _ atom η i);
        apply open_env_shift_key_from_inj).
  rewrite lvars_open_env_shift_from in Hbad.
  rewrite lvars_shift_from_fv in Hbad.
  exact Hbad.
Qed.

Lemma lvars_open_shift_from_under_gen j k x D :
  j <= k ->
  lvars_open (S k) x (lvars_shift_from j D) =
  lvars_shift_from j (lvars_open k x D).
Proof.
  intros Hjk.
  apply set_eq. intros z.
  rewrite !lvars_open_unfold.
  unfold set_swap, lvars_shift_from.
  rewrite !elem_of_map.
  split.
  - intros [u [Hz Hu]].
    apply elem_of_map in Hu as [v [Hu Hv]].
    exists (swap (LVBound k) (LVFree x) v). split.
    + subst z u.
      pose proof (logic_var_open_shift_from_under_gen j k x v Hjk) as Hop.
      rewrite !logic_var_open_unfold in Hop. exact Hop.
    + apply elem_of_map. exists v. split; [reflexivity|exact Hv].
  - intros [u [Hz Hu]].
    apply elem_of_map in Hu as [v [Hu Hv]].
    exists (logic_var_shift_from j v). split.
    + subst z u.
      pose proof (logic_var_open_shift_from_under_gen j k x v Hjk) as Hop.
      rewrite !logic_var_open_unfold in Hop. symmetry. exact Hop.
    + apply elem_of_map. exists v. split; [reflexivity|exact Hv].
Qed.

Lemma lvars_open_shift_from_under j k x D :
  j <= k ->
  lvars_open (S (S k)) x (lvars_shift_from (S j) D) =
  lvars_shift_from (S j) (lvars_open (S k) x D).
Proof.
  intros Hjk. apply lvars_open_shift_from_under_gen. lia.
Qed.

Lemma lvars_bv_shift_from_under_iff j k D :
  j <= k ->
  S (S k) ∈ lvars_bv (lvars_shift_from (S j) D) <->
  S k ∈ lvars_bv D.
Proof.
  intros Hjk.
  rewrite !lvars_bv_elem.
  unfold lvars_shift_from.
  rewrite elem_of_map.
  split.
  - intros [v [Hv HvD]].
    destruct v as [n|y]; cbn [logic_var_shift_from] in Hv; try discriminate.
    destruct (decide (S j <= n)) as [Hjn|Hjn].
    + inversion Hv. subst n. exact HvD.
    + inversion Hv. subst n. lia.
  - intros HvD.
    exists (LVBound (S k)). split.
    + cbn [logic_var_shift_from].
      destruct (decide (S j <= S k)) as [_|Hbad]; [reflexivity|lia].
    + exact HvD.
Qed.

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
