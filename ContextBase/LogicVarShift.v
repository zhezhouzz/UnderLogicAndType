(** * Binder-depth shifts for logic variables and lvar sets *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From ContextBase Require Export LogicVarInterface.

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
