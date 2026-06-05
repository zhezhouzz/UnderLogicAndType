(** * Binder-depth shifts for logic variables and lvar sets *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From ContextBase Require Export LogicVarOpenEnv.

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
    unfold swap, logic_var_shift_from;
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

(** ** Lvar-set scoping *)

Definition lvar_wf_at (d : nat) (D : aset) (v : logic_var) : Prop :=
  match v with
  | LVFree x => x ∈ D
  | LVBound k => k < d
  end.

Definition lvars_wf_at (d : nat) (D : aset) (L : lvset) : Prop :=
  forall v, v ∈ L -> lvar_wf_at d D v.

Definition lvars_lc_at (d : nat) (L : lvset) : Prop :=
  forall k, k ∈ lvars_bv L -> k < d.

Lemma lvars_wf_at_mono d D E L :
  D ⊆ E ->
  lvars_wf_at d D L ->
  lvars_wf_at d E L.
Proof.
  intros HDE Hwf [k|x] Hin; cbn [lvar_wf_at] in *.
  - exact (Hwf (LVBound k) Hin).
  - apply HDE. exact (Hwf (LVFree x) Hin).
Qed.

Lemma lvars_wf_at_lc d D L :
  lvars_wf_at d D L ->
  lvars_lc_at d L.
Proof.
  intros Hwf k Hk.
  rewrite lvars_bv_elem in Hk.
  exact (Hwf (LVBound k) Hk).
Qed.

Lemma lvars_wf_at_fv_subset d D L :
  lvars_wf_at d D L ->
  lvars_fv L ⊆ D.
Proof.
  intros Hwf x Hx.
  apply lvars_fv_elem in Hx.
  exact (Hwf (LVFree x) Hx).
Qed.

Lemma lvars_wf_at_drop_fresh d D x L :
  x ∉ lvars_fv L ->
  lvars_wf_at d (D ∪ {[x]}) L ->
  lvars_wf_at d D L.
Proof.
  intros Hfresh Hwf [k|y] Hy; cbn [lvar_wf_at].
  - exact (Hwf (LVBound k) Hy).
  - assert (y ∈ D ∪ {[x]}) as HyD by exact (Hwf (LVFree y) Hy).
    apply elem_of_union in HyD as [HyD | Hyx]; [exact HyD |].
    rewrite elem_of_singleton in Hyx. subst y.
    exfalso. apply Hfresh. apply lvars_fv_elem. exact Hy.
Qed.

Lemma lvars_wf_at_open_body D L x :
  x ∉ D ->
  lvars_wf_at 1 D L ->
  lvars_wf_at 0 (D ∪ {[x]}) (lvars_open 0 x L).
Proof.
  intros Hx Hwf v Hv.
  rewrite set_swap_elem in Hv.
  destruct v as [k|y]; cbn [lvar_wf_at].
  - destruct k as [|k].
    + rewrite swap_l in Hv.
      assert (LVFree x ∈ L) as Hxin by exact Hv.
      exfalso. apply Hx. exact (Hwf (LVFree x) Hxin).
    + rewrite swap_fresh in Hv by congruence.
      specialize (Hwf (LVBound (S k)) Hv). cbn [lvar_wf_at] in Hwf.
      lia.
  - destruct (decide (x = y)) as [->|Hxy].
    + set_solver.
    + rewrite swap_fresh in Hv by congruence.
      apply elem_of_union. left. exact (Hwf (LVFree y) Hv).
Qed.

Lemma lvars_wf_at_open_at d D L x :
  x ∉ D ->
  lvars_wf_at (S d) D L ->
  lvars_wf_at d (D ∪ {[x]}) (lvars_open d x L).
Proof.
  intros Hx Hwf v Hv.
  rewrite set_swap_elem in Hv.
  destruct v as [k|y]; cbn [lvar_wf_at].
  - destruct (decide (k = d)) as [->|Hkd].
    + rewrite swap_l in Hv.
      exfalso. apply Hx. exact (Hwf (LVFree x) Hv).
    + rewrite swap_fresh in Hv by congruence.
      specialize (Hwf (LVBound k) Hv). cbn [lvar_wf_at] in Hwf.
      lia.
  - destruct (decide (x = y)) as [->|Hxy].
    + apply elem_of_union_r. set_solver.
    + rewrite swap_fresh in Hv by congruence.
      apply elem_of_union_l. exact (Hwf (LVFree y) Hv).
Qed.

Lemma lvars_wf_at_shift d D L k :
  d <= k ->
  lvars_wf_at d D L ->
  lvars_wf_at d D (lvars_shift_from k L).
Proof.
  intros Hdk Hwf v Hv.
  unfold lvars_shift_from in Hv.
  apply elem_of_map in Hv as [u [-> Hu]].
  destruct u as [n|x]; cbn [logic_var_shift_from lvar_wf_at].
  - destruct (decide (k <= n)) as [Hkn|Hkn].
    + specialize (Hwf (LVBound n) Hu). cbn [lvar_wf_at] in Hwf. lia.
    + exact (Hwf (LVBound n) Hu).
  - exact (Hwf (LVFree x) Hu).
Qed.

Definition logic_var_at_depth (d : nat) (v : logic_var) : option logic_var :=
  match v with
  | LVFree x => Some (LVFree x)
  | LVBound n =>
      if decide (d <= n) then Some (LVBound (n - d)) else None
  end.

Definition lvars_at_depth (d : nat) (D : lvset) : lvset :=
  set_fold (fun v acc =>
    match logic_var_at_depth d v with
    | Some u => {[u]} ∪ acc
    | None => acc
    end) ∅ D.

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

Lemma lvars_shift_from_difference_of_atoms k (D : lvset) (X : aset) :
  lvars_shift_from k (D ∖ lvars_of_atoms X) =
  lvars_shift_from k D ∖ lvars_of_atoms X.
Proof.
  apply set_eq. intros v.
  split.
  - intros Hv.
    unfold lvars_shift_from in Hv |- *.
    apply elem_of_map in Hv as [u [-> Hu]].
    apply elem_of_difference in Hu as [HuD HuX].
    apply elem_of_difference. split.
    + apply elem_of_map. exists u. split; [reflexivity|exact HuD].
    + intros Hbad. apply HuX.
      unfold lvars_of_atoms in Hbad |- *.
      apply elem_of_map in Hbad as [a [Ha HaX]].
      destruct u as [n|x]; cbn [logic_var_shift_from] in Ha.
      * destruct (decide (k <= n)); discriminate.
      * inversion Ha. subst x.
        apply elem_of_map. exists a. split; [reflexivity|exact HaX].
  - intros Hv.
    unfold lvars_shift_from in Hv |- *.
    apply elem_of_difference in Hv as [HvD HvX].
    apply elem_of_map in HvD as [u [-> HuD]].
    apply elem_of_map. exists u. split; [reflexivity|].
    apply elem_of_difference. split; [exact HuD|].
    intros Hbad. apply HvX.
    unfold lvars_of_atoms in Hbad |- *.
    apply elem_of_map in Hbad as [a [Ha HaX]].
    destruct u as [n|x]; cbn [logic_var_shift_from] in Ha.
    + discriminate.
    + inversion Ha. subst x.
      apply elem_of_map. exists a. split; [reflexivity|exact HaX].
Qed.

Lemma lvars_at_depth_elem d D u :
  u ∈ lvars_at_depth d D <->
  exists v, v ∈ D /\ logic_var_at_depth d v = Some u.
Proof.
  unfold lvars_at_depth.
  refine (set_fold_ind_L
    (fun acc D => forall u, u ∈ acc <->
      exists v, v ∈ D /\ logic_var_at_depth d v = Some u)
    (fun v acc =>
      match logic_var_at_depth d v with
      | Some u => {[u]} ∪ acc
      | None => acc
      end) ∅ _ _ D u).
  - intros y. better_set_solver.
  - intros v D' acc Hfresh IH z.
    destruct (logic_var_at_depth d v) as [a|] eqn:Hv.
    + pose proof (IH z) as Hz. split.
      * intros Hx.
        apply elem_of_union in Hx as [Hx|Hx].
        -- apply elem_of_singleton in Hx. subst z.
           exists v. split; [better_set_solver | exact Hv].
        -- apply Hz in Hx as [w [Hw Hwx]].
           exists w. split; [better_set_solver | exact Hwx].
      * intros [w [Hw Hwx]].
        apply elem_of_union.
        apply elem_of_union in Hw as [Hw|Hw].
        -- apply elem_of_singleton in Hw. subst w.
           rewrite Hv in Hwx. inversion Hwx. subst z.
           left. better_set_solver.
        -- right. apply Hz. exists w. split; [exact Hw | exact Hwx].
    + pose proof (IH z) as Hz. split.
      * intros Hx.
        apply Hz in Hx as [w [Hw Hwx]].
        exists w. split; [better_set_solver | exact Hwx].
      * intros [w [Hw Hwx]].
        apply elem_of_union in Hw as [Hw|Hw].
        -- apply elem_of_singleton in Hw. subst w.
           rewrite Hv in Hwx. discriminate.
        -- apply Hz. exists w. split; [exact Hw | exact Hwx].
Qed.

Lemma lvars_at_depth_0 D :
  lvars_at_depth 0 D = D.
Proof.
  apply set_eq. intros u.
  rewrite lvars_at_depth_elem.
  split.
  - intros [v [Hv Hvu]].
    destruct v as [n|x]; cbn [logic_var_at_depth] in Hvu.
    + destruct (decide (0 <= n)); inversion Hvu. subst u.
      replace (n - 0) with n by lia. exact Hv.
    + inversion Hvu. subst u. exact Hv.
  - intros Hu.
    exists u. split; [exact Hu|].
    destruct u as [n|x]; cbn [logic_var_at_depth].
    + rewrite decide_True by lia. replace (n - 0) with n by lia. reflexivity.
    + reflexivity.
Qed.

Lemma lvars_at_depth_empty d :
  lvars_at_depth d ∅ = ∅.
Proof.
  apply set_eq. intros u. rewrite lvars_at_depth_elem. better_set_solver.
Qed.

Lemma lvars_at_depth_union d D E :
  lvars_at_depth d (D ∪ E) =
  lvars_at_depth d D ∪ lvars_at_depth d E.
Proof.
  apply set_eq. intros u.
  rewrite elem_of_union, !lvars_at_depth_elem.
  split.
  - intros [v [Hv Hvu]].
    apply elem_of_union in Hv as [Hv|Hv].
    + left. exists v. split; [exact Hv | exact Hvu].
    + right. exists v. split; [exact Hv | exact Hvu].
  - intros Hu.
    destruct Hu as [[v [Hv Hvu]]|[v [Hv Hvu]]].
    + exists v. split; [better_set_solver | exact Hvu].
    + exists v. split; [better_set_solver | exact Hvu].
Qed.

Lemma lvars_at_depth_singleton_free d x :
  lvars_at_depth d ({[LVFree x]} : lvset) = {[LVFree x]}.
Proof.
  apply set_eq. intros u. rewrite lvars_at_depth_elem.
  split.
  - intros [v [Hv Hvu]].
    rewrite elem_of_singleton in Hv. subst v.
    inversion Hvu. subst u. better_set_solver.
  - intros Hu.
    rewrite elem_of_singleton in Hu. subst u.
    exists (LVFree x). split; [better_set_solver | reflexivity].
Qed.

Lemma lvars_at_depth_singleton_bound0_succ d :
  lvars_at_depth (S d) ({[LVBound 0]} : lvset) = ∅.
Proof.
  apply set_eq. intros u.
  rewrite lvars_at_depth_elem.
  split.
  - intros [v [Hv Hvu]].
    rewrite elem_of_singleton in Hv. subst v.
    cbn [logic_var_at_depth] in Hvu.
    destruct (decide (S d <= 0)); [lia|discriminate].
  - better_set_solver.
Qed.

Lemma lvars_open0_difference_subset_depth1
    (D L : lvset) y :
  lc_lvars D ->
  LVFree y ∉ D ->
  lvars_at_depth 1 L ⊆ D ->
  lvars_open 0 y L ∖ {[LVFree y]} ⊆ lvars_at_depth 1 L.
Proof.
  intros Hlc HyD Hdepth u Hu.
  apply elem_of_difference in Hu as [Hu Hyu].
  apply elem_of_set_swap in Hu.
  change (swap (LVBound 0) (LVFree y) u ∈ L) with
    (logic_var_open 0 y u ∈ L) in Hu.
  destruct u as [k|z].
  - destruct k as [|k].
    + unfold swap in Hu.
      destruct (decide (LVBound 0 = LVBound 0)) as [_|Hbad]; [|congruence].
      exfalso. apply HyD.
      apply Hdepth.
      apply lvars_at_depth_elem.
      exists (LVFree y). split; [exact Hu|reflexivity].
    + unfold swap in Hu.
      destruct (decide (LVBound (S k) = LVBound 0)) as [Hbad|_];
        [inversion Hbad|].
      destruct (decide (LVBound (S k) = LVFree y)) as [Hbad|_];
          [discriminate|].
      assert (Hbad : LVBound k ∈ D).
      {
        apply Hdepth.
        apply lvars_at_depth_elem.
        exists (LVBound (S k)). split; [exact Hu|].
        cbn [logic_var_at_depth].
        rewrite decide_True by lia.
        replace (S k - 1) with k by lia.
        reflexivity.
      }
      exfalso. exact (Hlc (LVBound k) Hbad).
  - destruct (decide (z = y)) as [->|Hzy].
    + exfalso. apply Hyu. set_solver.
    + unfold swap in Hu.
      destruct (decide (LVFree z = LVBound 0)) as [Hbad|_];
        [discriminate|].
      destruct (decide (LVFree z = LVFree y)) as [Hbad|_];
        [inversion Hbad; congruence|].
      apply lvars_at_depth_elem.
      exists (LVFree z). split; [exact Hu|reflexivity].
Qed.

Lemma lvars_at_depth_mono d D E :
  D ⊆ E ->
  lvars_at_depth d D ⊆ lvars_at_depth d E.
Proof.
  intros Hsub u Hu.
  apply lvars_at_depth_elem in Hu as [v [Hv Hvu]].
  apply lvars_at_depth_elem.
  exists v. split; [better_set_solver | exact Hvu].
Qed.

Lemma lvars_at_depth_difference_subset d D E :
  lvars_at_depth d (D ∖ E) ⊆ lvars_at_depth d D.
Proof.
  apply lvars_at_depth_mono. better_set_solver.
Qed.

Lemma lvars_at_depth_difference_of_atoms d D X :
  lvars_at_depth d (D ∖ lvars_of_atoms X) =
  lvars_at_depth d D ∖ lvars_of_atoms X.
Proof.
  apply set_eq. intros u.
  split.
  - intros Hu0.
    apply lvars_at_depth_elem in Hu0 as [v [Hv Hvu]].
    apply elem_of_difference in Hv as [Hv Hu].
    apply elem_of_difference. split.
    + apply lvars_at_depth_elem. eexists. split; [exact Hv | exact Hvu].
    + destruct v as [n|x]; cbn [logic_var_at_depth] in Hvu.
      * destruct (decide (d <= n)); inversion Hvu. subst u.
        intros Hbad. unfold lvars_of_atoms in Hbad.
        apply elem_of_map in Hbad as [a [Hbad _]]. discriminate.
      * inversion Hvu. subst u.
        intros Hbad. apply Hu. exact Hbad.
  - intros Hu0.
    apply elem_of_difference in Hu0 as [Hu0 Hu].
    apply lvars_at_depth_elem in Hu0 as [v [Hv Hvu]].
    apply lvars_at_depth_elem. eexists. split; [|exact Hvu].
    apply elem_of_difference. split; [exact Hv|].
    intros HvX. apply Hu.
    destruct v as [n|x]; cbn [logic_var_at_depth] in Hvu.
    + destruct (decide (d <= n)); inversion Hvu. subst u.
      unfold lvars_of_atoms in HvX.
      apply elem_of_map in HvX as [a [HvX _]]. discriminate.
    + inversion Hvu. subst u. exact HvX.
Qed.

Lemma logic_var_at_depth_open d k x v :
  logic_var_at_depth d (logic_var_open (d + k) x v) =
  option_map (logic_var_open k x) (logic_var_at_depth d v).
Proof.
  destruct v as [n|y]; cbn [logic_var_at_depth option_map].
  - destruct (decide (d + k = n)) as [Heq|Hneq].
    + subst n.
      unfold swap.
      destruct (decide (LVBound (d + k) = LVBound (d + k))) as [_|Hbad];
        [|congruence].
      cbn [logic_var_at_depth].
      destruct (decide (d <= d + k)) as [_|Hbad]; [|lia].
      cbn [option_map].
      unfold swap.
      replace (d + k - d) with k by lia.
      destruct (decide (LVBound k = LVBound k)) as [_|Hbad]; [reflexivity|congruence].
    + unfold swap.
      destruct (decide (LVBound n = LVBound (d + k))) as [Heq|_];
        [inversion Heq; lia|].
      destruct (decide (LVBound n = LVFree x)) as [Hbad|_]; [discriminate|].
      cbn [logic_var_at_depth].
      destruct (decide (d <= n)) as [Hdn|Hdn].
      * cbn [option_map].
        unfold swap.
        destruct (decide (LVBound (n - d) = LVBound k)) as [Heq|_].
        -- inversion Heq. lia.
        -- destruct (decide (LVBound (n - d) = LVFree x)) as [Hbad|_];
             [discriminate|reflexivity].
      * reflexivity.
  - destruct (decide (x = y)) as [->|Hxy].
    + unfold swap.
      destruct (decide (LVFree y = LVBound (d + k))) as [Hbad|_];
        [discriminate|].
      destruct (decide (LVFree y = LVFree y)) as [_|Hbad]; [|congruence].
      cbn [logic_var_at_depth option_map].
      destruct (decide (d <= d + k)) as [_|Hbad]; [|lia].
      unfold swap.
      replace (d + k - d) with k by lia.
      destruct (decide (LVFree y = LVBound k)) as [Hbad|_]; [discriminate|].
      destruct (decide (LVFree y = LVFree y)) as [_|Hbad]; [reflexivity|congruence].
    + unfold swap.
      destruct (decide (LVFree y = LVBound (d + k))) as [Hbad|_];
        [discriminate|].
      destruct (decide (LVFree y = LVFree x)) as [Heq|_];
        [inversion Heq; congruence|].
      cbn [logic_var_at_depth option_map].
      unfold swap.
      destruct (decide (LVFree y = LVBound k)) as [Hbad|_]; [discriminate|].
      destruct (decide (LVFree y = LVFree x)) as [Heq|_];
        [inversion Heq; congruence|reflexivity].
Qed.

Lemma lvars_at_depth_open d k x D :
  lvars_at_depth d (lvars_open (d + k) x D) =
  lvars_open k x (lvars_at_depth d D).
Proof.
  apply set_eq. intros u.
  split.
  - intros Hu.
    apply lvars_at_depth_elem in Hu as [v [Hv Hvu]].
    apply elem_of_set_swap in Hv.
    change (swap (LVBound (d + k)) (LVFree x) v ∈ D) with
      (logic_var_open (d + k) x v ∈ D) in Hv.
    apply elem_of_set_swap.
    change (swap (LVBound k) (LVFree x) u ∈ lvars_at_depth d D) with
      (logic_var_open k x u ∈ lvars_at_depth d D).
    apply lvars_at_depth_elem. exists (logic_var_open (d + k) x v).
    split; [exact Hv|].
    rewrite logic_var_at_depth_open, Hvu. reflexivity.
  - intros Hu.
    apply elem_of_set_swap in Hu.
    change (swap (LVBound k) (LVFree x) u ∈ lvars_at_depth d D) with
      (logic_var_open k x u ∈ lvars_at_depth d D) in Hu.
    apply lvars_at_depth_elem in Hu as [v [Hv Hvu]].
    apply lvars_at_depth_elem.
    exists (logic_var_open (d + k) x v).
    split.
    + apply elem_of_set_swap.
      change (swap (LVBound (d + k)) (LVFree x)
        (logic_var_open (d + k) x v) ∈ D) with
        (logic_var_open (d + k) x (logic_var_open (d + k) x v) ∈ D).
      rewrite logic_var_open_involutive. exact Hv.
    + rewrite logic_var_at_depth_open, Hvu.
      cbn [option_map]. rewrite logic_var_open_involutive. reflexivity.
Qed.

Lemma lvars_fv_lvars_at_depth d D :
  lvars_fv (lvars_at_depth d D) = lvars_fv D.
Proof.
  apply set_eq. intros x.
  rewrite !lvars_fv_elem, lvars_at_depth_elem.
  split.
  - intros [v [Hv Hdepth]].
    destruct v as [k|y]; cbn [logic_var_at_depth] in Hdepth.
    + destruct (decide (d <= k)); discriminate.
    + inversion Hdepth. subst. exact Hv.
  - intros Hx.
    exists (LVFree x). split; [exact Hx | reflexivity].
Qed.

Lemma lvars_at_depth_free_elem d D x :
  LVFree x ∈ lvars_at_depth d D <-> LVFree x ∈ D.
Proof.
  rewrite lvars_at_depth_elem.
  split.
  - intros [v [Hv Hdepth]].
    destruct v as [n|y]; cbn [logic_var_at_depth] in Hdepth.
    + destruct (decide (d <= n)); discriminate.
    + inversion Hdepth. subst. exact Hv.
  - intros Hx.
    exists (LVFree x). split; [exact Hx | reflexivity].
Qed.

Lemma lvars_at_depth_depth d c D :
  lvars_at_depth d (lvars_at_depth c D) = lvars_at_depth (c + d) D.
Proof.
  apply set_eq. intros u.
  rewrite (lvars_at_depth_elem d (lvars_at_depth c D) u).
  rewrite (lvars_at_depth_elem (c + d) D u).
  split.
  - intros [v [Hv Hvu]].
    apply lvars_at_depth_elem in Hv as [w [Hw Hwv]].
    exists w. split; [exact Hw|].
    destruct w as [n|x].
    + cbn [logic_var_at_depth] in Hwv.
      destruct (decide (c <= n)) as [Hcn|Hcn]; [|discriminate].
      inversion Hwv. subst v.
      cbn [logic_var_at_depth] in Hvu.
      destruct (decide (d <= n - c)) as [Hdn|Hdn]; [|discriminate].
      inversion Hvu. subst u.
      cbn [logic_var_at_depth].
      destruct (decide (c + d <= n)) as [_|Hbad]; [|lia].
      replace (n - (c + d)) with (n - c - d) by lia.
      reflexivity.
    + cbn [logic_var_at_depth] in Hwv. inversion Hwv. subst v.
      cbn [logic_var_at_depth] in Hvu.
      inversion Hvu. subst u. reflexivity.
  - intros [v [Hv Hvu]].
    destruct v as [n|x].
    + cbn [logic_var_at_depth] in Hvu.
      destruct (decide (c + d <= n)) as [Hcdn|Hcdn]; [|discriminate].
      inversion Hvu. subst u.
      exists (LVBound (n - c)). split.
      * apply lvars_at_depth_elem. exists (LVBound n). split; [exact Hv|].
        cbn [logic_var_at_depth].
        destruct (decide (c <= n)) as [_|Hbad]; [reflexivity|lia].
      * cbn [logic_var_at_depth].
        destruct (decide (d <= n - c)) as [_|Hbad]; [|lia].
        replace (n - c - d) with (n - (c + d)) by lia.
        reflexivity.
    + cbn [logic_var_at_depth] in Hvu. inversion Hvu. subst u.
      exists (LVFree x). split.
      * apply lvars_at_depth_elem. exists (LVFree x). split; [exact Hv|reflexivity].
      * reflexivity.
Qed.

Lemma lvars_at_depth_succ_body d D :
  lvars_at_depth d D ⊆
  lvars_shift_from 0 (lvars_at_depth (S d) D) ∪ {[LVBound 0]}.
Proof.
  intros u Hu.
  apply lvars_at_depth_elem in Hu as [v [Hv Hdepth]].
  destruct v as [n|x]; cbn [logic_var_at_depth] in Hdepth.
  - destruct (decide (d <= n)) as [Hdn|Hdn]; [|discriminate].
    inversion Hdepth; subst u.
    destruct (decide (S d <= n)) as [Hsdn|Hsdn].
    + apply elem_of_union_l.
      unfold lvars_shift_from. apply elem_of_map.
      exists (LVBound (n - S d)). split.
      * cbn [logic_var_shift_from].
        destruct (decide (0 <= n - S d)) as [_|Hbad]; [|lia].
        f_equal. lia.
      * apply lvars_at_depth_elem.
        exists (LVBound n). split; [exact Hv |].
        cbn [logic_var_at_depth].
        destruct (decide (S d <= n)) as [_|Hbad]; [reflexivity | lia].
    + apply elem_of_union_r.
      assert (n = d) by lia. subst n.
      replace (d - d) with 0 by lia.
      apply elem_of_singleton. reflexivity.
  - inversion Hdepth; subst u.
    apply elem_of_union_l.
    unfold lvars_shift_from. apply elem_of_map.
    exists (LVFree x). split; [reflexivity |].
    apply lvars_at_depth_elem.
    exists (LVFree x). split; [exact Hv | reflexivity].
Qed.

Lemma lvars_bv_at_depth_succ_empty_of_open0 x D :
  lvars_bv (lvars_open 0 x D) = ∅ ->
  lvars_bv (lvars_at_depth 1 D) = ∅.
Proof.
  intros Hopen.
  apply set_eq. intros n.
  rewrite elem_of_empty.
  split; [|better_set_solver].
  intros Hn.
  rewrite lvars_bv_elem in Hn.
  apply lvars_at_depth_elem in Hn as [v [Hv Hdepth]].
  destruct v as [m|y]; cbn [logic_var_at_depth] in Hdepth; [|discriminate].
  destruct (decide (1 <= m)) as [Hm|Hm]; [|discriminate].
  inversion Hdepth. subst n.
  assert (LVBound m ∈ lvars_open 0 x D) as Hopened.
  {
    unfold set_swap.
    apply elem_of_map. exists (LVBound m). split; [|exact Hv].
    symmetry. apply swap_fresh.
    - intros Heq. inversion Heq. lia.
    - discriminate.
  }
  assert (m ∈ lvars_bv (lvars_open 0 x D)).
  { rewrite lvars_bv_elem. exact Hopened. }
  change (lvars_bv (set_swap (LVBound 0) (LVFree x) D) = ∅) in Hopen.
  change (m ∈ lvars_bv (set_swap (LVBound 0) (LVFree x) D)) in H.
  rewrite Hopen in H. better_set_solver.
Qed.

Lemma logic_var_at_depth_shift_from d k v :
  logic_var_at_depth d (logic_var_shift_from (d + k) v) =
  option_map (logic_var_shift_from k) (logic_var_at_depth d v).
Proof.
  destruct v as [n|x]; cbn [logic_var_shift_from logic_var_at_depth].
  - destruct (decide (d <= n)) as [Hdn|Hdn].
    + destruct (decide (d + k <= n)) as [Hdkn|Hdkn].
      * destruct (decide (d <= S n)) as [_|Hbad]; [|lia].
        cbn [option_map logic_var_shift_from].
        destruct (decide (k <= n - d)) as [_|Hbad]; [|lia].
        cbn [logic_var_at_depth].
        destruct (decide (d <= S n)) as [_|Hbad]; [|lia].
        replace (S n - d) with (S (n - d)) by lia.
        reflexivity.
      * destruct (decide (d <= n)) as [_|Hbad]; [|lia].
        cbn [option_map logic_var_shift_from].
        destruct (decide (k <= n - d)) as [Hbad|_]; [lia|].
        cbn [logic_var_at_depth].
        destruct (decide (d <= n)) as [_|Hbad]; [reflexivity|lia].
    + destruct (decide (d + k <= n)) as [Hdkn|_]; [lia|].
      destruct (decide (d <= n)) as [Hbad|_]; [lia|].
      cbn [logic_var_at_depth option_map].
      destruct (decide (d <= n)) as [Hbad|_]; [lia|reflexivity].
  - reflexivity.
Qed.

Lemma lvars_at_depth_shift_from d k D :
  lvars_at_depth d (lvars_shift_from (d + k) D) =
  lvars_shift_from k (lvars_at_depth d D).
Proof.
  apply set_eq. intros u.
  split.
  - intros Hu.
    apply lvars_at_depth_elem in Hu as [v [Hv Hvu]].
    unfold lvars_shift_from in Hv.
    apply elem_of_map in Hv as [w [-> Hw]].
    rewrite logic_var_at_depth_shift_from in Hvu.
    destruct (logic_var_at_depth d w) as [w'|] eqn:Hw'; [|discriminate].
    inversion Hvu. subst u.
    unfold lvars_shift_from. apply elem_of_map.
    exists w'. split; [reflexivity|].
    apply lvars_at_depth_elem. exists w. split; [exact Hw|exact Hw'].
  - intros Hu.
    unfold lvars_shift_from in Hu.
    apply elem_of_map in Hu as [v [-> Hv]].
    apply lvars_at_depth_elem in Hv as [w [Hw Hwv]].
    apply lvars_at_depth_elem.
    exists (logic_var_shift_from (d + k) w). split.
    + unfold lvars_shift_from. apply elem_of_map. exists w.
      split; [reflexivity|exact Hw].
    + rewrite logic_var_at_depth_shift_from, Hwv. reflexivity.
Qed.

Lemma logic_var_at_depth_shift_under d k v :
  k <= d ->
  logic_var_at_depth (S d) (logic_var_shift_from k v) =
  logic_var_at_depth d v.
Proof.
  intros Hkd.
  destruct v as [n|x]; cbn [logic_var_shift_from logic_var_at_depth].
  - destruct (decide (k <= n)) as [Hkn|Hkn].
    + cbn [logic_var_at_depth].
      destruct (decide (S d <= S n)) as [Hsdn|Hsdn].
      * destruct (decide (d <= n)) as [_|Hbad]; [|lia].
        replace (S n - S d) with (n - d) by lia. reflexivity.
      * destruct (decide (d <= n)) as [Hbad|_]; [lia|reflexivity].
    + cbn [logic_var_at_depth].
      destruct (decide (S d <= n)) as [Hsdn|Hsdn].
      * lia.
      * destruct (decide (d <= n)) as [Hdn|Hdn].
        -- assert (n = d) by lia. subst n. lia.
        -- reflexivity.
  - reflexivity.
Qed.

Lemma lvars_at_depth_shift_under d k D :
  k <= d ->
  lvars_at_depth (S d) (lvars_shift_from k D) =
  lvars_at_depth d D.
Proof.
  intros Hkd. apply set_eq. intros u.
  split.
  - intros Hu.
    apply lvars_at_depth_elem in Hu as [v [Hv Hvu]].
    unfold lvars_shift_from in Hv.
    apply elem_of_map in Hv as [w [-> Hw]].
    rewrite logic_var_at_depth_shift_under in Hvu by exact Hkd.
    apply lvars_at_depth_elem. exists w. split; [exact Hw | exact Hvu].
  - intros Hu.
    apply lvars_at_depth_elem in Hu as [v [Hv Hvu]].
    apply lvars_at_depth_elem.
    exists (logic_var_shift_from k v). split.
    + unfold lvars_shift_from. apply elem_of_map. exists v.
      split; [reflexivity | exact Hv].
    + rewrite logic_var_at_depth_shift_under by exact Hkd. exact Hvu.
Qed.

Lemma lvars_shift_from_succ_body_union D1 D1' D2 D2' :
  D1 ⊆ lvars_shift_from 0 D1' ∪ {[LVBound 0]} ->
  D2 ⊆ lvars_shift_from 0 D2' ∪ {[LVBound 0]} ->
  D1 ∪ D2 ⊆ lvars_shift_from 0 (D1' ∪ D2') ∪ {[LVBound 0]}.
Proof.
  intros H1 H2 u Hu.
  apply elem_of_union in Hu as [Hu | Hu].
  - specialize (H1 u Hu).
    apply elem_of_union in H1 as [Hshift | Hzero].
    + apply elem_of_union_l.
      eapply lvars_shift_from_mono; [|exact Hshift]. better_set_solver.
    + apply elem_of_union_r. exact Hzero.
  - specialize (H2 u Hu).
    apply elem_of_union in H2 as [Hshift | Hzero].
    + apply elem_of_union_l.
      eapply lvars_shift_from_mono; [|exact Hshift]. better_set_solver.
    + apply elem_of_union_r. exact Hzero.
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

Lemma lvars_shift_from_lc_at_id k D :
  lvars_lc_at k D ->
  lvars_shift_from k D = D.
Proof.
  intros Hlc.
  apply lvars_shift_from_below_id. exact Hlc.
Qed.

Lemma lvars_open_shift_from_lc_at_fresh k x D :
  lvars_lc_at k D ->
  x ∉ lvars_fv D ->
  lvars_open k x (lvars_shift_from k D) = D.
Proof.
  intros Hlc Hx.
  rewrite lvars_shift_from_lc_at_id by exact Hlc.
  apply lvars_open_fresh_index.
  - intros Hk. specialize (Hlc k Hk). lia.
  - exact Hx.
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
  unfold set_swap, lvars_shift_from.
  rewrite !elem_of_map.
  split.
  - intros [u [Hz Hu]].
    apply elem_of_map in Hu as [v [Hu Hv]].
    exists (swap (LVBound k) (LVFree x) v). split.
    + subst z u.
      pose proof (logic_var_open_shift_from_under_gen j k x v Hjk) as Hop.
      exact Hop.
    + apply elem_of_map. exists v. split; [reflexivity|exact Hv].
  - intros [u [Hz Hu]].
    apply elem_of_map in Hu as [v [Hu Hv]].
    exists (logic_var_shift_from j v). split.
    + subst z u.
      pose proof (logic_var_open_shift_from_under_gen j k x v Hjk) as Hop.
      symmetry. exact Hop.
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
