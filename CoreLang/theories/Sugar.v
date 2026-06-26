(** * CoreLang.Sugar

    Small derived forms used by examples.  The core syntax remains let-normal,
    with boolean-only matching.  The core language is deterministic; branching
    is ordinary boolean case analysis. *)

From CoreLang Require Export SmallStep OperationalProps LocallyNamelessProps.
From CoreLang Require Import BasicTypingProps.
From ContextBase Require Import Prelude.

Definition vtrue : value := vconst (cbool true).
Definition vfalse : value := vconst (cbool false).
Definition vnat (n : nat) : value := vconst (cnat n).

Fixpoint value_shift (k : nat) (v : value) : value :=
  match v with
  | vconst _ => v
  | vfvar _ => v
  | vbvar n =>
      match bool_decide (k <= n) with
      | true => vbvar (S n)
      | false => v
      end
  | vlam T e => vlam T (tm_shift (S k) e)
  | vfix T vf => vfix T (value_shift (S k) vf)
  end
with tm_shift (k : nat) (e : tm) : tm :=
  match e with
  | tret v => tret (value_shift k v)
  | tlete e1 e2 => tlete (tm_shift k e1) (tm_shift (S k) e2)
  | tprim op v => tprim op (value_shift k v)
  | tapp v1 v2 => tapp (value_shift k v1) (value_shift k v2)
  | tmatch v et ef =>
      tmatch (value_shift k v) (tm_shift k et) (tm_shift k ef)
  | tnode root lft rgt =>
      tnode (value_shift k root) (value_shift k lft) (value_shift k rgt)
	  | tmatchtree v el en =>
	      tmatchtree (value_shift k v) (tm_shift k el) (tm_shift (k + 3) en)
	  | tcons hd tl =>
	      tcons (value_shift k hd) (value_shift k tl)
	  | tmatchlist v en ec =>
	      tmatchlist (value_shift k v) (tm_shift k en) (tm_shift (k + 2) ec)
	  end.

#[global] Instance shift_value_inst : Shift value := value_shift.
#[global] Instance shift_tm_inst : Shift tm := tm_shift.
Arguments shift_value_inst /.
Arguments shift_tm_inst /.

Definition tapp_tm (ef : tm) (vx : value) : tm :=
  tlete ef (tapp (vbvar 0) (value_shift 0 vx)).

Notation "e '·ₜ' v" := (tapp_tm e v)
  (at level 40, left associativity,
   format "e  ·ₜ  v").

Notation "'↑{' k '}' v" := (value_shift k v)
  (at level 20, k constr, only printing,
   format "↑{ k }  v") : core_scope.
Notation "'↑{' k '}' e" := (tm_shift k e)
  (at level 20, k constr, only printing,
   format "↑{ k }  e") : core_scope.
Notation "v '↑'" := (value_shift 0 v)
  (at level 20, only printing,
   format "v  ↑") : core_scope.
Notation "e '↑'" := (tm_shift 0 e)
  (at level 20, only printing,
   format "e  ↑") : core_scope.

Lemma value_shift_fv k v :
  fv_value (value_shift k v) = fv_value v
with tm_shift_fv k e :
  fv_tm (tm_shift k e) = fv_tm e.
Proof.
  - destruct v; cbn [value_shift fv_value]; try reflexivity.
    + destruct (bool_decide (k <= n)); reflexivity.
    + apply tm_shift_fv.
    + apply value_shift_fv.
  - destruct e; cbn [tm_shift fv_tm]; rewrite ?value_shift_fv, ?tm_shift_fv; reflexivity.
Qed.

Lemma value_shift_swap_atom x y k v :
  value_shift k (value_swap_atom x y v) =
  value_swap_atom x y (value_shift k v)
with tm_shift_swap_atom x y k e :
  tm_shift k (tm_swap_atom x y e) =
  tm_swap_atom x y (tm_shift k e).
Proof.
  - destruct v; cbn [value_shift value_swap_atom]; try reflexivity.
    + destruct (bool_decide (k <= n)); reflexivity.
    + rewrite tm_shift_swap_atom. reflexivity.
    + rewrite value_shift_swap_atom. reflexivity.
  - destruct e; cbn [tm_shift tm_swap_atom];
      rewrite ?value_shift_swap_atom, ?tm_shift_swap_atom; reflexivity.
Qed.

Lemma value_tm_shift_open_fvar_mutual :
  (forall v k cutoff x,
      cutoff <= k ->
      open_value (S k) (vfvar x) (value_shift cutoff v) =
      value_shift cutoff (open_value k (vfvar x) v)) *
  (forall e k cutoff x,
      cutoff <= k ->
      open_tm (S k) (vfvar x) (tm_shift cutoff e) =
      tm_shift cutoff (open_tm k (vfvar x) e)).
Proof.
  apply value_tm_mutind; cbn [open_value open_tm value_shift tm_shift];
    intros; try reflexivity.
  - destruct (decide (k = n)) as [->|Hkn].
    + rewrite !bool_decide_eq_true_2 by lia.
      cbn [open_value].
      destruct (decide (S n = S n)) as [_|Hbad]; [|congruence].
      destruct (decide (n = n)) as [_|Hbad]; [reflexivity|congruence].
    + destruct (bool_decide (cutoff <= n)) eqn:Hcut.
      * apply bool_decide_eq_true_1 in Hcut.
        cbn [open_value value_shift].
        rewrite bool_decide_eq_true_2 by exact Hcut.
        destruct (decide (S k = S n)) as [Hsk|_]; [inversion Hsk; congruence|].
        destruct (decide (k = n)) as [Hbad|_]; [congruence|reflexivity].
      * apply bool_decide_eq_false_1 in Hcut.
        cbn [open_value value_shift].
        rewrite bool_decide_eq_false_2 by exact Hcut.
        destruct (decide (S k = n)) as [Hsk|_]; [lia|].
        destruct (decide (k = n)) as [Hbad|_]; [congruence|reflexivity].
  - rewrite H by lia. reflexivity.
  - rewrite H by lia. reflexivity.
  - rewrite H by exact H0. reflexivity.
  - rewrite H by exact H1.
    rewrite H0 by lia. reflexivity.
  - rewrite H by exact H0. reflexivity.
  - rewrite H by exact H1.
    rewrite H0 by exact H1. reflexivity.
  - rewrite H by exact H2.
    rewrite H0 by exact H2.
    rewrite H1 by exact H2. reflexivity.
  - rewrite H by exact H2.
    rewrite H0 by exact H2.
    rewrite H1 by exact H2. reflexivity.
	  - rewrite H by exact H2.
	    rewrite H0 by exact H2.
	    replace (S k + 3) with (S (k + 3)) by lia.
	    rewrite H1 by lia. reflexivity.
  - rewrite H by exact H1.
    rewrite H0 by exact H1. reflexivity.
  - rewrite H by exact H2.
    rewrite H0 by exact H2.
    replace (S k + 2) with (S (k + 2)) by lia.
    rewrite H1 by lia. reflexivity.
Qed.

Lemma value_shift_open_value_fvar v k cutoff x :
  cutoff <= k ->
  open_value (S k) (vfvar x) (value_shift cutoff v) =
  value_shift cutoff (open_value k (vfvar x) v).
Proof. exact (fst value_tm_shift_open_fvar_mutual v k cutoff x). Qed.

Lemma tm_shift_open_tm_fvar e k cutoff x :
  cutoff <= k ->
  open_tm (S k) (vfvar x) (tm_shift cutoff e) =
  tm_shift cutoff (open_tm k (vfvar x) e).
Proof. exact (snd value_tm_shift_open_fvar_mutual e k cutoff x). Qed.

Lemma value_tm_shift_open_fvar_before_mutual :
  (forall v k cutoff x,
      k < cutoff ->
      open_value k (vfvar x) (value_shift cutoff v) =
      value_shift cutoff (open_value k (vfvar x) v)) *
  (forall e k cutoff x,
      k < cutoff ->
      open_tm k (vfvar x) (tm_shift cutoff e) =
      tm_shift cutoff (open_tm k (vfvar x) e)).
Proof.
  apply value_tm_mutind; cbn [open_value open_tm value_shift tm_shift];
    intros; try reflexivity.
  - destruct (bool_decide (cutoff <= n)) eqn:Hcut.
    + apply bool_decide_eq_true_1 in Hcut.
      cbn [open_value value_shift].
      destruct (decide (k = S n)) as [Hbad|_]; [lia|].
      destruct (decide (k = n)) as [->|Hkn]; [lia|].
      cbn [value_shift]. rewrite bool_decide_eq_true_2 by exact Hcut.
      reflexivity.
    + apply bool_decide_eq_false_1 in Hcut.
      cbn [open_value value_shift].
      destruct (decide (k = n)) as [->|Hkn]; [reflexivity|].
      cbn [value_shift]. rewrite bool_decide_eq_false_2 by exact Hcut.
      reflexivity.
  - rewrite H by lia. reflexivity.
  - rewrite H by lia. reflexivity.
  - rewrite H by exact H0. reflexivity.
  - rewrite H by exact H1.
    rewrite H0 by lia. reflexivity.
  - rewrite H by exact H0. reflexivity.
  - rewrite H by exact H1.
    rewrite H0 by exact H1. reflexivity.
  - rewrite H by exact H2.
    rewrite H0 by exact H2.
    rewrite H1 by exact H2. reflexivity.
  - rewrite H by exact H2.
    rewrite H0 by exact H2.
    rewrite H1 by exact H2. reflexivity.
	  - rewrite H by exact H2.
	    rewrite H0 by exact H2.
	    rewrite H1 by lia. reflexivity.
  - rewrite H by exact H1.
    rewrite H0 by exact H1. reflexivity.
  - rewrite H by exact H2.
    rewrite H0 by exact H2.
    rewrite H1 by lia. reflexivity.
Qed.

Lemma value_shift_open_value_fvar_before v k cutoff x :
  k < cutoff ->
  open_value k (vfvar x) (value_shift cutoff v) =
  value_shift cutoff (open_value k (vfvar x) v).
Proof. exact (fst value_tm_shift_open_fvar_before_mutual v k cutoff x). Qed.

Lemma tm_shift_open_tm_fvar_before e k cutoff x :
  k < cutoff ->
  open_tm k (vfvar x) (tm_shift cutoff e) =
  tm_shift cutoff (open_tm k (vfvar x) e).
Proof. exact (snd value_tm_shift_open_fvar_before_mutual e k cutoff x). Qed.

Lemma value_tm_shift_lc_id_mutual :
  (forall v, lc_value v -> forall k, value_shift k v = v) /\
  (forall e, lc_tm e -> forall k, tm_shift k e = e).
Proof.
  apply lc_mutind; cbn [value_shift tm_shift]; intros; try reflexivity.
  - f_equal.
    pose (x := fresh_for (L ∪ fv_tm e)).
    assert (HxL : x ∉ L) by (subst x; pose proof (fresh_for_not_in (L ∪ fv_tm e)); set_solver).
    assert (Hxfv : x ∉ fv_tm e) by (subst x; pose proof (fresh_for_not_in (L ∪ fv_tm e)); set_solver).
    assert (Hopen :
      open_tm 0 (vfvar x) (tm_shift (S k) e) =
      open_tm 0 (vfvar x) e).
    {
      rewrite tm_shift_open_tm_fvar_before by lia.
      rewrite H by exact HxL.
      reflexivity.
    }
    apply (f_equal (close_tm x 0)) in Hopen.
    rewrite !close_open_var_tm in Hopen by (rewrite ?tm_shift_fv; exact Hxfv).
    exact Hopen.
  - f_equal.
    pose (x := fresh_for (L ∪ fv_value vf)).
    assert (HxL : x ∉ L) by (subst x; pose proof (fresh_for_not_in (L ∪ fv_value vf)); set_solver).
    assert (Hxfv : x ∉ fv_value vf) by (subst x; pose proof (fresh_for_not_in (L ∪ fv_value vf)); set_solver).
    assert (Hopen :
      open_value 0 (vfvar x) (value_shift (S k) vf) =
      open_value 0 (vfvar x) vf).
    {
      rewrite value_shift_open_value_fvar_before by lia.
      rewrite H by exact HxL.
      reflexivity.
    }
    apply (f_equal (close_value x 0)) in Hopen.
    rewrite !close_open_var_value in Hopen by (rewrite ?value_shift_fv; exact Hxfv).
    exact Hopen.
  - rewrite H. reflexivity.
  - f_equal.
    + rewrite H. reflexivity.
    + pose (x := fresh_for (L ∪ fv_tm e2)).
      assert (HxL : x ∉ L) by (subst x; pose proof (fresh_for_not_in (L ∪ fv_tm e2)); set_solver).
      assert (Hxfv : x ∉ fv_tm e2) by (subst x; pose proof (fresh_for_not_in (L ∪ fv_tm e2)); set_solver).
      assert (Hopen :
        open_tm 0 (vfvar x) (tm_shift (S k) e2) =
        open_tm 0 (vfvar x) e2).
      {
        rewrite tm_shift_open_tm_fvar_before by lia.
        rewrite H0 by exact HxL.
        reflexivity.
      }
      apply (f_equal (close_tm x 0)) in Hopen.
      rewrite !close_open_var_tm in Hopen by (rewrite ?tm_shift_fv; exact Hxfv).
      exact Hopen.
  - rewrite H. reflexivity.
  - rewrite H, H0. reflexivity.
  - rewrite H, H0, H1. reflexivity.
  - rewrite H, H0, H1. reflexivity.
  - f_equal.
    + rewrite H. reflexivity.
    + rewrite H0. reflexivity.
    + pose (root := fresh_for (L ∪ fv_tm enode)).
      assert (Hroot : root ∉ L ∪ fv_tm enode)
        by (subst root; apply fresh_for_not_in).
      pose (left0 := fresh_for (L ∪ fv_tm enode ∪ {[root]})).
      assert (Hleft : left0 ∉ L ∪ fv_tm enode ∪ {[root]})
        by (subst left0; apply fresh_for_not_in).
      pose (right0 := fresh_for (L ∪ fv_tm enode ∪ {[root]} ∪ {[left0]})).
      assert (Hright : right0 ∉ L ∪ fv_tm enode ∪ {[root]} ∪ {[left0]})
        by (subst right0; apply fresh_for_not_in).
      assert (Hopen :
        open_tree_node_branch root left0 right0 (tm_shift (k + 3) enode) =
        open_tree_node_branch root left0 right0 enode).
      {
        unfold open_tree_node_branch, open_tree_node_branch_value.
        rewrite tm_shift_open_tm_fvar_before by lia.
        rewrite tm_shift_open_tm_fvar_before by lia.
        rewrite tm_shift_open_tm_fvar_before by lia.
        change (tm_shift (k + 3) (open_tree_node_branch root left0 right0 enode) =
          open_tree_node_branch root left0 right0 enode).
        rewrite H1 by set_solver.
        reflexivity.
      }
      unfold open_tree_node_branch, open_tree_node_branch_value in Hopen.
      assert (Hright_shift :
        right0 ∉ fv_tm
          (open_tm 1 (vfvar left0)
            (open_tm 0 (vfvar root) (tm_shift (k + 3) enode)))).
      {
        pose proof (open_fv_tm (tm_shift (k + 3) enode) (vfvar root) 0)
          as Hopen_root.
        pose proof (open_fv_tm
          (open_tm 0 (vfvar root) (tm_shift (k + 3) enode)) (vfvar left0) 1)
          as Hopen_left.
        rewrite tm_shift_fv in Hopen_root.
        simpl in Hopen_root, Hopen_left. set_solver.
      }
      assert (Hright_plain :
        right0 ∉ fv_tm
          (open_tm 1 (vfvar left0) (open_tm 0 (vfvar root) enode))).
      {
        pose proof (open_fv_tm enode (vfvar root) 0) as Hopen_root.
        pose proof (open_fv_tm
          (open_tm 0 (vfvar root) enode) (vfvar left0) 1) as Hopen_left.
        simpl in Hopen_root, Hopen_left. set_solver.
      }
      apply (f_equal (fun e => close_tm right0 2 e)) in Hopen.
      rewrite (close_open_var_tm _ right0 2 Hright_shift) in Hopen.
      rewrite (close_open_var_tm _ right0 2 Hright_plain) in Hopen.
      assert (Hleft_shift :
        left0 ∉ fv_tm (open_tm 0 (vfvar root) (tm_shift (k + 3) enode))).
      {
        pose proof (open_fv_tm (tm_shift (k + 3) enode) (vfvar root) 0)
          as Hopen_root.
        rewrite tm_shift_fv in Hopen_root.
        simpl in Hopen_root. set_solver.
      }
      assert (Hleft_plain :
        left0 ∉ fv_tm (open_tm 0 (vfvar root) enode)).
      {
        pose proof (open_fv_tm enode (vfvar root) 0) as Hopen_root.
        simpl in Hopen_root. set_solver.
      }
      apply (f_equal (fun e => close_tm left0 1 e)) in Hopen.
      rewrite (close_open_var_tm _ left0 1 Hleft_shift) in Hopen.
      rewrite (close_open_var_tm _ left0 1 Hleft_plain) in Hopen.
      assert (Hroot_shift : root ∉ fv_tm (tm_shift (k + 3) enode)).
      { rewrite tm_shift_fv. set_solver. }
      assert (Hroot_plain : root ∉ fv_tm enode) by set_solver.
	      apply (f_equal (fun e => close_tm root 0 e)) in Hopen.
	      rewrite (close_open_var_tm _ root 0 Hroot_shift) in Hopen.
	      rewrite (close_open_var_tm _ root 0 Hroot_plain) in Hopen.
	      exact Hopen.
  - rewrite H, H0. reflexivity.
  - f_equal.
    + rewrite H. reflexivity.
    + rewrite H0. reflexivity.
    + pose (hd := fresh_for (L ∪ fv_tm econs)).
      assert (Hhd : hd ∉ L ∪ fv_tm econs)
        by (subst hd; apply fresh_for_not_in).
      pose (tl := fresh_for (L ∪ fv_tm econs ∪ {[hd]})).
      assert (Htl : tl ∉ L ∪ fv_tm econs ∪ {[hd]})
        by (subst tl; apply fresh_for_not_in).
      assert (Hopen :
        open_list_cons_branch hd tl (tm_shift (k + 2) econs) =
        open_list_cons_branch hd tl econs).
      {
        unfold open_list_cons_branch, open_list_cons_branch_value.
        rewrite tm_shift_open_tm_fvar_before by lia.
        rewrite tm_shift_open_tm_fvar_before by lia.
        change (tm_shift (k + 2) (open_list_cons_branch hd tl econs) =
          open_list_cons_branch hd tl econs).
        rewrite H1 by set_solver.
        reflexivity.
      }
      unfold open_list_cons_branch, open_list_cons_branch_value in Hopen.
      assert (Htl_shift :
        tl ∉ fv_tm (open_tm 0 (vfvar hd) (tm_shift (k + 2) econs))).
      {
        pose proof (open_fv_tm (tm_shift (k + 2) econs) (vfvar hd) 0)
          as Hopen_hd.
        rewrite tm_shift_fv in Hopen_hd.
        simpl in Hopen_hd. set_solver.
      }
      assert (Htl_plain :
        tl ∉ fv_tm (open_tm 0 (vfvar hd) econs)).
      {
        pose proof (open_fv_tm econs (vfvar hd) 0) as Hopen_hd.
        simpl in Hopen_hd. set_solver.
      }
      apply (f_equal (fun e => close_tm tl 1 e)) in Hopen.
      rewrite (close_open_var_tm _ tl 1 Htl_shift) in Hopen.
      rewrite (close_open_var_tm _ tl 1 Htl_plain) in Hopen.
      assert (Hhd_shift : hd ∉ fv_tm (tm_shift (k + 2) econs)).
      { rewrite tm_shift_fv. set_solver. }
      assert (Hhd_plain : hd ∉ fv_tm econs) by set_solver.
      apply (f_equal (fun e => close_tm hd 0 e)) in Hopen.
      rewrite (close_open_var_tm _ hd 0 Hhd_shift) in Hopen.
      rewrite (close_open_var_tm _ hd 0 Hhd_plain) in Hopen.
      exact Hopen.
Qed.

Lemma value_shift_lc_id k v :
  lc_value v ->
  value_shift k v = v.
Proof. intros Hlc. exact (proj1 value_tm_shift_lc_id_mutual v Hlc k). Qed.

Lemma tm_shift_lc_id k e :
  lc_tm e ->
  tm_shift k e = e.
Proof. intros Hlc. exact (proj2 value_tm_shift_lc_id_mutual e Hlc k). Qed.

Lemma fv_tapp_tm ef vx :
  fv_tm (tapp_tm ef vx) = fv_tm ef ∪ fv_value vx.
Proof.
  unfold tapp_tm. cbn [fv_tm fv_value].
  rewrite value_shift_fv. set_solver.
Qed.

Lemma tm_swap_atom_tapp_tm x y ef vx :
  tm_swap_atom x y (tapp_tm ef vx) =
  tapp_tm (tm_swap_atom x y ef) (value_swap_atom x y vx).
Proof.
  unfold tapp_tm. cbn [tm_swap_atom value_swap_atom].
  rewrite value_shift_swap_atom. reflexivity.
Qed.

Lemma tm_swap_atom_tapp_tm_fvar_fresh x y ef :
  x ∉ fv_tm ef →
  y ∉ fv_tm ef →
  tm_swap_atom x y (tapp_tm ef (vfvar x)) = tapp_tm ef (vfvar y).
Proof.
  intros Hx Hy.
  rewrite tm_swap_atom_tapp_tm.
  rewrite tm_swap_atom_fresh by assumption.
  simpl. replace (swap x y x) with y
    by (symmetry; apply swap_l).
  reflexivity.
Qed.

Lemma open_tapp_tm_lc_arg ef vx k u :
  lc_value vx →
  open_tm k u (tapp_tm ef vx) = tapp_tm (open_tm k u ef) vx.
Proof.
  intros Hvx.
  unfold tapp_tm. cbn [open_tm open_value].
  rewrite value_shift_lc_id by exact Hvx.
  rewrite open_rec_lc_value by exact Hvx.
  destruct (decide (S k = 0)); [lia|reflexivity].
Qed.

Lemma body_tapp_tm_body vx :
  lc_value vx →
  body_tm (tapp (vbvar 0) vx).
Proof.
  intros Hvx. exists ∅. intros x _.
  change (lc_tm (tapp (vfvar x) (open_value 0 (vfvar x) vx))).
  rewrite (open_rec_lc_value vx Hvx 0 (vfvar x)).
  repeat constructor. exact Hvx.
Qed.

Lemma lc_tapp_tm ef vx :
  lc_tm ef →
  lc_value vx →
  lc_tm (tapp_tm ef vx).
Proof.
  intros Hef Hvx.
  unfold tapp_tm.
  eapply LC_lete with (L := ∅); [exact Hef|].
  intros x _.
  change (lc_tm (tapp (vfvar x)
    (open_value 0 (vfvar x) (value_shift 0 vx)))).
  assert (Hshift_lc : lc_value (value_shift 0 vx)).
  { rewrite value_shift_lc_id by exact Hvx. exact Hvx. }
  rewrite (open_rec_lc_value (value_shift 0 vx) Hshift_lc 0 (vfvar x)).
  rewrite value_shift_lc_id by exact Hvx.
  repeat constructor. exact Hvx.
Qed.

Lemma basic_typing_tapp_tm Γ ef vx Tx T :
  Γ ⊢ₑ ef ⋮ (Tx →ₜ T) →
  Γ ⊢ᵥ vx ⋮ Tx →
  Γ ⊢ₑ tapp_tm ef vx ⋮ T.
Proof.
  intros Hef Hvx.
  unfold tapp_tm.
  eapply TT_Let with (L := dom Γ ∪ fv_value vx).
  - exact Hef.
  - intros x Hx.
    change (<[x:=Tx →ₜ T]> Γ ⊢ₑ
      tapp (vfvar x) (open_value 0 (vfvar x) (value_shift 0 vx)) ⋮ T).
    assert (Hshift_lc : lc_value (value_shift 0 vx)).
    { rewrite value_shift_lc_id by exact (typing_value_lc _ _ _ Hvx).
      exact (typing_value_lc _ _ _ Hvx). }
    rewrite (open_rec_lc_value (value_shift 0 vx) Hshift_lc 0 (vfvar x)).
    rewrite value_shift_lc_id by exact (typing_value_lc _ _ _ Hvx).
    eapply TT_App.
    + eapply VT_FVar. rewrite lookup_insert.
      destruct (decide (x = x)); [reflexivity | congruence].
    + eapply basic_typing_weaken_insert_value; [set_solver | exact Hvx].
Qed.

Lemma basic_typing_tapp_tm_fvar_inv Γ e y T :
  Γ ⊢ₑ tapp_tm e (vfvar y) ⋮ T ->
  exists Tx, Γ ⊢ₑ e ⋮ (Tx →ₜ T) /\ Γ ⊢ᵥ vfvar y ⋮ Tx.
Proof.
  unfold tapp_tm.
  intros Hty.
	  inversion Hty as
	    [|Γ0 Tfun Tbody ef ebody L Hef Hbody| | | | | | |]; subst.
  pose (x := fresh_for (L ∪ dom Γ ∪ fv_tm e ∪ {[y]})).
  assert (Hx : x ∉ L ∪ dom Γ ∪ fv_tm e ∪ {[y]})
    by (subst x; apply fresh_for_not_in).
  specialize (Hbody x ltac:(set_solver)).
  change (<[x:=Tfun]> Γ ⊢ₑ tapp (vfvar x) (vfvar y) ⋮ T) in Hbody.
	  inversion Hbody as [| | |Γ1 s1 s2 v1 v2 Hfun Harg| | | | |]; subst.
  inversion Hfun; subst.
  rewrite lookup_insert in H1.
  destruct (decide (x = x)); [|congruence].
  simplify_eq.
  exists s1. split.
  - exact Hef.
  - eapply basic_typing_drop_insert_fresh_value; [|exact Harg].
    cbn [fv_value]. set_solver.
Qed.

Lemma basic_typing_tapp_tm_tlete_assoc Γ e1 e2 y T :
  Γ ⊢ₑ tlete e1 (tapp_tm e2 (vfvar y)) ⋮ T ->
  Γ ⊢ₑ tapp_tm (tlete e1 e2) (vfvar y) ⋮ T.
Proof.
  intros Hty.
	  inversion Hty as
	    [|Γ0 T1 T2 e1' e2' L He1 Hbody| | | | | | |]; subst.
  pose (x := fresh_for (L ∪ dom Γ ∪ fv_tm e2 ∪ {[y]})).
  assert (Hx : x ∉ L ∪ dom Γ ∪ fv_tm e2 ∪ {[y]})
    by (subst x; apply fresh_for_not_in).
  pose proof (Hbody x ltac:(set_solver)) as Hbody_x.
  change (<[x:=T1]> Γ ⊢ₑ tapp_tm (e2 ^^ x) (vfvar y) ⋮ T) in Hbody_x.
  apply basic_typing_tapp_tm_fvar_inv in Hbody_x as [Tx [He2x Hy]].
  eapply basic_typing_tapp_tm.
  - eapply TT_Let with (L := L ∪ fv_tm e2 ∪ {[y]}).
    + exact He1.
    + intros z Hz.
      pose proof (Hbody z ltac:(set_solver)) as Hbody_z.
      change (<[z:=T1]> Γ ⊢ₑ tapp_tm (e2 ^^ z) (vfvar y) ⋮ T)
        in Hbody_z.
      apply basic_typing_tapp_tm_fvar_inv in Hbody_z as [Txz [He2z Hyz]].
      assert (HyΓ : Γ ⊢ᵥ vfvar y ⋮ Tx).
      {
        eapply basic_typing_drop_insert_fresh_value; [|exact Hy].
        cbn [fv_value]. set_solver.
      }
      assert (HyzΓ : Γ ⊢ᵥ vfvar y ⋮ Txz).
      {
        eapply basic_typing_drop_insert_fresh_value; [|exact Hyz].
        cbn [fv_value]. set_solver.
      }
      assert (Txz = Tx) by (eapply basic_typing_unique_value; eauto).
      subst Txz. exact He2z.
  - eapply basic_typing_drop_insert_fresh_value; [|exact Hy].
    cbn [fv_value]. set_solver.
Qed.

Lemma basic_typing_tapp_tm_tlete_assoc_rev Γ e1 e2 y T :
  Γ ⊢ₑ tapp_tm (tlete e1 e2) (vfvar y) ⋮ T ->
  Γ ⊢ₑ tlete e1 (tapp_tm e2 (vfvar y)) ⋮ T.
Proof.
  intros Hty.
  apply basic_typing_tapp_tm_fvar_inv in Hty as [Tx [Hlet Hy]].
	  inversion Hlet as
	    [|Γ0 T1 T2 e1' e2' L He1 Hbody| | | | | | |]; subst.
  eapply TT_Let with (L := L ∪ dom Γ ∪ fv_tm e2 ∪ {[y]}).
  - exact He1.
  - intros z Hz.
    pose proof (Hbody z ltac:(set_solver)) as He2z.
    change (<[z:=T1]> Γ ⊢ₑ tapp_tm (e2 ^^ z) (vfvar y) ⋮ T).
    eapply basic_typing_tapp_tm.
    + exact He2z.
    + eapply basic_typing_weaken_insert_value.
      * cbn [fv_value]. set_solver.
      * exact Hy.
Qed.

Lemma basic_typing_tret_fvar_insert Γ x T :
  <[x := T]> Γ ⊢ₑ tret (vfvar x) ⋮ T.
Proof.
  apply TT_Ret. apply VT_FVar.
  rewrite lookup_insert. destruct (decide (x = x)); [reflexivity | congruence].
Qed.

Lemma basic_typing_tapp_tm_fvar_insert Γ e x Tx T :
  x ∉ dom Γ →
  Γ ⊢ₑ e ⋮ (Tx →ₜ T) →
  <[x := Tx]> Γ ⊢ₑ tapp_tm e (vfvar x) ⋮ T.
Proof.
  intros Hx Htyped.
  eapply basic_typing_tapp_tm.
  - eapply basic_typing_weaken_insert_tm; [exact Hx | exact Htyped].
  - apply VT_FVar.
    rewrite lookup_insert. destruct (decide (x = x)); [reflexivity | congruence].
Qed.
