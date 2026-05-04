From CoreLang Require Export Syntax.
From Stdlib Require Import Arith.Compare_dec.

(** * Shared locally-nameless proof helpers

    This file intentionally stays small: it provides the lightweight proof
    automation used by the CoreLang proof files, while the larger theorem
    statements live next to the CoreLang definitions. *)

(** ** Hypothesis traversal *)

Ltac revert_all :=
  repeat match goal with
  | H : _ |- _ => revert H
  end.

Ltac get_hyps :=
  constr:(ltac:(revert_all; constructor) : True).

Tactic Notation "do_hyps" tactic3(tac) :=
  let hs := get_hyps in
  let rec go hs :=
      lazymatch hs with
      | ?hs ?H => tac H; go hs
      | _ => idtac
      end in
  go hs.

Tactic Notation "select" "!" open_constr(pat) tactic3(tac) :=
  let T := lazymatch goal with
           | H : pat |- _ => type of H
           end in
  do_hyps (fun H => lazymatch type of H with
                  | pat => tac H
                  | _ => idtac
                  end);
  unify T pat.

Ltac fold_hyps acc tac :=
  let hs := get_hyps in
  let rec go hs acc :=
      lazymatch hs with
      | ?hs ?H => let acc' := tac H acc in go hs acc'
      | _ => acc
      end in
  go hs acc.

(** ** Small destruct/inversion helpers *)

Ltac destruct_hyp_conj :=
  match goal with
  | H : ?P ∧ ?Q |- _ =>
      destruct H;
      repeat match goal with
      | H' : P ∧ Q |- _ => clear H'
      end
  | H : atom * _ |- _ => destruct H
  | H : ex _ |- _ => destruct H
  | H : context[decide (?a = ?b)] |- _ =>
      destruct (decide (a = b)); subst
  | |- context[decide (?a = ?b)] =>
      destruct (decide (a = b)); subst
  end.

Ltac destruct_hyp_disj :=
  repeat match goal with
  | H : _ ∨ _ |- _ => destruct H
  end.

Ltac mydestr := repeat destruct_hyp_conj.

Ltac invclear H := inversion H; subst; clear H.

(** ** Set/map normalization *)

Ltac fast_set_solver :=
  solve [try fast_done; repeat (set_unfold; subst; intuition)].

Ltac set_fold_not :=
  change (?x ∈ ?v → False) with (x ∉ v) in *;
  change (?x = ?v → False) with (x ≠ v) in *.

Ltac set_prune_hyps_safe :=
  simpl;
  set_fold_not;
  repeat
    match goal with
    | H : ?T |- _ =>
      lazymatch T with
      | _ ⊆ _ => fail
      | _ ≡ ∅ => rewrite H in *; clear H
      | _ ≡ _ => fail
      | _ ∈ _ => fail
      | _ ∉ _ => fail
      | _ ≠ _ => fail
      | context [_ → _ ⊆ _] => fail
      | context [_ → _ ≡ _] => fail
      | context [_ → _ ∈ _] => fail
      | context [_ → _ ∉ _] => fail
      | context [_ → _ ≠ _] => fail
      | _ => clear H
      end
    end;
  repeat
    match goal with
    | H : _ ∉ {[_]} |- _ => apply not_elem_of_singleton_1 in H
    end;
  repeat
    match goal with
    | H : ?S ⊆ ?U, H' : ?S ⊆ ?V |- _ =>
      let rec go U :=
          lazymatch U with
          | ?U1 ∪ ?U2 => go U1; go U2
          | _ =>
            lazymatch V with
            | context[U] => idtac
            end
          end in go U; clear H'
    end.

Tactic Notation "set_hyp_filter" constr(T) ">>=" tactic3(tac) :=
  lazymatch T with
  | _ ⊆ _ => fail
  | _ ≡ _ => fail
  | context [_ → _ ⊆ _] => fail
  | context [_ → _ ≡ _] => fail
  | _ => tac T
  end.

Tactic Notation "set_hyp_filter" constr(T) constr(x) ">>=" tactic3(tac) :=
  lazymatch T with
  | context[x] =>
    lazymatch T with
    | _ ∈ _ => fail
    | _ ∉ _ => fail
    | _ ≠ _ => fail
    | context [_ → _ ∈ _] => fail
    | context [_ → _ ∉ _] => fail
    | context [_ → _ ≠ _] => fail
    | _ => tac T
    end
  | _ => tac T
  end.

Ltac set_prune_hyps :=
  set_prune_hyps_safe;
  try
    lazymatch goal with
    | |- _ ⊆ _ =>
      repeat
        match goal with
        | H : ?T |- _ =>
          set_hyp_filter T >>= (fun _ => clear H)
        end
    | |- ?y ∉ _ =>
      repeat
        match goal with
        | H : ?T |- _ =>
          set_hyp_filter T >>= (fun T =>
            set_hyp_filter T y >>= (fun _ => clear H))
        end
    | |- ?x ≠ ?y =>
      repeat
        match goal with
        | H : ?T |- _ =>
          set_hyp_filter T >>= (fun T =>
            set_hyp_filter T x >>= (fun T =>
              set_hyp_filter T y >>= (fun _ => clear H)))
        end
    end.

Tactic Notation "set_solver" "!" :=
  set_prune_hyps_safe; set_solver.
Tactic Notation "set_solver" "!!" :=
  set_prune_hyps; set_solver.
Tactic Notation "fast_set_solver" "!" :=
  set_prune_hyps_safe; fast_set_solver.
Tactic Notation "fast_set_solver" "!!" :=
  set_prune_hyps; fast_set_solver.

Ltac crush_binders :=
  repeat match goal with
  | H : context[decide (?x = ?x)] |- _ =>
      rewrite decide_True in H by reflexivity
  | |- context[decide (?x = ?x)] =>
      rewrite decide_True by reflexivity
  | H : context[decide (?x = ?y)] |- _ =>
      rewrite decide_False in H by congruence
  | |- context[decide (?x = ?y)] =>
      rewrite decide_False by congruence
  end.

Ltac inv_lc :=
  repeat match goal with
  | H : lc_value (vconst _) |- _ => inversion H; subst; clear H
  | H : lc_value (vfvar _) |- _ => inversion H; subst; clear H
  | H : lc_value (vbvar _) |- _ => inversion H; subst; clear H
  | H : lc_value (vlam _ _) |- _ => inversion H; subst; clear H
  | H : lc_value (vfix _ _) |- _ => inversion H; subst; clear H
  | H : lc_tm (tret _) |- _ => inversion H; subst; clear H
  | H : lc_tm (tlete _ _) |- _ => inversion H; subst; clear H
  | H : lc_tm (tprim _ _) |- _ => inversion H; subst; clear H
  | H : lc_tm (tapp _ _) |- _ => inversion H; subst; clear H
  | H : lc_tm (tmatch _ _ _) |- _ => inversion H; subst; clear H
  end.

Ltac ln_simpl :=
  simpl in *; crush_binders; try set_solver; try congruence; eauto.

(** ** Small set facts used by locally-nameless scripts *)

Lemma setunion_cons_cons (x : atom) (s1 s2 : aset) :
  {[x]} ∪ s1 ∪ ({[x]} ∪ s2) = {[x]} ∪ s1 ∪ s2.
Proof. set_solver. Qed.

Lemma setunion_empty_left (s : aset) :
  ∅ ∪ s = s.
Proof. set_solver. Qed.

Lemma subseteq_subtract_both (x : atom) (s1 s2 : aset) :
  x ∉ s1 →
  x ∉ s2 →
  {[x]} ∪ s1 ⊆ {[x]} ∪ s2 →
  s1 ⊆ s2.
Proof. set_solver. Qed.

Lemma setunion_cons_right (x : atom) (s : aset) :
  s ∪ ({[x]} ∪ ∅) = {[x]} ∪ s.
Proof. set_solver. Qed.

Lemma subseteq_subtract_both' (x : atom) (s1 s2 : aset) :
  x ∉ s1 →
  x ∉ s2 →
  {[x]} ∪ s1 ⊆ s2 ∪ ({[x]} ∪ ∅) →
  s1 ⊆ s2.
Proof. set_solver. Qed.

Lemma subseteq_trans_cons (x : atom) (s1 s2 s3 : aset) :
  {[x]} ∪ s1 ⊆ {[x]} ∪ s2 →
  s2 ⊆ {[x]} ∪ s3 →
  {[x]} ∪ s1 ⊆ {[x]} ∪ s3.
Proof. set_solver. Qed.

Lemma setunion_mono_cons (x : atom) (s1 s2 s3 s4 : aset) :
  {[x]} ∪ s1 ⊆ {[x]} ∪ s2 →
  {[x]} ∪ s3 ⊆ {[x]} ∪ s4 →
  {[x]} ∪ (s1 ∪ s3) ⊆ {[x]} ∪ (s2 ∪ s4).
Proof. set_solver. Qed.

Ltac my_set_simpl_aux :=
  match goal with
  | |- _ !! _ = None => rewrite <- not_elem_of_dom
  | H : stale _ = ∅ |- _ => rewrite H in *; clear H
  | H : context[∅ ∪ ?d] |- _ =>
      setoid_rewrite setunion_empty_left in H
  | |- context[∅ ∪ ?d] =>
      setoid_rewrite setunion_empty_left
  | H : context[?s ∪ ∅] |- _ =>
      setoid_rewrite (right_id ∅ (∪) s) in H
  | |- context[?s ∪ ∅] =>
      setoid_rewrite (right_id ∅ (∪) s)
  end.

Ltac my_set_simpl := repeat my_set_simpl_aux.

Ltac my_map_simpl_aux :=
  match goal with
  | H : context[dom (<[_:=_]> _)] |- _ => rewrite dom_insert_L in H
  | |- context[dom (<[_:=_]> _)] => rewrite dom_insert_L
  | H : context[∅ ∪ _] |- _ => rewrite map_empty_union in H
  | |- context[∅ ∪ _] => rewrite map_empty_union
  | H : context[_ ∪ ∅] |- _ => rewrite map_union_empty in H
  | |- context[_ ∪ ∅] => rewrite map_union_empty
  end.

Ltac my_map_simpl := repeat my_map_simpl_aux.

Ltac my_set_solver :=
  my_map_simpl;
  my_set_simpl;
  eauto;
  try match goal with
  | |- {[?x]} ∪ (?s1 ∪ ?s3) ⊆ {[?x]} ∪ (?s2 ∪ ?s4) =>
      apply setunion_mono_cons; eauto
  | H : {[?x]} ∪ ?s1 ⊆ {[?x]} ∪ ?s2 |- ?s1 ⊆ ?s2 =>
      eapply subseteq_subtract_both; eauto; fast_set_solver
  end;
  try fast_set_solver!!;
  try set_solver.

(** ** Fresh-variable automation *)

Ltac pose_fresh_from x s :=
  let Hfresh := fresh "Hfresh" in
  pose (x := fresh_for s);
  assert (Hfresh : x ∉ s) by (subst x; apply fresh_for_not_in).

Ltac collect_one_stale e acc :=
  match goal with
  | _ =>
      lazymatch acc with
      | tt => constr:(stale e)
      | _ => constr:(acc ∪ stale e)
      end
  | _ => acc
  end.

Ltac collect_stales S :=
  let stales := fold_hyps S collect_one_stale in
  lazymatch stales with
  | tt => fail "no stale available"
  | _ => stales
  end.

Ltac auto_exists_L :=
  let acc := collect_stales tt in
  econstructor; eauto; try instantiate (1 := acc).

Ltac auto_pose_fv a :=
  let acc := collect_stales tt in
  pose (a := fresh_for acc);
  assert (a ∉ acc) by (subst a; apply fresh_for_not_in);
  clearbody a.

Ltac specialize_with x :=
  match goal with
  | H : forall x, (x ∈ ?L → False) → _ |- _ =>
      let Htmp := fresh "Htmp" in
      assert (x ∉ L) as Htmp by my_set_solver;
      specialize (H x Htmp);
      try clear Htmp
  | H : forall x, x ∉ ?L → _ |- _ =>
      let Htmp := fresh "Htmp" in
      assert (x ∉ L) as Htmp by my_set_solver;
      specialize (H x Htmp);
      try clear Htmp
  end.

Ltac pose_fresh_fv name := auto_pose_fv name.

(** ** Decidable-variable cleanup *)

Ltac rw_decide_true a b :=
  assert (a = b) as Hrw_decide_true by auto;
  rewrite (decide_True _ _ Hrw_decide_true);
  clear Hrw_decide_true.

Ltac rw_decide_true_in a b H :=
  assert (a = b) as Hrw_decide_true by auto;
  rewrite (decide_True _ _ Hrw_decide_true) in H;
  clear Hrw_decide_true.

Ltac auto_exfalso :=
  match goal with
  | H : ?a ≠ ?a |- _ => exfalso; apply H; reflexivity
  | H : False |- _ => inversion H
  | H : Some _ = None |- _ => inversion H
  | H : None = Some _ |- _ => inversion H
  end || (exfalso; fast_set_solver!!).

Ltac var_dec_solver :=
  try auto_exfalso;
  match goal with
  | H : Some ?a = Some ?b |- _ =>
      inversion H; subst; clear H; simpl; auto
  | H : ?a ≠ ?a |- _ =>
      exfalso; apply H; reflexivity
  | |- Some _ = None =>
      exfalso; congruence
  | |- None = Some _ =>
      exfalso; congruence
  | H : context[decide (?a = ?a)] |- _ =>
      rw_decide_true_in a a H; auto
  | H : context[decide (?a = ?b)] |- _ =>
      match goal with
      | H' : a = b |- _ => rewrite (decide_True _ _ H') in H; auto
      | H' : a ≠ b |- _ => rewrite (decide_False _ _ H') in H; auto
      | _ => destruct (decide (a = b)); subst; simpl in H; simpl
      end
  | H : context[decide (?a < ?b)] |- _ =>
      match goal with
      | H' : a < b |- _ => rewrite (decide_True _ _ H') in H; auto
      | H' : ¬ (a < b) |- _ => rewrite (decide_False _ _ H') in H; auto
      | _ => destruct (decide (a < b)); subst; simpl in H; simpl
      end
  | |- context[decide (?a = ?a)] =>
      rw_decide_true a a; auto
  | |- context[decide (?a = ?b)] =>
      match goal with
      | H : a = b |- _ => rewrite (decide_True _ _ H); auto
      | H : a ≠ b |- _ => rewrite (decide_False _ _ H); auto
      | _ => destruct (decide (a = b)); subst; simpl; var_dec_solver
      end
  | |- context[decide (?a < ?b)] =>
      match goal with
      | H : a < b |- _ => rewrite (decide_True _ _ H); auto
      | H : ¬ (a < b) |- _ => rewrite (decide_False _ _ H); auto
      | _ => destruct (decide (a < b)); subst; simpl; var_dec_solver
      end
  | _ => progress simpl
  end.

(** ** Hypothesis application *)

Ltac curry_tac f p :=
  let rec go p :=
      lazymatch p with
      | (?a, ?p) => curry_tac (f a) p
      | tt => f
      end in go p.

Tactic Notation "apply_eq" uconstr(H) "by" tactic3(tac) :=
  let rec go R p :=
      match R with
      | ?R ?a =>
          let f := constr:(fun e =>
                             ltac:(let g := curry_tac (R e) p in
                                   exact g)) in
          let T := type of a in
          let a := mk_evar T in
          refine (eq_ind a f _ _ _); [ go R constr:((a, p)) | ]
      | _ => idtac
      end in
  match goal with
  | |- ?T => go T constr:(tt)
  end; [ tac H | .. ]; try reflexivity.

Tactic Notation "apply_eq" uconstr(H) := apply_eq H by (fun H => apply H).
Tactic Notation "eapply_eq" uconstr(H) := apply_eq H by (fun H => eapply H).

Tactic Notation "auto_apply" "by" tactic3(tac) :=
  try eassumption;
  match goal with
  | H : context[_ → ?C] |- ?C => tac H
  | H : context[_ → ?C _] |- ?C _ => tac H
  | H : context[_ → ?C _ _] |- ?C _ _ => tac H
  | H : context[_ → ?C _ _ _] |- ?C _ _ _ => tac H
  | H : context[_ → ?C _ _ _ _] |- ?C _ _ _ _ => tac H
  | H : context[_ → ?C _ _ _ _ _] |- ?C _ _ _ _ _ => tac H
  | H : context[_ → ?C _ _ _ _ _ _] |- ?C _ _ _ _ _ _ => tac H
  | H : context[_ → ?C _ _ _ _ _ _ _] |- ?C _ _ _ _ _ _ _ => tac H
  end.

Tactic Notation "auto_apply" := auto_apply by (fun H => apply H).
Tactic Notation "auto_eapply" := auto_apply by (fun H => eapply H).
Tactic Notation "auto_apply_eq" := auto_apply by (fun H => apply_eq H).
Tactic Notation "auto_eapply_eq" := auto_apply by (fun H => eapply_eq H).

(** ** Cofinite constructors *)

Ltac econstructor_L :=
  unshelve econstructor;
  try lazymatch goal with
  | |- aset =>
      let acc := collect_stales tt in exact acc
  | |- ?G =>
      try lazymatch type of G with
      | Prop => fail 1
      | _ => shelve
      end
  end;
  eauto.

Ltac auto_specialization :=
  try lazymatch goal with
  | |- ∀ y, y ∉ _ → _ =>
      let y := fresh "y" in
      let Hy := fresh "Hy" in
      intros y Hy;
      specialize_with y
  end;
  eauto.

Ltac econstructor_L_specialized :=
  econstructor_L; auto_specialization.
