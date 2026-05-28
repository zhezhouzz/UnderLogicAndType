(** * ContextBase.SetTactics

    Shared set-side proof automation.

    [set_normalize] performs equivalence-preserving normalization only.
    [better_set_solver] adds the small amount of hypothesis pruning and
    non-equivalence reasoning that we want all later layers to share instead of
    hand-writing stdpp set lemmas. *)

From stdpp Require Export gmap sets fin_sets fin_map_dom fin_maps countable tactics.

Lemma set_difference_pull_singleton {K : Type} `{Countable K}
    (X Y : gset K) x :
  x ∈ X →
  x ∉ Y →
  X ∖ Y = (X ∖ ({[x]} ∪ Y)) ∪ {[x]}.
Proof.
  intros HxX HxY.
  apply set_eq. intros z.
  rewrite elem_of_difference, elem_of_union, elem_of_difference,
    elem_of_union, !elem_of_singleton.
  split.
  - intros [HzX HzY].
    destruct (decide (z = x)) as [->|Hzx].
    + right. reflexivity.
    + left. split; [exact HzX |].
      intros [Hzx'|HzY']; [congruence | contradiction].
  - intros [[HzX Hnot] | Hzx].
    + split; [exact HzX |].
      intros HzY. apply Hnot. right. exact HzY.
    + subst z. split; [exact HxX | exact HxY].
Qed.

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
      | _ ## _ => fail
      | context [_ → _ ⊆ _] => fail
      | context [_ → _ ≡ _] => fail
      | context [_ → _ ∈ _] => fail
      | context [_ → _ ∉ _] => fail
      | context [_ → _ ≠ _] => fail
      | context [_ → _ ## _] => fail
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

Tactic Notation "fast_set_solver" "!" :=
  set_prune_hyps_safe; fast_set_solver.
Tactic Notation "fast_set_solver" "!!" :=
  set_prune_hyps; fast_set_solver.

Ltac set_normalize_step :=
  match goal with
  | H : context[∅ ∪ ?X] |- _ =>
      rewrite (left_id ∅ (∪) X) in H
  | |- context[∅ ∪ ?X] =>
      rewrite (left_id ∅ (∪) X)
  | H : context[?X ∪ ∅] |- _ =>
      rewrite (right_id ∅ (∪) X) in H
  | |- context[?X ∪ ∅] =>
      rewrite (right_id ∅ (∪) X)
  | H : context[?X ∩ ?X] |- _ =>
      replace (X ∩ X) with X in H by set_solver
  | |- context[?X ∩ ?X] =>
      replace (X ∩ X) with X by set_solver
  | Hsub : ?X ⊆ ?Y, H : context[?Y ∩ ?X] |- _ =>
      replace (Y ∩ X) with X in H by set_solver
  | Hsub : ?X ⊆ ?Y |- context[?Y ∩ ?X] =>
      replace (Y ∩ X) with X by set_solver
  | Hsub : ?X ⊆ ?Y, H : context[?X ∩ ?Y] |- _ =>
      replace (X ∩ Y) with X in H by set_solver
  | Hsub : ?X ⊆ ?Y |- context[?X ∩ ?Y] =>
      replace (X ∩ Y) with X by set_solver
  | H : context[dom ∅] |- _ => rewrite dom_empty_L in H
  | |- context[dom ∅] => rewrite dom_empty_L
  | H : context[dom ({[_:=_]})] |- _ => rewrite dom_singleton_L in H
  | |- context[dom ({[_:=_]})] => rewrite dom_singleton_L
  | H : context[dom (<[_:=_]> _)] |- _ => rewrite dom_insert_L in H
  | |- context[dom (<[_:=_]> _)] => rewrite dom_insert_L
  | H : context[dom (delete _ _)] |- _ => rewrite dom_delete_L in H
  | |- context[dom (delete _ _)] => rewrite dom_delete_L
  | H : context[dom (_ ∪ _)] |- _ => rewrite dom_union_L in H
  | |- context[dom (_ ∪ _)] => rewrite dom_union_L
  end.

Ltac set_normalize := repeat set_normalize_step.

Ltac better_set_solver :=
  set_normalize;
  eauto 6;
  try fast_set_solver!!;
  try set_solver.

Tactic Notation "better_set_solver" "!" :=
  set_prune_hyps_safe; better_set_solver.
Tactic Notation "better_set_solver" "!!" :=
  set_prune_hyps; better_set_solver.

Ltac solve_set := better_set_solver.
