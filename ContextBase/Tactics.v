(** * ContextBase.Tactics

    Shared set and finite-map proof automation. *)

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

Lemma gset_union_singleton_empty_r {K : Type} `{Countable K}
    (X : gset K) y :
  X ∪ ({[y]} ∪ ∅) = X ∪ {[y]}.
Proof. set_solver. Qed.

Lemma gset_empty_union_singleton_l {K : Type} `{Countable K}
    (y : K) :
  ∅ ∪ {[y]} = ({[y]} : gset K).
Proof. set_solver. Qed.

Lemma gset_notin_union4_l {K : Type} `{Countable K}
    (a : K) (A B C D : gset K) :
  a ∉ A ∪ B ∪ C ∪ D →
  a ∉ A.
Proof. set_solver. Qed.

Lemma gset_notin_union4_r1 {K : Type} `{Countable K}
    (a : K) (A B C D : gset K) :
  a ∉ A ∪ B ∪ C ∪ D →
  a ∉ B.
Proof. set_solver. Qed.

Lemma gset_notin_union4_r2 {K : Type} `{Countable K}
    (a : K) (A B C D : gset K) :
  a ∉ A ∪ B ∪ C ∪ D →
  a ∉ C.
Proof. set_solver. Qed.

Lemma gset_notin_union4_r3 {K : Type} `{Countable K}
    (a : K) (A B C D : gset K) :
  a ∉ A ∪ B ∪ C ∪ D →
  a ∉ D.
Proof. set_solver. Qed.

Lemma gset_elem_union_singleton_not_eq_left {K : Type} `{Countable K}
    (A : gset K) a y :
  a ∈ A ∪ {[y]} →
  a ≠ y →
  a ∈ A.
Proof. set_solver. Qed.

Lemma gset_elem_open_world_inter_singleton {K : Type} `{Countable K}
    x y (B : gset K) :
  x ∈ B →
  x ∈ (B ∪ {[y]}) ∩ ({[x]} : gset K).
Proof. set_solver. Qed.

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

(** ** Finite-map lookup/domain normalization *)

Lemma map_lookup_insert {K A : Type} `{Countable K}
    (m : gmap K A) x v :
  (<[x := v]> m) !! x = Some v.
Proof.
  rewrite lookup_insert. destruct (decide (x = x)); congruence.
Qed.

Lemma map_lookup_insert_ne {K A : Type} `{Countable K}
    (m : gmap K A) x y v :
  y ≠ x →
  (<[x := v]> m) !! y = m !! y.
Proof. intros Hyx. apply lookup_insert_ne. congruence. Qed.

Lemma map_lookup_singleton {K A : Type} `{Countable K}
    (x : K) (v : A) :
  ({[x := v]} : gmap K A) !! x = Some v.
Proof.
  rewrite lookup_singleton. destruct (decide (x = x)); congruence.
Qed.

Lemma map_lookup_singleton_ne {K A : Type} `{Countable K}
    (x y : K) (v : A) :
  y ≠ x →
  ({[x := v]} : gmap K A) !! y = None.
Proof. intros Hyx. apply lookup_singleton_ne. congruence. Qed.

Lemma map_lookup_union_Some_raw {K A : Type} `{Countable K}
    (m1 m2 : gmap K A) i v :
  (m1 ∪ m2) !! i = Some v ↔
    m1 !! i = Some v ∨ (m1 !! i = None ∧ m2 !! i = Some v).
Proof. apply lookup_union_Some_raw. Qed.

Lemma map_lookup_union_None {K A : Type} `{Countable K}
    (m1 m2 : gmap K A) i :
  (m1 ∪ m2) !! i = None ↔ m1 !! i = None ∧ m2 !! i = None.
Proof. apply lookup_union_None. Qed.

Lemma map_elem_of_dom_lookup_some {K A : Type} `{Countable K}
    (m : gmap K A) i v :
  m !! i = Some v →
  i ∈ dom m.
Proof. intros Hlook. by apply elem_of_dom_2 in Hlook. Qed.

Ltac map_normalize_step :=
  match goal with
  | H : context[∅ ∪ ?m] |- _ => rewrite map_empty_union in H
  | |- context[∅ ∪ ?m] => rewrite map_empty_union
  | H : context[?m ∪ ∅] |- _ => rewrite map_union_empty in H
  | |- context[?m ∪ ∅] => rewrite map_union_empty
  | H : context[∅ !! _] |- _ => rewrite lookup_empty in H
  | |- context[∅ !! _] => rewrite lookup_empty
  | H : context[{[?i := ?v]} !! ?i] |- _ =>
      rewrite map_lookup_singleton in H
  | |- context[{[?i := ?v]} !! ?i] =>
      rewrite map_lookup_singleton
  | Hne : ?j ≠ ?i, H : context[{[?i := ?v]} !! ?j] |- _ =>
      rewrite map_lookup_singleton_ne in H by exact Hne
  | Hne : ?j ≠ ?i |- context[{[?i := ?v]} !! ?j] =>
      rewrite map_lookup_singleton_ne by exact Hne
  | Hne : ?i ≠ ?j, H : context[{[?i := ?v]} !! ?j] |- _ =>
      rewrite map_lookup_singleton_ne in H by congruence
  | Hne : ?i ≠ ?j |- context[{[?i := ?v]} !! ?j] =>
      rewrite map_lookup_singleton_ne by congruence
  | H : context[(delete ?i ?m) !! ?i] |- _ =>
      rewrite lookup_delete_eq in H
  | |- context[(delete ?i ?m) !! ?i] =>
      rewrite lookup_delete_eq
  | Hne : ?j ≠ ?i, H : context[(delete ?i ?m) !! ?j] |- _ =>
      rewrite lookup_delete_ne in H by exact Hne
  | Hne : ?j ≠ ?i |- context[(delete ?i ?m) !! ?j] =>
      rewrite lookup_delete_ne by exact Hne
  | Hne : ?i ≠ ?j, H : context[(delete ?i ?m) !! ?j] |- _ =>
      rewrite lookup_delete_ne in H by congruence
  | Hne : ?i ≠ ?j |- context[(delete ?i ?m) !! ?j] =>
      rewrite lookup_delete_ne by congruence
  | H : context[(<[?i := ?v]> ?m) !! ?i] |- _ =>
      rewrite map_lookup_insert in H
  | |- context[(<[?i := ?v]> ?m) !! ?i] =>
      rewrite map_lookup_insert
  | H : context[@gmap_lookup ?K ?EqK ?CountK ?A ?i (<[?i := ?v]> ?m)] |- _ =>
      rewrite map_lookup_insert in H
  | |- context[@gmap_lookup ?K ?EqK ?CountK ?A ?i (<[?i := ?v]> ?m)] =>
      rewrite map_lookup_insert
  | Hne : ?j ≠ ?i, H : context[(<[?i := ?v]> ?m) !! ?j] |- _ =>
      rewrite lookup_insert_ne in H by exact Hne
  | Hne : ?j ≠ ?i |- context[(<[?i := ?v]> ?m) !! ?j] =>
      rewrite lookup_insert_ne by exact Hne
  | Hne : ?i ≠ ?j, H : context[(<[?i := ?v]> ?m) !! ?j] |- _ =>
      rewrite lookup_insert_ne in H by congruence
  | Hne : ?i ≠ ?j |- context[(<[?i := ?v]> ?m) !! ?j] =>
      rewrite lookup_insert_ne by congruence
  | Hne : ?j ≠ ?i,
    H : context[@gmap_lookup ?K ?EqK ?CountK ?A ?j (<[?i := ?v]> ?m)] |- _ =>
      rewrite lookup_insert_ne in H by exact Hne
  | Hne : ?j ≠ ?i
    |- context[@gmap_lookup ?K ?EqK ?CountK ?A ?j (<[?i := ?v]> ?m)] =>
      rewrite lookup_insert_ne by exact Hne
  | H : context[@gmap_lookup ?K ?EqK ?CountK ?A ?j (<[?i := ?v]> ?m)] |- _ =>
      rewrite lookup_insert_ne in H by congruence
  | |- context[@gmap_lookup ?K ?EqK ?CountK ?A ?j (<[?i := ?v]> ?m)] =>
      rewrite lookup_insert_ne by congruence
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

Ltac map_normalize := repeat map_normalize_step.

Ltac map_lookup_split :=
  repeat match goal with
  | H : (_ ∪ _) !! _ = Some _ |- _ =>
      rewrite lookup_union_Some_raw in H
  | |- (_ ∪ _) !! _ = Some _ =>
      rewrite lookup_union_Some_raw
  | H : (_ ∪ _) !! _ = None |- _ =>
      rewrite lookup_union_None in H
  | |- (_ ∪ _) !! _ = None =>
      rewrite lookup_union_None
  | H : _ !! _ = None |- _ =>
      rewrite <- not_elem_of_dom in H
  | |- _ !! _ = None =>
      rewrite <- not_elem_of_dom
  end.

Ltac map_lookup_case_step :=
  match goal with
  | H : context[(<[?i := ?v]> ?m) !! ?j] |- _ =>
      destruct (decide (j = i)); subst;
      [rewrite map_lookup_insert in H | rewrite lookup_insert_ne in H by congruence]
  | |- context[(<[?i := ?v]> ?m) !! ?j] =>
      destruct (decide (j = i)); subst;
      [rewrite map_lookup_insert | rewrite lookup_insert_ne by congruence]
  end.

Ltac better_map_solver :=
  map_normalize;
  map_lookup_split;
  map_normalize;
  repeat match goal with
  | H : ?m !! ?x = Some ?v |- ?x ∈ dom ?m =>
      apply elem_of_dom_2 in H; exact H
  | H : ?m !! ?x = Some ?v |- exists v, ?m !! ?x = Some v =>
      exists v; exact H
  | H : ?x ∈ dom ?m |- exists v, ?m !! ?x = Some v =>
      apply elem_of_dom in H; exact H
  | H : ?x ∉ dom ?m |- ?m !! ?x = None =>
      apply not_elem_of_dom; exact H
  | H : ?m !! ?x = None |- ?x ∉ dom ?m =>
      apply not_elem_of_dom in H; exact H
  | Hdom : dom ?m = ?X, Hx : ?x ∉ ?X |- ?m !! ?x = None =>
      apply not_elem_of_dom; rewrite Hdom; exact Hx
  | Hdom : dom ?m = ?X, Hx : ?x ∈ dom ?m |- ?x ∈ ?X =>
      rewrite <- Hdom; exact Hx
  | Hdom : dom ?m = ?X, Hx : ?x ∈ ?X |- ?x ∈ dom ?m =>
      rewrite Hdom; exact Hx
  end;
  eauto 8;
  try reflexivity;
  try congruence;
  try (repeat map_lookup_case_step; eauto 8; try reflexivity; try congruence);
  try better_set_solver.

Tactic Notation "better_map_solver" "!" :=
  set_prune_hyps_safe; better_map_solver.
Tactic Notation "better_map_solver" "!!" :=
  set_prune_hyps; better_map_solver.
