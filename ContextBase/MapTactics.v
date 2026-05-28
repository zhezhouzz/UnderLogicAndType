(** * ContextBase.MapTactics

    Shared finite-map lookup/domain normalization. *)

From ContextBase Require Export SetTactics.

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

Lemma map_lookup_none_of_not_elem_dom {K A : Type} `{Countable K}
    (m : gmap K A) i :
  i ∉ dom m →
  m !! i = None.
Proof. intros Hnot. by apply not_elem_of_dom. Qed.

Lemma map_not_elem_dom_of_lookup_none {K A : Type} `{Countable K}
    (m : gmap K A) i :
  m !! i = None →
  i ∉ dom m.
Proof. intros Hnone. by apply not_elem_of_dom in Hnone. Qed.

Lemma map_lookup_delete_eq {K A : Type} `{Countable K}
    (m : gmap K A) i :
  delete i m !! i = None.
Proof. apply lookup_delete_eq. Qed.

Lemma map_lookup_delete_ne {K A : Type} `{Countable K}
    (m : gmap K A) i j :
  j ≠ i →
  delete i m !! j = m !! j.
Proof. intros Hji. apply lookup_delete_ne. congruence. Qed.

Ltac map_normalize_step :=
  match goal with
  | H : context[∅ ∪ ?m] |- _ => rewrite map_empty_union in H
  | |- context[∅ ∪ ?m] => rewrite map_empty_union
  | H : context[?m ∪ ∅] |- _ => rewrite map_union_empty in H
  | |- context[?m ∪ ∅] => rewrite map_union_empty
  | H : context[∅ !! _] |- _ => rewrite lookup_empty in H
  | |- context[∅ !! _] => rewrite lookup_empty
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
      rewrite lookup_insert in H
  | |- context[(<[?i := ?v]> ?m) !! ?i] =>
      rewrite lookup_insert
  | H : context[@gmap_lookup ?K ?EqK ?CountK ?A ?i (<[?i := ?v]> ?m)] |- _ =>
      rewrite lookup_insert in H
  | |- context[@gmap_lookup ?K ?EqK ?CountK ?A ?i (<[?i := ?v]> ?m)] =>
      rewrite lookup_insert
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
      [rewrite lookup_insert in H | rewrite lookup_insert_ne in H by congruence]
  | |- context[(<[?i := ?v]> ?m) !! ?j] =>
      destruct (decide (j = i)); subst;
      [rewrite lookup_insert | rewrite lookup_insert_ne by congruence]
  end.

Ltac better_map_solver :=
  map_normalize;
  map_lookup_split;
  map_normalize;
  repeat match goal with
  | H : ?m !! ?x = Some ?v |- ?x ∈ dom ?m =>
      apply elem_of_dom_2 in H; exact H
  | H : ?x ∉ dom ?m |- ?m !! ?x = None =>
      apply not_elem_of_dom; exact H
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
  try (map_lookup_case_step; eauto 8; try reflexivity; try congruence);
  try better_set_solver.

Tactic Notation "better_map_solver" "!" :=
  set_prune_hyps_safe; better_map_solver.
Tactic Notation "better_map_solver" "!!" :=
  set_prune_hyps; better_map_solver.
