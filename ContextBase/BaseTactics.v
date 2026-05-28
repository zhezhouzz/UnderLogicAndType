(** * ContextBase.BaseTactics

    Automation for common uses of ContextBase lemmas outside the base layer. *)

From ContextBase Require Import LogicVarShift.

(** [better_base_solver] extends the shared set/map solvers with generic swap
    normal forms that recur across CoreLang, store, algebra, and syntax proofs.
    Fresh-name generation is intentionally kept out of this tactic: cofinite
    proofs should choose witnesses explicitly and then use set automation on the
    resulting freshness side conditions. *)

Ltac base_swap_normalize_step :=
  match goal with
  | H : context[swap ?x ?y ?x] |- _ =>
      rewrite (swap_l x y) in H
  | |- context[swap ?x ?y ?x] =>
      rewrite (swap_l x y)
  | H : context[swap ?x ?y ?y] |- _ =>
      rewrite (swap_r x y) in H
  | |- context[swap ?x ?y ?y] =>
      rewrite (swap_r x y)
  | H : context[swap ?x ?y (swap ?x ?y ?z)] |- _ =>
      rewrite (swap_involutive x y z) in H
  | |- context[swap ?x ?y (swap ?x ?y ?z)] =>
      rewrite (swap_involutive x y z)
  | H : context[swap ?x ?y ?z] |- _ =>
      rewrite (swap_fresh x y z) in H by (congruence || better_set_solver)
  | |- context[swap ?x ?y ?z] =>
      rewrite (swap_fresh x y z) by (congruence || better_set_solver)
  | H : context[set_swap ?x ?y ∅] |- _ =>
      rewrite (set_swap_empty x y) in H
  | |- context[set_swap ?x ?y ∅] =>
      rewrite (set_swap_empty x y)
  | H : context[set_swap ?x ?y ({[?z]})] |- _ =>
      rewrite (set_swap_singleton x y z) in H
  | |- context[set_swap ?x ?y ({[?z]})] =>
      rewrite (set_swap_singleton x y z)
  | H : context[set_swap ?x ?y (?X ∪ ?Y)] |- _ =>
      rewrite (set_swap_union x y X Y) in H
  | |- context[set_swap ?x ?y (?X ∪ ?Y)] =>
      rewrite (set_swap_union x y X Y)
  | H : context[set_swap ?x ?y (?X ∩ ?Y)] |- _ =>
      rewrite (set_swap_intersection x y X Y) in H
  | |- context[set_swap ?x ?y (?X ∩ ?Y)] =>
      rewrite (set_swap_intersection x y X Y)
  | H : context[set_swap ?x ?y (set_swap ?x ?y ?D)] |- _ =>
      rewrite (set_swap_involutive x y D) in H
  | |- context[set_swap ?x ?y (set_swap ?x ?y ?D)] =>
      rewrite (set_swap_involutive x y D)
  | H : ?z ∈ set_swap ?x ?y ?D |- _ =>
      rewrite (set_swap_elem x y z D) in H
  | |- ?z ∈ set_swap ?x ?y ?D =>
      rewrite (set_swap_elem x y z D)
  end.

Ltac base_swap_normalize := repeat base_swap_normalize_step.

Ltac better_base_solver :=
  base_swap_normalize;
  map_normalize;
  set_normalize;
  first
    [ solve [reflexivity]
    | solve [congruence]
    | solve [better_map_solver]
    | solve [better_set_solver]
    | solve [eauto 8] ].
