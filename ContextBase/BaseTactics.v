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

Ltac base_open_env_normalize_step :=
  match goal with
  | H : context[logic_var_open_env ∅ ?v] |- _ =>
      rewrite (logic_var_open_env_empty v) in H
  | |- context[logic_var_open_env ∅ ?v] =>
      rewrite (logic_var_open_env_empty v)
  | H : context[lvars_open_env ∅ ?D] |- _ =>
      rewrite (lvars_open_env_empty D) in H
  | |- context[lvars_open_env ∅ ?D] =>
      rewrite (lvars_open_env_empty D)
  | H : context[lvars_open_env ?η (?D ∪ ?E)] |- _ =>
      rewrite (lvars_open_env_union η D E) in H
  | |- context[lvars_open_env ?η (?D ∪ ?E)] =>
      rewrite (lvars_open_env_union η D E)
  | H : context[(kmap S ?η) !! 0] |- _ =>
      rewrite (open_env_lift_lookup_zero_none η) in H
  | |- context[(kmap S ?η) !! 0] =>
      rewrite (open_env_lift_lookup_zero_none η)
  | Hnone : ?η !! ?k = None,
    H : context[(kmap S ?η) !! S ?k] |- _ =>
      rewrite (open_env_lift_lookup_none η k Hnone) in H
  | Hnone : ?η !! ?k = None
    |- context[(kmap S ?η) !! S ?k] =>
      rewrite (open_env_lift_lookup_none η k Hnone)
  | H : context[open_env_atoms ∅] |- _ =>
      rewrite open_env_atoms_empty in H
  | |- context[open_env_atoms ∅] =>
      rewrite open_env_atoms_empty
  | Hnone : ?η !! ?k = None,
    H : context[open_env_atoms (<[?k := ?x]> ?η)] |- _ =>
      rewrite (open_env_atoms_insert k x η Hnone) in H
  | Hnone : ?η !! ?k = None
    |- context[open_env_atoms (<[?k := ?x]> ?η)] =>
      rewrite (open_env_atoms_insert k x η Hnone)
  end.

Ltac base_open_env_normalize := repeat base_open_env_normalize_step.

#[global] Hint Resolve
  open_env_avoids_atom_empty
  open_env_avoids_atom_lift
  open_env_avoids_atom_of_notin_atoms
  open_env_fresh_for_lvars_empty
  open_env_fresh_for_lvars_inj_on
  open_env_fresh_for_lvars_mono
  lvars_open_env_mono
  lvars_fv_open_env_lookup
  lvars_fv_open_env_free
  : base_solver.

Ltac better_base_solver :=
  base_swap_normalize;
  base_open_env_normalize;
  map_normalize;
  set_normalize;
  first
    [ solve [reflexivity]
    | solve [apply swap_involutive]
    | solve [apply swap_sym]
    | solve [apply swap_l]
    | solve [apply swap_r]
    | solve [apply swap_fresh; congruence]
    | solve [apply set_swap_involutive]
    | solve [apply set_swap_sym]
    | solve [apply set_swap_conjugate]
    | solve [apply set_swap_conjugate_inv]
    | solve [apply set_swap_fresh; better_set_solver]
    | solve
        [ match goal with
          | H : open_env_fresh_for_lvars ?η ?D
            |- logic_var_open_env_inj_on ?η ?D =>
              exact (open_env_fresh_for_lvars_inj_on η D H)
          end ]
    | solve [congruence]
    | solve [better_map_solver]
    | solve [better_set_solver]
    | solve [eauto 8 with base_solver] ].
