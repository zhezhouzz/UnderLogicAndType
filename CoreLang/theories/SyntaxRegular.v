(** * Regular facts for core syntax. *)

From CoreLang Require Export SyntaxCore.
From ContextBase Require Import BaseTactics.

Lemma fv_value_swap_atom x y v :
  fv_value (value_swap_atom x y v) = set_swap x y (fv_value v)
with fv_tm_swap_atom x y e :
  fv_tm (tm_swap_atom x y e) = set_swap x y (fv_tm e).
Proof.
  - destruct v; simpl; try reflexivity.
    + better_base_solver.
    + apply fv_tm_swap_atom.
    + apply fv_value_swap_atom.
  - destruct e; simpl.
    + apply fv_value_swap_atom.
    + rewrite !fv_tm_swap_atom. better_base_solver.
    + apply fv_value_swap_atom.
    + rewrite !fv_value_swap_atom. better_base_solver.
    + rewrite fv_value_swap_atom, !fv_tm_swap_atom. better_base_solver.
Qed.

Lemma value_swap_atom_involutive x y v :
  value_swap_atom x y (value_swap_atom x y v) = v
with tm_swap_atom_involutive x y e :
  tm_swap_atom x y (tm_swap_atom x y e) = e.
Proof.
  - destruct v; simpl; try reflexivity.
    + better_base_solver.
    + rewrite tm_swap_atom_involutive. reflexivity.
    + rewrite value_swap_atom_involutive. reflexivity.
  - destruct e; simpl; rewrite ?value_swap_atom_involutive,
      ?tm_swap_atom_involutive; reflexivity.
Qed.

Lemma value_swap_atom_fresh x y v :
  x ∉ fv_value v →
  y ∉ fv_value v →
  value_swap_atom x y v = v
with tm_swap_atom_fresh x y e :
  x ∉ fv_tm e →
  y ∉ fv_tm e →
  tm_swap_atom x y e = e.
Proof.
  - destruct v; simpl; intros Hx Hy; try reflexivity.
    + better_base_solver.
    + rewrite tm_swap_atom_fresh by set_solver. reflexivity.
    + rewrite value_swap_atom_fresh by set_solver. reflexivity.
  - destruct e; simpl; intros Hx Hy; try rewrite !value_swap_atom_fresh by set_solver;
      try rewrite !tm_swap_atom_fresh by set_solver; reflexivity.
Qed.

Lemma value_swap_atom_open x y k u v :
  value_swap_atom x y (open_value k u v) =
  open_value k (value_swap_atom x y u) (value_swap_atom x y v)
with tm_swap_atom_open x y k u e :
  tm_swap_atom x y (open_tm k u e) =
  open_tm k (value_swap_atom x y u) (tm_swap_atom x y e).
Proof.
  - destruct v; simpl; try reflexivity.
    + destruct (decide (k = n)); reflexivity.
    + rewrite tm_swap_atom_open. reflexivity.
    + rewrite value_swap_atom_open. reflexivity.
  - destruct e; simpl; try rewrite ?value_swap_atom_open;
      try rewrite ?tm_swap_atom_open; reflexivity.
Qed.

Lemma open_value_swap_atom x y k z v :
  open_value k (vfvar z) (value_swap_atom x y v) =
  value_swap_atom x y (open_value k (vfvar (swap x y z)) v).
Proof.
  rewrite value_swap_atom_open. simpl.
  better_base_solver.
Qed.

Lemma open_tm_swap_atom x y k z e :
  open_tm k (vfvar z) (tm_swap_atom x y e) =
  tm_swap_atom x y (open_tm k (vfvar (swap x y z)) e).
Proof.
  rewrite tm_swap_atom_open. simpl.
  better_base_solver.
Qed.

(** ** Single-variable substitution *)

