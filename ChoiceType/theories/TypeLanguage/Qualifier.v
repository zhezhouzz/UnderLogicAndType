(** * ChoiceType.TypeLanguage.Qualifier

    Type-level qualifiers are locally-nameless predicates over lvar-keyed
    stores.  This mirrors [LogicQualifier]'s dependent-domain design, except
    the payload is an [LStore] rather than an [LWorld].

    The core language operation is opening.  Opening is implemented as a swap
    between a bound lvar and a free atom, with the predicate interpreting its
    input after swapping the store back. *)

From CoreLang Require Export Prelude Syntax.
From ChoicePrelude Require Export Store.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.ProofIrrelevance.

Local Notation LStoreT := (LStore (V := value)) (only parsing).

Lemma lstore_restrict_dom (s : LStoreT) (X : lvset) :
  dom (lstore_restrict s X : LStoreT) = dom (s : LStoreT) ∩ X.
Proof.
Admitted.

Lemma lstore_swap_dom (a b : logic_var) (s : LStoreT) :
  dom (lstore_swap a b s : LStoreT) = gset_swap a b (dom (s : LStoreT)).
Proof.
Admitted.

Record LStoreOn (D : lvset) : Type := {
  lso_store : LStoreT;
  lso_dom : dom (lso_store : LStoreT) = D;
}.

Arguments lso_store {_} _.
Arguments lso_dom {_} _.

Definition lstore_on_ext D (s1 s2 : LStoreOn D) :
  lso_store s1 = lso_store s2 ->
  s1 = s2.
Proof.
  destruct s1 as [s1 H1], s2 as [s2 H2]. simpl.
  intros ->. f_equal. apply proof_irrelevance.
Qed.

Definition lstore_on_restrict
    (D' : lvset) {D : lvset} (s : LStoreOn D)
    (Hsub : D' ⊆ D) : LStoreOn D'.
Proof.
  refine {| lso_store := lstore_restrict (lso_store s) D' |}.
  rewrite lstore_restrict_dom, (lso_dom s).
  set_solver.
Defined.

Definition lstore_on_swap
    (a b : logic_var) {D : lvset} (s : LStoreOn D)
    : LStoreOn (gset_swap a b D).
Proof.
  refine {| lso_store := lstore_swap a b (lso_store s) |}.
  rewrite lstore_swap_dom, (lso_dom s). reflexivity.
Defined.

Definition lstore_on_open_back
    (k : nat) (x : atom) (D : lvset)
    (s : LStoreOn (lvars_open k x D)) : LStoreOn D.
Proof.
  refine {| lso_store := lstore_swap (LVBound k) (LVFree x) (lso_store s) |}.
  rewrite lstore_swap_dom, (lso_dom s).
  rewrite lvars_open_unfold, gset_swap_involutive. reflexivity.
Defined.

Record type_qualifier : Type := tqual {
  qual_lvars : lvset;
  qual_prop : LStoreOn qual_lvars -> Prop;
}.

Definition qual_vars (q : type_qualifier) : lvset :=
  qual_lvars q.

Definition qual_dom (q : type_qualifier) : aset :=
  lvars_fv (qual_lvars q).

Definition qual_bvars (q : type_qualifier) : gset nat :=
  lvars_bv (qual_lvars q).

Definition qual_open_atom
    (k : nat) (x : atom) (q : type_qualifier) : type_qualifier :=
  match q with
  | tqual D P =>
      tqual (lvars_open k x D)
        (fun s => P (lstore_on_open_back k x D s))
  end.

Definition qual_top : type_qualifier :=
  tqual ∅ (fun _ => True).

Definition qual_and (q1 q2 : type_qualifier) : type_qualifier :=
  match q1, q2 with
  | tqual D1 P1, tqual D2 P2 =>
      tqual (D1 ∪ D2)
        (fun s =>
           P1 (lstore_on_restrict D1 s ltac:(set_solver)) /\
           P2 (lstore_on_restrict D2 s ltac:(set_solver)))
  end.

Definition lc_qualifier (q : type_qualifier) : Prop :=
  lc_lvars (qual_lvars q).

Definition body_qualifier (q : type_qualifier) : Prop :=
  exists L : aset, forall x : atom, x ∉ L -> lc_qualifier (qual_open_atom 0 x q).

#[global] Instance stale_qualifier : Stale type_qualifier := qual_dom.
Arguments stale_qualifier /.

#[global] Instance open_qual_atom_inst : Open atom type_qualifier := qual_open_atom.
Arguments open_qual_atom_inst /.

#[global] Instance lc_qual_inst : Lc type_qualifier := lc_qualifier.
Arguments lc_qual_inst /.

Notation "q '^q^' x" := (qual_open_atom 0 x q) (at level 20).
Notation "q1 '&q' q2" := (qual_and q1 q2) (at level 40).
Notation "⊤q" := qual_top.

Lemma qual_ext (q1 q2 : type_qualifier) :
  qual_lvars q1 = qual_lvars q2 ->
  (forall (s1 : LStoreOn (qual_lvars q1))
          (s2 : LStoreOn (qual_lvars q2)),
      lso_store s1 = lso_store s2 ->
      qual_prop q1 s1 <-> qual_prop q2 s2) ->
  q1 = q2.
Proof.
Admitted.

Lemma qual_open_atom_vars k x q :
  qual_vars (qual_open_atom k x q) = lvars_open k x (qual_vars q).
Proof.
  destruct q. reflexivity.
Qed.

Lemma qual_open_atom_dom_subset k x q :
  qual_dom (qual_open_atom k x q) ⊆ qual_dom q ∪ {[x]}.
Proof.
Admitted.

Lemma qual_open_atom_bvars k x q :
  qual_bvars (qual_open_atom k x q) =
    lvars_bv (lvars_open k x (qual_vars q)).
Proof.
  destruct q. reflexivity.
Qed.

Lemma qual_open_atom_lc_fresh k x q :
  lc_qualifier q ->
  x ∉ qual_dom q ->
  qual_open_atom k x q = q.
Proof.
Admitted.

Lemma qual_top_lc :
  lc_qualifier qual_top.
Proof.
Admitted.
