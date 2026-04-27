From ChoiceAlgebra Require Import Prelude Store.

(** * Resources  (Definitions 1.2–1.5)

    A [World] is a record bundling:
      - [world_dom]    : the shared domain of all stores in this world
      - [world_stores] : the collection of stores (all with domain [world_dom])

    Well-formedness ([wf_world]) is an independent predicate requiring
    non-emptiness and the domain invariant.  Keeping it separate lets
    resource operations remain total functions. *)

Section Resource.

Context `{Countable Var} `{EqDecision Value} `{Inhabited Value}.

Local Notation StoreT := (gmap Var Value) (only parsing).

(** ** Worlds *)

Record World := mk_world {
  world_dom    : gset Var;
  world_stores : StoreT → Prop;
}.

(** Coercion: treat a World as a predicate on stores.
    Enables [m s] notation in place of [world_stores m s]. *)
Coercion world_stores : World >-> Funclass.

(** ** Well-formedness (Definition 1.2)

    [wf_world m] records two invariants:
    - [wf_ne]  : the world is non-empty
    - [wf_dom] : every store in the world has exactly the declared domain

    The second condition replaces the old [∀ s1 s2, m s1 → m s2 → dom s1 = dom s2],
    which required comparing two members to talk about the domain. *)
Record wf_world (m : World) : Prop := {
  wf_ne  : ∃ s, m s;
  wf_dom : ∀ s, m s → dom s = world_dom m;
}.

(** ** Compatibility of worlds  (Definition 1.2, extended) *)

Definition world_compat (m1 m2 : World) : Prop :=
  ∀ s1 s2, m1 s1 → m2 s2 → store_compat s1 s2.

(** ** Resource operations  (Definition 1.3) *)

(** Unit resource: domain ∅, only the empty store. *)
Definition res_unit : World := {|
  world_dom    := ∅;
  world_stores := λ s, s = ∅;
|}.

(** Resource product m1 × m2.
    Domain is the union of the two component domains. *)
Definition res_product (m1 m2 : World) : World := {|
  world_dom    := world_dom m1 ∪ world_dom m2;
  world_stores := λ s, ∃ s1 s2,
      m1 s1 ∧ m2 s2 ∧ store_compat s1 s2 ∧ s = s1 ∪ s2;
|}.

(** Resource sum m1 + m2: stores from either world.
    Domain is [world_dom m1]; well-formed only when [world_dom m1 = world_dom m2]. *)
Definition res_sum (m1 m2 : World) : World := {|
  world_dom    := world_dom m1;
  world_stores := λ s, m1 s ∨ m2 s;
|}.

(** Definedness condition for sum: the two worlds share the same domain. *)
Definition res_sum_defined (m1 m2 : World) : Prop :=
  world_dom m1 = world_dom m2.

(** Restriction of m to the variables in X.
    Domain shrinks to [world_dom m ∩ X]. *)
Definition res_restrict (m : World) (X : gset Var) : World := {|
  world_dom    := world_dom m ∩ X;
  world_stores := λ s, ∃ s', m s' ∧ store_restrict s' X = s;
|}.

(** Fiber of m over σ: stores in m that restrict to σ on dom(σ).
    Domain stays [world_dom m]. *)
Definition fiber (m : World) (σ : StoreT) : World := {|
  world_dom    := world_dom m;
  world_stores := λ s, m s ∧ store_restrict s (dom σ) = σ;
|}.

(** ** Partial order  (Definition 1.4) *)

Definition res_le (m1 m2 : World) : Prop :=
  (∀ s1, m1 s1 → ∃ s2, m2 s2 ∧ store_restrict s2 (dom s1) = s1) ∧
  (∀ s1 s2, m1 s1 → m2 s2 → m1 (store_restrict s2 (dom s1))).

Local Infix "≤ᵣ" := res_le (at level 70).

(** ** Well-formedness of operations *)

Lemma wf_res_unit : wf_world res_unit.
Proof. Admitted.

Lemma wf_res_product (m1 m2 : World) :
  wf_world m1 → wf_world m2 → world_compat m1 m2 →
  wf_world (res_product m1 m2).
Proof. Admitted.

Lemma wf_res_sum (m1 m2 : World) :
  wf_world m1 → wf_world m2 → res_sum_defined m1 m2 →
  wf_world (res_sum m1 m2).
Proof. Admitted.

Lemma wf_res_restrict (m : World) (X : gset Var) :
  wf_world m →
  (∃ s, m s ∧ dom s ∩ X ≠ ∅) →
  wf_world (res_restrict m X).
Proof. Admitted.

Lemma wf_fiber (m : World) (σ : StoreT) :
  wf_world m →
  (∃ s, m s ∧ store_restrict s (dom σ) = σ) →
  wf_world (fiber m σ).
Proof. Admitted.

(** ** Compatibility lemmas *)

Lemma world_compat_unit_l (m : World) : world_compat res_unit m.
Proof.
  unfold world_compat, store_compat. simpl.
  intros s1 s2 H1 H2 x v1 v2 Hv1 Hv2.
  subst. rewrite lookup_empty in Hv1. discriminate.
Qed.

Lemma world_compat_unit_r (m : World) : world_compat m res_unit.
Proof.
  unfold world_compat, store_compat. simpl.
  intros s1 s2 H1 H2 x v1 v2 Hv1 Hv2.
  subst. rewrite lookup_empty in Hv2. discriminate.
Qed.

(** ** Partial order properties *)

Lemma res_le_refl (m : World) : m ≤ᵣ m.
Proof. Admitted.

Lemma res_le_antisym (m1 m2 : World) :
  wf_world m1 → wf_world m2 →
  m1 ≤ᵣ m2 → m2 ≤ᵣ m1 →
  ∀ s, m1 s ↔ m2 s.
Proof. Admitted.

Lemma res_le_trans (m1 m2 m3 : World) :
  m1 ≤ᵣ m2 → m2 ≤ᵣ m3 → m1 ≤ᵣ m3.
Proof. Admitted.

Lemma res_le_product_l (m1 m2 : World) :
  wf_world m1 → wf_world m2 → world_compat m1 m2 →
  m1 ≤ᵣ res_product m1 m2.
Proof. Admitted.

Lemma res_product_le_mono (m1 m2 m1' m2' : World) :
  m1 ≤ᵣ m1' → m2 ≤ᵣ m2' →
  world_compat m1 m2 → world_compat m1' m2' →
  res_product m1 m2 ≤ᵣ res_product m1' m2'.
Proof. Admitted.

Lemma res_sum_le_mono (m1 m2 m1' m2' : World) :
  m1 ≤ᵣ m1' → m2 ≤ᵣ m2' →
  res_sum_defined m1 m2 → res_sum_defined m1' m2' →
  res_sum m1 m2 ≤ᵣ res_sum m1' m2'.
Proof. Admitted.

(** ** Commutativity and associativity *)

Lemma res_product_comm (m1 m2 : World) :
  world_compat m1 m2 →
  ∀ s, res_product m1 m2 s ↔ res_product m2 m1 s.
Proof. Admitted.

Lemma res_product_assoc (m1 m2 m3 : World) :
  world_compat m1 m2 →
  world_compat (res_product m1 m2) m3 →
  ∀ s, res_product (res_product m1 m2) m3 s ↔
       res_product m1 (res_product m2 m3) s.
Proof. Admitted.

Lemma res_product_unit_r (m : World) :
  wf_world m → ∀ s, res_product m res_unit s ↔ m s.
Proof. Admitted.

Lemma res_sum_comm (m1 m2 : World) :
  res_sum_defined m1 m2 →
  ∀ s, res_sum m1 m2 s ↔ res_sum m2 m1 s.
Proof. intros _. intros s. unfold res_sum. simpl. tauto. Qed.

Lemma res_sum_assoc (m1 m2 m3 : World) :
  ∀ s, res_sum (res_sum m1 m2) m3 s ↔ res_sum m1 (res_sum m2 m3) s.
Proof. intros s. unfold res_sum. simpl. tauto. Qed.

(** ** Fiber properties *)

Lemma fiber_sub (m : World) (σ : StoreT) :
  ∀ s, fiber m σ s → m s.
Proof. intros s [Hin _]. exact Hin. Qed.

Lemma wf_fiber_valid (m : World) (σ : StoreT) :
  wf_world m →
  (∃ s, fiber m σ s) →
  wf_world (fiber m σ).
Proof.
  intros Hwf Hne.
  apply wf_fiber; [exact Hwf | exact Hne].
Qed.

End Resource.

Infix "≤ᵣ" := res_le (at level 70).
