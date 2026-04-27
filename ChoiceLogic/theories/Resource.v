From ChoiceLogic Require Import Prelude Substitution.

(** * Resources  (Definitions 1.2–1.5)

    A *world* is any set of substitutions (Subst → Prop).
    A world is a (well-formed) *resource* in the sense of the paper when it satisfies
    the predicate [wf_resource]: non-emptiness and a common domain for all members. *)

Section Resource.

Context `{Countable Var} `{EqDecision Value} `{Inhabited Value}.

Local Notation SubstT := (gmap Var Value) (only parsing).

(** ** Worlds *)

Definition World : Type := SubstT → Prop.

(** ** Well-formedness / “resource” worlds  (Definition 1.2) *)

Definition wf_resource (w : World) : Prop :=
  (∃ σ, w σ) ∧ (∀ σ1 σ2, w σ1 → w σ2 → dom σ1 = dom σ2).

(** ** Compatibility of worlds  (extended from Definition 1.2) *)

Definition world_compat (m1 m2 : World) : Prop :=
  ∀ σ1 σ2, m1 σ1 → m2 σ2 → subst_compat σ1 σ2.

(** ** Resource operations  (Definition 1.3) *)

(** Resource product m1 × m2 : pairwise union of compatible substitutions.
    It is used under the side condition [world_compat m1 m2] (Definition 1.3). *)
Definition res_product (m1 m2 : World) : World :=
  λ σ, ∃ σ1 σ2, m1 σ1 ∧ m2 σ2 ∧ subst_compat σ1 σ2 ∧ σ = σ1 ∪ σ2.

(** Resource sum m1 + m2 : set union (defined when domains agree). *)
Definition res_sum (m1 m2 : World) : World :=
  λ σ, m1 σ ∨ m2 σ.

(** Unit resource: the singleton containing only the empty substitution. *)
Definition res_unit : World := λ σ, σ = ∅.

(** Definedness condition for the sum: elements from both sides share the same domain. *)
Definition res_sum_defined (m1 m2 : World) : Prop :=
  ∀ σ1 σ2, m1 σ1 → m2 σ2 → dom σ1 = dom σ2.

(** ** Restriction  (Definition 1.2, extended) *)

Definition res_restrict (m : World) (X : gset Var) : World :=
  λ σ, ∃ σ', m σ' ∧ subst_restrict σ' X = σ.

(** ** Fiber over a projection  (Definition 1.5) *)

Definition fiber (m : World) (σ : SubstT) : World :=
  fiber_set m σ.

(** ** Partial order  (Definition 1.4)

    m1 ≤ m2 iff m2 restricted to the domain of m1 equals m1, i.e.,
    { σ'|_{dom(m1)} | σ' ∈ m2 } = m1. *)

Definition res_le (m1 m2 : World) : Prop :=
  (** Every element of m1 arises as a restriction of some element of m2. *)
  (∀ σ1, m1 σ1 → ∃ σ2, m2 σ2 ∧ subst_restrict σ2 (dom σ1) = σ1) ∧
  (** Every restriction of a m2-element to any m1-element's domain is back in m1. *)
  (∀ σ1 σ2, m1 σ1 → m2 σ2 → m1 (subst_restrict σ2 (dom σ1))).

Local Infix "≤ᵣ" := res_le (at level 70).

(** ** Validity / closure lemmas *)

Lemma wf_res_unit : wf_resource res_unit.
Proof.
  split.
  - exists ∅. reflexivity.
  - intros σ1 σ2 H1 H2. unfold res_unit in H1, H2. hauto.
Qed.

Lemma res_product_valid (m1 m2 : World) :
  wf_resource m1 → wf_resource m2 →
  world_compat m1 m2 →
  wf_resource (res_product m1 m2).
Proof.
  intros H1 H2 Hcomp.
  split.
  - destruct H1 as ([σ1 H1] & Hdom1). destruct H2 as ([σ2 H2] & Hdom2).
    exists (σ1 ∪ σ2). exists σ1, σ2. hauto.
  - intros σ1 σ2 Hp1 Hp2.
    destruct H1 as ([σ1' H1] & Hdom1). destruct H2 as ([σ2' H2] & Hdom2).
    destruct Hp1 as (σ11 & σ12 & H11 & H12 & Hcomp1 & Hσ11).
    destruct Hp2 as (σ21 & σ22 & H21 & H22 & Hcomp2 & Hσ21). subst.
    specialize (Hdom1 σ11 σ21 H11 H21).
    specialize (Hdom2 σ12 σ22 H12 H22).
    repeat rewrite subst_union_dom; eauto. hauto.
Qed.

Lemma res_sum_valid (m1 m2 : World) :
  wf_resource m1 → wf_resource m2 →
  res_sum_defined m1 m2 →
  wf_resource (res_sum m1 m2).
Proof.
  intros [Hne1 Hdom1] [Hne2 Hdom2] Hdef.
  split.
  - destruct Hne1 as [σ1 H1]. exists σ1. left. exact H1.
  - intros σ1 σ2 [H1|H1] [H2|H2].
    + exact (Hdom1 σ1 σ2 H1 H2).
    + exact (Hdef σ1 σ2 H1 H2).
    + symmetry. exact (Hdef σ2 σ1 H2 H1).
    + exact (Hdom2 σ1 σ2 H1 H2).
Qed.

Lemma res_restrict_valid (m : World) (X : gset Var) :
  wf_resource m →
  (∃ σ, m σ ∧ dom σ ∩ X ≠ ∅) →   (* X overlaps the domain *)
  wf_resource (res_restrict m X).
Proof.
  intros [Hne Hdom] Hoverlap.
  split.
  - destruct Hoverlap as [σ [Hσ _]].
    exists (subst_restrict σ X). exists σ. split; [exact Hσ | reflexivity].
  - intros σ1 σ2 [σ1' [H1' Hrestr1]] [σ2' [H2' Hrestr2]].
    subst.
    rewrite !subst_restrict_dom.
    Admitted.

(** The unit resource is compatible with every world. *)
Lemma world_compat_unit_l (m : World) : world_compat res_unit m.
Proof.
  unfold world_compat, res_unit, subst_compat.
  intros σ1 σ2 H1 H2 x v1 v2 Hv1 Hv2.
  subst. rewrite lookup_empty in Hv1. discriminate.
Qed.

Lemma world_compat_unit_r (m : World) : world_compat m res_unit.
Proof.
  unfold world_compat, res_unit, subst_compat.
  intros σ1 σ2 H1 H2 x v1 v2 Hv1 Hv2.
  subst. rewrite lookup_empty in Hv2. discriminate.
Qed.

(** ** Partial order properties *)

Lemma res_le_refl (m : World) : m ≤ᵣ m.
Proof. Admitted.

Lemma res_le_antisym (m1 m2 : World) :
  wf_resource m1 → wf_resource m2 →
  m1 ≤ᵣ m2 → m2 ≤ᵣ m1 →
  ∀ σ, m1 σ ↔ m2 σ.
Proof. Admitted.

Lemma res_le_trans (m1 m2 m3 : World) :
  m1 ≤ᵣ m2 → m2 ≤ᵣ m3 → m1 ≤ᵣ m3.
Proof. Admitted.

(** ** Key algebraic property: m1 ≤ m1 × m2  (paragraph after Definition 1.3) *)

Lemma res_le_product_l (m1 m2 : World) :
  wf_resource m1 → wf_resource m2 →
  world_compat m1 m2 →
  m1 ≤ᵣ res_product m1 m2.
Proof. Admitted.

(** Addition is NOT monotone in general (unlike IL / OL). *)
(** The following counterexample is left as a note: see paper §1.2. *)

(** ** Bifunctoriality of × and + w.r.t. ≤ *)

Lemma res_product_le_mono (m1 m2 m1' m2' : World) :
  m1 ≤ᵣ m1' → m2 ≤ᵣ m2' →
  world_compat m1 m2 →
  world_compat m1' m2' →
  res_product m1 m2 ≤ᵣ res_product m1' m2'.
Proof. Admitted.

Lemma res_sum_le_mono (m1 m2 m1' m2' : World) :
  m1 ≤ᵣ m1' → m2 ≤ᵣ m2' →
  res_sum_defined m1 m2 →
  res_sum_defined m1' m2' →
  res_sum m1 m2 ≤ᵣ res_sum m1' m2'.
Proof. Admitted.

(** ** Commutativity and associativity (when defined) *)

Lemma res_product_comm (m1 m2 : World) :
  world_compat m1 m2 →
  ∀ σ, res_product m1 m2 σ ↔ res_product m2 m1 σ.
Proof.
  intros Hcomp σ. unfold res_product. split.
  - intros (σ1 & σ2 & H1 & H2 & Hc & Heq).
    exists σ2, σ1. repeat split.
    + exact H2.
    + exact H1.
    + exact (subst_compat_sym _ _ Hc).
    + subst. apply map_eq. intros i.
      unfold subst_compat in Hc.
      destruct (σ1 !! i) as [v1|] eqn:E1, (σ2 !! i) as [v2|] eqn:E2.
Admitted.

Lemma res_product_assoc (m1 m2 m3 : World) :
  world_compat m1 m2 →
  world_compat (res_product m1 m2) m3 →
  ∀ σ, res_product (res_product m1 m2) m3 σ ↔
       res_product m1 (res_product m2 m3) σ.
Proof. Admitted.

Lemma res_product_unit_r (m : World) :
  wf_resource m →
  ∀ σ, res_product m res_unit σ ↔ m σ.
Proof.
  intros [Hne Hdom] σ.
  unfold res_product, res_unit. split.
  - intros (σ1 & σ2 & H1 & H2 & Hcomp & Heq). subst.
Admitted.

Lemma res_sum_comm (m1 m2 : World) :
  ∀ σ, res_sum m1 m2 σ ↔ res_sum m2 m1 σ.
Proof. intros σ. unfold res_sum. hauto. Qed.

Lemma res_sum_assoc (m1 m2 m3 : World) :
  ∀ σ, res_sum (res_sum m1 m2) m3 σ ↔ res_sum m1 (res_sum m2 m3) σ.
Proof. intros σ. unfold res_sum. hauto. Qed.

(** The fiber of a valid world with σ is a sub-world (not necessarily valid). *)
Lemma fiber_sub (m : World) (σ : SubstT) :
  ∀ σ', fiber m σ σ' → m σ'.
Proof. intros σ' [Hin _]. exact Hin. Qed.

Lemma fiber_valid (m : World) (σ : SubstT) :
  wf_resource m →
  (∃ σ', fiber m σ σ') →
  wf_resource (fiber m σ).
Proof.
  intros [_ Hdom] Hne.
  split.
  - exact Hne.
  - intros σ1 σ2 [H1 _] [H2 _].
    exact (Hdom σ1 σ2 H1 H2).
Qed.

End Resource.

(** Section [Var] / [Value] parameters discharge over exported definitions. *)

Infix "≤ᵣ" := res_le (at level 70).
