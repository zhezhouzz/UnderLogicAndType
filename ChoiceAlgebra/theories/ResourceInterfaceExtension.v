(** * Concrete resource extension interface lemmas *)

From ChoicePrelude Require Import Prelude Store.
From ChoiceAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict ResourceAlgebra ResourceExtension ResourceExtensionDerived.
From ChoiceAlgebra Require Export ResourceInterfaceOrder.
From Stdlib Require Import Logic.ProofIrrelevance.

Section ResourceInterface.

Context {V : Type} `{ValueSig V}.

Local Notation Store := (@Store V) (only parsing).
Local Notation World := (@World V) (only parsing).
Local Notation WfWorld := (@WfWorld V) (only parsing).

Local Notation "m '#>' F '~~>' n" := (res_extend_by m F n)
  (at level 70, F at next level, n at next level).

Lemma res_extend_by_restrict_base (m : WfWorld) (F : @fiber_extension V) (n : WfWorld) :
  m #> F ~~> n →
  res_restrict n (world_dom m) = m.
Proof. apply resA_extend_by_restrict_base. Qed.

Lemma res_extend_by_dom (m : WfWorld) (F : @fiber_extension V) (n : WfWorld) :
  m #> F ~~> n →
  world_dom (n : World) = world_dom (m : World) ∪ extA_out F.
Proof. apply resA_extend_by_dom. Qed.

Lemma res_extend_by_le (m : WfWorld) (F : @fiber_extension V) (n : WfWorld) :
  m #> F ~~> n →
  m ⊑ n.
Proof. apply resA_extend_by_le. Qed.

Lemma res_extend_by_applicable (m : WfWorld) (F : @fiber_extension V) (n : WfWorld) :
  m #> F ~~> n →
  extension_applicable F m.
Proof. apply resA_extend_by_applicable. Qed.

Lemma res_extend_by_input_dom (m : WfWorld) (F : @fiber_extension V) (n : WfWorld) :
  m #> F ~~> n →
  extA_in F ⊆ world_dom (m : World).
Proof.
  intros Hext.
  pose proof (res_extend_by_applicable m F n Hext) as Happ.
  exact (extA_app_in _ _ Happ).
Qed.

Lemma res_extend_by_output_fresh (m : WfWorld) (F : @fiber_extension V) (n : WfWorld) :
  m #> F ~~> n →
  extA_out F ## world_dom (m : World).
Proof.
  intros Hext.
  pose proof (res_extend_by_applicable m F n Hext) as Happ.
  exact (extA_app_out _ _ Happ).
Qed.

Lemma res_extend_by_exists (m : WfWorld) (F : @fiber_extension V) :
  extension_applicable F m →
  ∃ n, m #> F ~~> n.
Proof. apply resA_extend_by_exists. Qed.

Lemma res_extend_by_projection_eq
    (m n : WfWorld) (F : @fiber_extension V) (my ny : WfWorld) :
  res_restrict m (extA_in F) = res_restrict n (extA_in F) →
  m #> F ~~> my →
  n #> F ~~> ny →
  res_restrict my (extA_in F ∪ extA_out F) =
  res_restrict ny (extA_in F ∪ extA_out F).
Proof. apply resA_extend_by_projection_eq. Qed.

Lemma res_extend_by_commute
    (m : WfWorld) (F G : @fiber_extension V)
    (mF mG mFG mGF : WfWorld) :
  m #> F ~~> mF →
  m #> G ~~> mG →
  mF #> G ~~> mFG →
  mG #> F ~~> mGF →
  mFG = mGF.
Proof. apply resA_extend_by_commute. Qed.

Lemma res_extend_by_sum_pullback
    (m : WfWorld) F (n n1 n2 : WfWorld)
    (Hdef : raw_sum_defined (n1 : World) (n2 : World)) :
  m #> F ~~> n →
  fiber_extension_functional_on m F →
  world_dom (m : World) ⊆ world_dom (n1 : World) →
  world_dom (m : World) ⊆ world_dom (n2 : World) →
  res_sum n1 n2 Hdef ⊑ n →
  ∃ (m1 m2 : WfWorld) (Hdefm : raw_sum_defined m1 m2)
    (n1' n2' : WfWorld),
    world_dom (m1 : World) = world_dom (m : World) ∧
    world_dom (m2 : World) = world_dom (m : World) ∧
    res_subset m1 m ∧
    res_subset m2 m ∧
    res_sum m1 m2 Hdefm ⊑ m ∧
    m1 #> F ~~> n1' ∧
    n1 ⊑ n1' ∧
    m2 #> F ~~> n2' ∧
    n2 ⊑ n2'.
Proof. apply resA_extend_by_sum_pullback. Qed.

Lemma res_one_point_extension_pushout
    (m n my : WfWorld) (y : atom) :
  m ⊑ n →
  y ∉ world_dom (n : World) →
  world_dom (my : World) = world_dom (m : World) ∪ {[y]} →
  res_restrict my (world_dom (m : World)) = m →
  ∃ ny : WfWorld,
    world_dom (ny : World) = world_dom (n : World) ∪ {[y]} ∧
    res_restrict ny (world_dom (n : World)) = n ∧
    my ⊑ ny.
Proof. apply resA_one_point_extension_pushout. Qed.

End ResourceInterface.
