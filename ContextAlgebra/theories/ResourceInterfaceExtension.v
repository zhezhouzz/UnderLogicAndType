(** * Concrete resource extension interface lemmas *)

From ContextPrelude Require Import Prelude Store.
From ContextAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict ResourceAlgebra ResourceExtension ResourceExtensionDerived.
From ContextAlgebra Require Export ResourceInterfaceOrder.
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

Lemma extension_applicable_product_r_fresh
    (n m : WfWorld) (F : @fiber_extension V)
    (Hc_m : world_compat n m) :
  extA_out F ## world_dom (n : World) ->
  extension_applicable F m ->
  extension_applicable F (res_product n m Hc_m).
Proof.
  intros Hout_n Happ.
  constructor.
  - cbn. pose proof (extA_app_in _ _ Happ). set_solver.
  - cbn. pose proof (extA_app_out _ _ Happ). set_solver.
Qed.

Lemma world_compat_restrict_l_extend_by_fresh
    (n m mx : WfWorld) (F : @fiber_extension V) (X : aset) :
  extA_out F ## X ->
  m #> F ~~> mx ->
  world_compat n m ->
  world_compat (res_restrict n X) mx.
Proof.
  intros HoutX [Happ [_ Hstores]] Hc σnX σmx HσnX Hσmx.
  simpl in HσnX.
  destruct HσnX as [σn [Hσn Hrestrict]]. subst σnX.
  apply Hstores in Hσmx as
    (σm & we & σe & Hσm & HF & Hσe & ->).
  apply storeA_compat_union_intro_r.
  - apply storeA_compat_sym.
    apply storeA_compat_restrict_r.
    apply storeA_compat_sym.
    exact (Hc σn σm Hσn Hσm).
  - apply storeA_disj_dom_compat.
    pose proof (extA_output_store_dom_from_base m F σm we σe
      Happ Hσm HF Hσe) as Hdomσe.
    change (dom (storeA_restrict σn X : gmap atom V) ∩
      dom (σe : gmap atom V) = ∅).
    pose proof (@storeA_restrict_dom V atom _ _ σn X) as HdomσnX.
    change (dom (storeA_restrict σn X : gmap atom V) =
      dom (σn : gmap atom V) ∩ X) in HdomσnX.
    rewrite HdomσnX, Hdomσe.
    set_solver.
Qed.

Lemma res_extend_by_product_r_store_forward
    (n m mx : WfWorld) (F : @fiber_extension V)
    (Hc_m : world_compat n m) (Hc_mx : world_compat n mx) σ :
  extA_out F ## world_dom (n : World) ->
  m #> F ~~> mx ->
  (res_product n mx Hc_mx : World) σ ->
  ∃ σbase we σe,
    (res_product n m Hc_m : World) σbase ∧
    extA_rel F (storeA_restrict σbase (extA_in F)) we ∧
    (we : World) σe ∧
    σ = σbase ∪ σe.
Proof.
  intros Hout_n [Happ [_ Hstores_mx]]
    (σn & σmx & Hσn & Hσmx & Hcompat_n_mx & ->).
  apply Hstores_mx in Hσmx as
    (σm & we & σe & Hσm & HF & Hσe & ->).
  exists (σn ∪ σm), we, σe.
  split.
  - exists σn, σm.
    split; [exact Hσn|].
    split; [exact Hσm|].
    split; [exact (Hc_m σn σm Hσn Hσm)|].
    reflexivity.
  - split.
    + assert (Hrestr :
      @storeA_restrict V atom _ _
        (@union (gmap atom V) _ (σn : gmap atom V) (σm : gmap atom V))
        (extA_in F) =
      @storeA_restrict V atom _ _ σm (extA_in F)).
      {
        apply storeA_restrict_union_absorb_r.
        - exact (Hc_m σn σm Hσn Hσm).
        - pose proof (wfworld_store_dom m σm Hσm) as Hdom_m.
          change (dom (σm : gmap atom V) = world_dom (m : World)) in Hdom_m.
          rewrite Hdom_m.
          exact (extA_app_in _ _ Happ).
      }
      change (extA_rel F
        (@storeA_restrict V atom _ _
          (@union (gmap atom V) _ (σn : gmap atom V) (σm : gmap atom V))
          (extA_in F)) we).
      rewrite Hrestr. exact HF.
    + split.
      * exact Hσe.
      * change ((σn : gmap atom V) ∪ ((σm : gmap atom V) ∪ (σe : gmap atom V)) =
          ((σn : gmap atom V) ∪ (σm : gmap atom V)) ∪ (σe : gmap atom V)).
        exact (@assoc_L (gmap atom V) union _
          (σn : gmap atom V) (σm : gmap atom V) (σe : gmap atom V)).
Qed.

Lemma res_extend_by_product_r_store_backward
    (n m mx : WfWorld) (F : @fiber_extension V)
    (Hc_m : world_compat n m) (Hc_mx : world_compat n mx) σ :
  extA_out F ## world_dom (n : World) ->
  m #> F ~~> mx ->
  (∃ σbase we σe,
    (res_product n m Hc_m : World) σbase ∧
    extA_rel F (storeA_restrict σbase (extA_in F)) we ∧
    (we : World) σe ∧
    σ = σbase ∪ σe) ->
  (res_product n mx Hc_mx : World) σ.
Proof.
  intros Hout_n [Happ [_ Hstores_mx]]
    (σnm & we & σe & Hσnm & HF & Hσe & ->).
  destruct Hσnm as
    (σn & σm & Hσn & Hσm & Hcompat_n_m & ->).
  assert (Hrestr :
      @storeA_restrict V atom _ _
        (@union (gmap atom V) _ (σn : gmap atom V) (σm : gmap atom V))
        (extA_in F) =
      @storeA_restrict V atom _ _ σm (extA_in F)).
  {
    apply storeA_restrict_union_absorb_r.
    - exact Hcompat_n_m.
    - pose proof (wfworld_store_dom m σm Hσm) as Hdom_m.
      change (dom (σm : gmap atom V) = world_dom (m : World)) in Hdom_m.
      rewrite Hdom_m.
      exact (extA_app_in _ _ Happ).
  }
  change (extA_rel F
    (@storeA_restrict V atom _ _
      (@union (gmap atom V) _ (σn : gmap atom V) (σm : gmap atom V))
      (extA_in F)) we) in HF.
  rewrite Hrestr in HF.
  exists σn, (σm ∪ σe).
  repeat split.
  - exact Hσn.
  - apply Hstores_mx.
    exists σm, we, σe.
    split; [exact Hσm|].
    split; [exact HF|].
    split; [exact Hσe|].
    reflexivity.
  - apply storeA_compat_union_intro_r.
    + exact Hcompat_n_m.
    + apply storeA_disj_dom_compat.
      pose proof (wfworld_store_dom n σn Hσn) as Hdom_n.
	      pose proof (wfworld_store_dom we σe Hσe) as Hdom_e.
	      change (dom (σn : gmap atom V) = world_dom (n : World)) in Hdom_n.
	      change (dom (σe : gmap atom V) = world_dom (we : World)) in Hdom_e.
	      rewrite Hdom_n.
	      pose proof (extA_output_store_dom_from_base m F σm we σe
	        Happ Hσm HF Hσe) as Hdom_σe.
	      rewrite Hdom_σe. set_solver.
  - change (((σn : gmap atom V) ∪ (σm : gmap atom V)) ∪ (σe : gmap atom V) =
      (σn : gmap atom V) ∪ ((σm : gmap atom V) ∪ (σe : gmap atom V))).
    exact (eq_sym (@assoc_L (gmap atom V) union _
      (σn : gmap atom V) (σm : gmap atom V) (σe : gmap atom V))).
Qed.

Lemma res_extend_by_product_r_fresh
    (n m mx : WfWorld) (F : @fiber_extension V)
    (Hc_m : world_compat n m) (Hc_mx : world_compat n mx) :
  extA_out F ## world_dom (n : World) ->
  m #> F ~~> mx ->
  res_product n m Hc_m #> F ~~> res_product n mx Hc_mx.
Proof.
  intros Hout_n Hext.
  pose proof (res_extend_by_applicable m F mx Hext) as Happ.
  pose proof (res_extend_by_dom m F mx Hext) as Hdom_mx.
  split.
  - eapply extension_applicable_product_r_fresh; eauto.
  - split.
    + change (world_dom (n : World) ∪ world_dom (mx : World) =
        (world_dom (n : World) ∪ world_dom (m : World)) ∪ extA_out F).
      rewrite Hdom_mx. set_solver.
    + intros σ. split.
      * eapply res_extend_by_product_r_store_forward; eauto.
      * eapply res_extend_by_product_r_store_backward; eauto.
Qed.

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
