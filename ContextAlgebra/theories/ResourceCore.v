From ContextBase Require Import Prelude LogicVar BaseTactics.
From ContextStore Require Import Store.
From Stdlib Require Import Logic.PropExtensionality Logic.FunctionalExtensionality
  Logic.ProofIrrelevance.

(** * Abstract resources over a countable key *)

Section ResourceCoreA.

Context {K : Type} `{Countable K}.
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (gmap K V) (only parsing).

Record WorldA := mk_worldA {
  worldA_dom    : gset K;
  worldA_stores : StoreAT → Prop;
}.

Coercion worldA_stores : WorldA >-> Funclass.

Record wf_worldA (m : WorldA) : Prop := {
  wfA_ne  : ∃ σ, m σ;
  wfA_dom : ∀ σ, m σ → dom σ = worldA_dom m;
}.

Definition WfWorldA : Type := { m : WorldA | wf_worldA m }.

Coercion raw_worldA (w : WfWorldA) : WorldA := proj1_sig w.
Definition worldA_wf (w : WfWorldA) : wf_worldA (raw_worldA w) := proj2_sig w.

Lemma worldA_ext (m1 m2 : WorldA) :
  worldA_dom m1 = worldA_dom m2 →
  (∀ σ, m1 σ ↔ m2 σ) →
  m1 = m2.
Proof.
  destruct m1, m2. simpl. intros -> Hstores.
  f_equal. apply functional_extensionality. intros σ.
  apply propositional_extensionality. exact (Hstores σ).
Qed.

Lemma wfworldA_ext (w1 w2 : WfWorldA) :
  (w1 : WorldA) = (w2 : WorldA) →
  w1 = w2.
Proof.
  destruct w1 as [m1 Hwf1], w2 as [m2 Hwf2]. simpl.
  intros ->. f_equal. apply proof_irrelevance.
Qed.

Lemma wfworldA_store_dom (w : WfWorldA) (σ : StoreAT) :
  w σ → dom σ = worldA_dom (w : WorldA).
Proof. apply (wfA_dom _ (worldA_wf w)). Qed.

Lemma wfworldA_store_dom_subset (w : WfWorldA) (σ : StoreAT) (X : gset K) :
  w σ →
  worldA_dom (w : WorldA) ⊆ X →
  dom σ ⊆ X.
Proof.
  intros Hσ HX. rewrite (wfworldA_store_dom w σ Hσ). exact HX.
Qed.



(** ** Key actions lifted from stores to resources *)

Local Notation WorldAT := WorldA (only parsing).
Local Notation WfWorldAT := WfWorldA (only parsing).

Definition rawA_rekey (f : K → K) (m : WorldAT) : WorldAT := {|
  worldA_dom    := set_map f (worldA_dom m);
  worldA_stores := λ σ, ∃ σ0 : StoreAT,
    m σ0 ∧ storeA_map_key f σ0 = σ;
|}.

Definition resA_rekey (f : K → K) (Hf : Inj (=) (=) f)
    (w : WfWorldAT) : WfWorldAT.
Proof.
  refine (exist _ (rawA_rekey f w) _).
  destruct (worldA_wf w) as [Hne Hdom].
  split.
  - destruct Hne as [σ Hσ].
    exists (storeA_map_key f σ). exists σ. split; [exact Hσ | reflexivity].
  - intros σ [σ0 [Hσ0 Hrekey]].
    rewrite <- Hrekey.
    change (dom (storeA_map_key f σ0 : gmap K V) =
      set_map f (worldA_dom (w : WorldAT) : gset K)).
    rewrite storeA_rekey_dom by exact Hf.
    pose proof (Hdom σ0 Hσ0) as Hσdom.
    change (dom (σ0 : gmap K V) = worldA_dom (w : WorldAT)) in Hσdom.
    rewrite Hσdom. reflexivity.
Defined.

Definition rawA_swap (x y : K) (m : WorldAT) : WorldAT :=
  rawA_rekey (swap x y) m.

Definition resA_swap (x y : K) (w : WfWorldAT) : WfWorldAT :=
  resA_rekey (swap x y) (swap_inj x y) w.

Lemma resA_swap_involutive (x y : K) (w : WfWorldAT) :
  resA_swap x y (resA_swap x y w) = w.
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. better_base_solver.
  - intros σ. simpl. split.
    + intros [σ1 [[σ0 [Hσ0 Hswap0]] Hswap1]].
      rewrite <- Hswap1, <- Hswap0.
      change (w (storeA_swap x y
        (storeA_swap x y σ0))).
      rewrite storeA_swap_involutive. exact Hσ0.
    + intros Hσ.
      exists (storeA_swap x y σ). split.
      * exists σ. split; [exact Hσ | reflexivity].
      * change (storeA_swap x y
          (storeA_swap x y σ) = σ).
        apply storeA_swap_involutive.
Qed.

Lemma resA_swap_sym (x y : K) (w : WfWorldAT) :
  resA_swap x y w = resA_swap y x w.
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. better_base_solver.
  - intros σ. simpl. split.
    + intros [σ0 [Hσ0 Hswap]]. exists σ0. split; [exact Hσ0 |].
      change (storeA_swap y x σ0 = σ).
      change (storeA_swap x y σ0 = σ) in Hswap.
      rewrite <- storeA_swap_sym. exact Hswap.
    + intros [σ0 [Hσ0 Hswap]]. exists σ0. split; [exact Hσ0 |].
      change (storeA_swap x y σ0 = σ).
      change (storeA_swap y x σ0 = σ) in Hswap.
      rewrite storeA_swap_sym. exact Hswap.
Qed.

Lemma resA_swap_conjugate a b x y (w : WfWorldAT) :
  resA_swap a b (resA_swap x y w) =
  resA_swap (swap a b x) (swap a b y) (resA_swap a b w).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. better_base_solver.
  - intros σ. simpl. split.
    + intros [σ0 [[σ1 [Hσ1 Hswap1]] Hswap0]]. subst σ0 σ.
      exists (storeA_swap a b σ1). split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * symmetry. apply storeA_swap_conjugate.
    + intros [σ0 [[σ1 [Hσ1 Hswap1]] Hswap0]]. subst σ0 σ.
      exists (storeA_swap x y σ1). split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * apply storeA_swap_conjugate.
Qed.

Lemma resA_swap_conjugate_inv a b x y (w : WfWorldAT) :
  resA_swap x y (resA_swap a b w) =
  resA_swap a b (resA_swap (swap a b x) (swap a b y) w).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. better_base_solver.
  - intros σ. simpl. split.
    + intros [σ0 [[σ1 [Hσ1 Hswap1]] Hswap0]]. subst σ0 σ.
      exists (storeA_swap (swap a b x) (swap a b y) σ1).
      split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * symmetry. apply storeA_swap_conjugate_inv.
    + intros [σ0 [[σ1 [Hσ1 Hswap1]] Hswap0]]. subst σ0 σ.
      exists (storeA_swap a b σ1). split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * apply storeA_swap_conjugate_inv.
Qed.

Context `{!ShiftKey K}.

Definition rawA_shift (k : nat) (m : WorldAT) : WorldAT :=
  rawA_rekey (key_shift k) m.

Definition resA_shift (k : nat) (w : WfWorldAT) : WfWorldAT :=
  resA_rekey (key_shift k) (key_shift_inj k) w.

End ResourceCoreA.

Section ResourceOpenA.

Context {V : Type} `{ValueSig V}.

Definition rawA_open (k : nat) (x : atom)
    (m : @WorldA logic_var _ _ V) : @WorldA logic_var _ _ V :=
  rawA_swap (LVBound k) (LVFree x) m.

Definition resA_open (k : nat) (x : atom)
    (w : @WfWorldA logic_var _ _ V) : @WfWorldA logic_var _ _ V :=
  resA_swap (LVBound k) (LVFree x) w.

End ResourceOpenA.



(** * Restriction and fibers for abstract resources *)

Section ResourceRestrictA.

Context {K : Type} `{Countable K} .
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (gmap K V) (only parsing).
Local Notation WorldAT := (@WorldA K _ _ V) (only parsing).
Local Notation WfWorldAT := (@WfWorldA K _ _ V) (only parsing).

Definition rawA_restrict (m : WorldAT) (X : gset K) : WorldAT := {|
  worldA_dom    := worldA_dom m ∩ X;
  worldA_stores := λ σ, ∃ σ0 : StoreAT,
    m σ0 ∧ storeA_restrict σ0 X = σ;
|}.

Definition resA_restrict (w : WfWorldAT) (X : gset K) : WfWorldAT.
Proof.
  refine (exist _ (rawA_restrict w X) _).
  destruct (worldA_wf w) as [Hne Hdom].
  split.
  - destruct Hne as [σ Hσ].
    exists (storeA_restrict σ X). exists σ. split; [exact Hσ | reflexivity].
  - intros σ [σ0 [Hσ0 Hrestrict]]. subst σ.
    rewrite storeA_restrict_dom.
    rewrite (Hdom σ0 Hσ0). reflexivity.
Defined.

Lemma wfworldA_store_restrict_dom (w : WfWorldAT) (σ : StoreAT) (X : gset K) :
  w σ → dom (storeA_restrict σ X) = worldA_dom (w : WorldAT) ∩ X.
Proof.
  intros Hσ. rewrite storeA_restrict_dom.
  rewrite (wfworldA_store_dom w σ Hσ). reflexivity.
Qed.

Lemma resA_restrict_lift_store
    (w : WfWorldAT) (X : gset K) (σ : StoreAT) :
  (resA_restrict w X : WorldAT) σ →
  ∃ σw, (w : WorldAT) σw ∧ storeA_restrict σw X = σ.
Proof.
  intros Hσ. exact Hσ.
Qed.

Lemma resA_restrict_project_store
    (w : WfWorldAT) (X : gset K) (σ : StoreAT) :
  (w : WorldAT) σ →
  (resA_restrict w X : WorldAT) (storeA_restrict σ X).
Proof.
  intros Hσ. exists σ. split; [exact Hσ | reflexivity].
Qed.

Lemma resA_restrict_eq_lift_store
    (w wX : WfWorldAT) (X : gset K) (σ : StoreAT) :
  resA_restrict w X = wX →
  (wX : WorldAT) σ →
  ∃ σw, (w : WorldAT) σw ∧ storeA_restrict σw X = σ.
Proof.
  intros <- Hσ. exact Hσ.
Qed.

Lemma resA_restrict_eq_project_store
    (w wX : WfWorldAT) (X : gset K) (σ : StoreAT) :
  resA_restrict w X = wX →
  (w : WorldAT) σ →
  (wX : WorldAT) (storeA_restrict σ X).
Proof.
  intros <- Hσ. apply resA_restrict_project_store. exact Hσ.
Qed.

Definition rawA_fiber (m : WorldAT) (σ : StoreAT) : WorldAT := {|
  worldA_dom    := worldA_dom m;
  worldA_stores := λ σ0, m σ0 ∧ storeA_restrict σ0 (dom σ) = σ;
|}.

Lemma rawA_fiber_commute (m : WorldAT) (σ1 σ2 : StoreAT) :
  rawA_fiber (rawA_fiber m σ1) σ2 =
  rawA_fiber (rawA_fiber m σ2) σ1.
Proof.
  apply worldA_ext; [reflexivity |].
  intros σ. simpl. tauto.
Qed.

Lemma rawA_fiber_empty (m : WorldAT) :
  rawA_fiber m (∅ : StoreAT) = m.
Proof.
  apply worldA_ext; [reflexivity |].
  intros σ. simpl. split.
  - tauto.
  - intros Hσ. split; [exact Hσ |].
    apply storeA_restrict_empty_set.
Qed.

Definition resA_fiber (w : WfWorldAT) (σ : StoreAT)
    (Hne : ∃ σ0, (w : WorldAT) σ0 ∧ storeA_restrict σ0 (dom σ) = σ)
    : WfWorldAT.
Proof.
  refine (exist _ (rawA_fiber w σ) _).
  destruct (worldA_wf w) as [_ Hdom].
  split.
  - destruct Hne as [σ0 [Hσ0 Hrestrict]].
    exists σ0. split; [exact Hσ0 | exact Hrestrict].
  - intros σ0 [Hσ0 _]. exact (Hdom σ0 Hσ0).
Defined.

Definition resA_fiber_from_projection
    (w : WfWorldAT) (X : gset K) (σ : StoreAT) (wfib : WfWorldAT) : Prop :=
  (resA_restrict w X : WorldAT) σ ∧
  (wfib : WorldAT) = rawA_fiber w σ.

Definition resA_fiber_member (w : WfWorldAT) (X : gset K) (wfib : WfWorldAT) : Prop :=
  ∃ σ, resA_fiber_from_projection w X σ wfib.

Lemma resA_fiber_commute (w : WfWorldAT) (σ1 σ2 : StoreAT)
    H1 H2 H1' H2' :
  resA_fiber (resA_fiber w σ1 H1) σ2 H2 =
  resA_fiber (resA_fiber w σ2 H1') σ1 H2'.
Proof.
  apply wfworldA_ext. apply rawA_fiber_commute.
Qed.

Lemma resA_fiber_from_projection_member
    (w wfib : WfWorldAT) (X : gset K) (σ σw : StoreAT) :
  resA_fiber_from_projection w X σ wfib →
  (w : WorldAT) σw →
  storeA_restrict σw X = σ →
  (wfib : WorldAT) σw.
Proof.
  intros [Hproj Heq] Hσw Hrestrict.
  rewrite Heq. simpl. split; [exact Hσw |].
  rewrite <- Hrestrict.
  rewrite <- (storeA_restrict_idemp
    (storeA_restrict σw X)
    (dom (storeA_restrict σw X))) at 2 by set_solver.
  rewrite storeA_restrict_restrict.
  replace (X ∩ dom (storeA_restrict σw X))
    with (dom (storeA_restrict σw X)).
  - reflexivity.
  - better_store_solver.
Qed.

Lemma resA_projection_from_fiber_projection
    (w wfib : WfWorldAT) (X Y : gset K) (σX σY : StoreAT) :
  resA_fiber_from_projection w X σX wfib →
  (resA_restrict wfib Y : WorldAT) σY →
  (resA_restrict w Y : WorldAT) σY.
Proof.
  intros [_ Heq] HprojY.
  destruct HprojY as [s [Hfib HrestrictY]].
  rewrite Heq in Hfib. destruct Hfib as [Hs _].
  exists s. split; [exact Hs | exact HrestrictY].
Qed.

Lemma resA_projection_into_other_fiber
    (w wfibX wfibY : WfWorldAT) (X Y : gset K) (σX σY : StoreAT) :
  resA_fiber_from_projection w X σX wfibX →
  resA_fiber_from_projection w Y σY wfibY →
  (resA_restrict wfibX Y : WorldAT) σY →
  (resA_restrict wfibY (dom σX) : WorldAT) σX.
Proof.
  intros [_ HeqX] [_ HeqY] HprojY.
  destruct HprojY as [s [HfibX HrestrictY]].
  rewrite HeqX in HfibX.
  destruct HfibX as [Hs HrestrictX].
  exists s. split.
  - rewrite HeqY. simpl. split; [exact Hs |].
    assert (Hrestrict_dom :
      storeA_restrict s (dom σY) =
      storeA_restrict s Y).
    {
      rewrite <- (storeA_restrict_idemp
        (storeA_restrict s Y) (dom σY)).
      - rewrite storeA_restrict_restrict.
        replace (Y ∩ dom σY) with (dom σY) by
          (rewrite <- HrestrictY; better_store_solver).
        reflexivity.
      - rewrite HrestrictY. set_solver.
    }
    rewrite Hrestrict_dom. exact HrestrictY.
  - exact HrestrictX.
Qed.

Lemma resA_restrict_rekey
    (f : K → K) (Hf : Inj (=) (=) f) (w : WfWorldAT) (X : gset K) :
  resA_restrict (resA_rekey f Hf w) (set_map f X) =
  resA_rekey f Hf (resA_restrict w X).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. apply set_eq. intros z. rewrite elem_of_intersection. split.
    + intros [HzD HzX].
      apply elem_of_map in HzD as [u [-> HuD]].
      apply elem_of_map in HzX as [v [Hv HuX]].
      apply Hf in Hv. subst v.
      apply elem_of_map. exists u. split; [reflexivity | set_solver].
    + intros [u [-> Hu]]%elem_of_map.
      apply elem_of_intersection in Hu as [HuD HuX].
      split; apply elem_of_map; eexists; split; eauto.
  - intros σ. simpl. split.
    + intros [σr [[σw [Hσw Hrekey]] Hrestrict]].
      exists (storeA_restrict σw X). split.
      * exists σw. split; [exact Hσw | reflexivity].
      * rewrite <- Hrestrict, <- Hrekey.
        symmetry. apply storeA_restrict_rekey. exact Hf.
    + intros [σx [[σw [Hσw Hrestrict]] Hrekey]].
      exists (storeA_map_key f σw). split.
      * exists σw. split; [exact Hσw | reflexivity].
      * rewrite <- Hrekey, <- Hrestrict.
        apply storeA_restrict_rekey. exact Hf.
Qed.

Lemma resA_restrict_swap (x y : K) (w : WfWorldAT) (X : gset K) :
  resA_restrict (resA_swap x y w) (set_swap x y X) =
  resA_swap x y (resA_restrict w X).
Proof.
  apply resA_restrict_rekey.
Qed.

Lemma resA_restrict_swap_projection x y (w : WfWorldAT) (X : gset K) (σ : StoreAT) :
  (resA_restrict w X : WorldAT) σ →
  (resA_restrict (resA_swap x y w) (set_swap x y X) : WorldAT)
    (storeA_swap x y σ).
Proof.
  intros Hproj.
  change ((resA_restrict (resA_swap x y w) (set_swap x y X) : WorldAT)
    (storeA_swap x y σ)).
  rewrite resA_restrict_swap. simpl.
  exists σ. split; [exact Hproj | reflexivity].
Qed.

Lemma resA_swap_extension_dom (x y : K) (m my : WfWorldAT) (z : K) :
  worldA_dom (my : WorldAT) = worldA_dom (m : WorldAT) ∪ {[z]} →
  worldA_dom (resA_swap x y my : WorldAT) =
  worldA_dom (resA_swap x y m : WorldAT) ∪ {[swap x y z]}.
Proof.
  intros Hdom. simpl.
	  change (set_swap x y (worldA_dom (my : WorldAT)) =
	    set_swap x y (worldA_dom (m : WorldAT)) ∪ {[swap x y z]}).
	  rewrite Hdom. better_base_solver.
Qed.

Lemma resA_swap_extension_dom_cancel
    (x y : K) (m my : WfWorldAT) (z : K) :
  worldA_dom (my : WorldAT) = worldA_dom (resA_swap x y m : WorldAT) ∪ {[z]} →
  worldA_dom (resA_swap x y my : WorldAT) =
  worldA_dom (m : WorldAT) ∪ {[swap x y z]}.
Proof.
  intros Hdom. simpl in Hdom |- *.
  change (worldA_dom (my : WorldAT) =
    set_swap x y (worldA_dom (m : WorldAT)) ∪ {[z]}) in Hdom.
	  change (set_swap x y (worldA_dom (my : WorldAT)) =
	    worldA_dom (m : WorldAT) ∪ {[swap x y z]}).
	  rewrite Hdom. better_base_solver.
Qed.

Lemma resA_swap_restrict_extension
    (x y : K) (m my : WfWorldAT) :
  resA_restrict my (worldA_dom (m : WorldAT)) = m →
  resA_restrict (resA_swap x y my) (worldA_dom (resA_swap x y m : WorldAT)) =
  resA_swap x y m.
Proof.
  intros Hrestr.
  change (resA_restrict (resA_swap x y my)
    (set_swap x y (worldA_dom (m : WorldAT))) = resA_swap x y m).
  rewrite resA_restrict_swap, Hrestr. reflexivity.
Qed.

Lemma resA_swap_restrict_extension_cancel
    (x y : K) (m my : WfWorldAT) :
  resA_restrict my (worldA_dom (resA_swap x y m : WorldAT)) = resA_swap x y m →
  resA_restrict (resA_swap x y my) (worldA_dom (m : WorldAT)) = m.
Proof.
  intros Hrestr.
  change (resA_restrict my (set_swap x y (worldA_dom (m : WorldAT))) =
    resA_swap x y m) in Hrestr.
  rewrite <- (set_swap_involutive x y (worldA_dom (m : WorldAT))).
  rewrite resA_restrict_swap, Hrestr, resA_swap_involutive. reflexivity.
Qed.

Lemma resA_restrict_restrict_eq (w : WfWorldAT) (X Y : gset K) :
  resA_restrict (resA_restrict w X) Y =
  resA_restrict w (X ∩ Y).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [σx [[σw [Hσw Hx]] Hy]]. subst σx σ.
      exists σw. split; [exact Hσw |].
      rewrite storeA_restrict_restrict. reflexivity.
    + intros [σw [Hσw Hxy]]. subst σ.
      exists (storeA_restrict σw X). split.
      * exists σw. split; [exact Hσw | reflexivity].
      * rewrite storeA_restrict_restrict. reflexivity.
Qed.

Lemma resA_restrict_self (w : WfWorldAT) :
  resA_restrict w (worldA_dom (w : WorldAT)) = w.
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [σw [Hσw Hrestrict]]. subst σ.
      rewrite storeA_restrict_idemp; [exact Hσw |].
      pose proof (wfworldA_store_dom w σw Hσw) as Hdom.
      change (dom (σw : gmap K V) = worldA_dom (w : WorldAT)) in Hdom.
      rewrite Hdom. set_solver.
    + intros Hσ.
      exists σ. split; [exact Hσ |].
      apply storeA_restrict_idemp.
      pose proof (wfworldA_store_dom w σ Hσ) as Hdom.
      change (dom (σ : gmap K V) = worldA_dom (w : WorldAT)) in Hdom.
      rewrite Hdom. set_solver.
Qed.

Lemma resA_fiber_swap (x y : K) (w : WfWorldAT) (σ : StoreAT)
    (Hne : ∃ σ0, (w : WorldAT) σ0 ∧
      storeA_restrict σ0 (dom σ) = σ)
    (Hne' : ∃ σ0, (resA_swap x y w : WorldAT) σ0 ∧
      storeA_restrict σ0 (dom (storeA_swap x y σ)) =
        storeA_swap x y σ) :
  resA_swap x y (resA_fiber w σ Hne) =
  resA_fiber (resA_swap x y w) (storeA_swap x y σ) Hne'.
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. reflexivity.
  - intros τ. simpl. split.
    + intros [τ0 [[Hτ0 Hrestr] Hswap]].
      rewrite <- Hswap.
      split.
      * exists τ0. split; [exact Hτ0 | reflexivity].
      * change (storeA_restrict
          (storeA_swap x y τ0)
          (dom (storeA_swap x y σ : gmap K V)) =
          storeA_swap x y σ).
        rewrite (storeA_swap_dom x y σ), storeA_restrict_swap. f_equal.
        exact Hrestr.
    + intros [[τ0 [Hτ0 Hswap]] Hrestr].
      rewrite <- Hswap in Hrestr |- *.
      exists τ0. split.
      * split; [exact Hτ0 |].
        change (storeA_restrict
          (storeA_swap x y τ0)
          (dom (storeA_swap x y σ : gmap K V)) =
          storeA_swap x y σ) in Hrestr.
        rewrite storeA_swap_dom, storeA_restrict_swap in Hrestr.
        apply (f_equal (storeA_swap x y)) in Hrestr.
        rewrite !storeA_swap_involutive in Hrestr. exact Hrestr.
      * reflexivity.
Qed.

Lemma resA_fiber_from_projection_swap x y (w wfib wfib' : WfWorldAT)
    (X : gset K) (σ : StoreAT) :
  resA_fiber_from_projection w X σ wfib →
  resA_fiber_from_projection (resA_swap x y w) (set_swap x y X)
    (storeA_swap x y σ) wfib' →
  resA_swap x y wfib = wfib'.
Proof.
  intros [Hproj Heq] [Hproj' Heq'].
  apply wfworldA_ext.
  change (rawA_swap x y (wfib : WorldAT) = (wfib' : WorldAT)).
  rewrite Heq, Heq'. apply worldA_ext.
  - simpl. reflexivity.
  - intros τ. simpl. split.
    + intros [τ0 [[Hτ0 Hrestr] Hswap]].
      rewrite <- Hswap.
      split.
      * exists τ0. split; [exact Hτ0 | reflexivity].
      * change (storeA_restrict
          (storeA_swap x y τ0)
          (dom (storeA_swap x y σ : gmap K V)) =
          storeA_swap x y σ).
        rewrite (storeA_swap_dom x y σ), storeA_restrict_swap. f_equal.
        exact Hrestr.
    + intros [[τ0 [Hτ0 Hswap]] Hrestr].
      rewrite <- Hswap in Hrestr |- *.
      exists τ0. split.
      * split; [exact Hτ0 |].
        change (storeA_restrict
          (storeA_swap x y τ0)
          (dom (storeA_swap x y σ : gmap K V)) =
          storeA_swap x y σ) in Hrestr.
        rewrite storeA_swap_dom, storeA_restrict_swap in Hrestr.
        apply (f_equal (storeA_swap x y)) in Hrestr.
        rewrite !storeA_swap_involutive in Hrestr. exact Hrestr.
      * reflexivity.
Qed.

Context `{!ShiftKey K}.

Lemma resA_restrict_shift (k : nat) (w : WfWorldAT) (X : gset K) :
  resA_restrict (resA_shift k w) (set_map (key_shift k) X) =
  resA_shift k (resA_restrict w X).
Proof.
  apply resA_restrict_rekey.
Qed.

End ResourceRestrictA.

Section ResourceOpenRestrictA.

Context {V : Type} `{ValueSig V}.

Lemma resA_restrict_open (k : nat) (x : atom)
    (w : @WfWorldA logic_var _ _ V) (X : gset logic_var) :
  resA_restrict (resA_open k x w) (set_swap (LVBound k) (LVFree x) X) =
  resA_open k x (resA_restrict w X).
Proof.
  apply resA_restrict_swap.
Qed.

End ResourceOpenRestrictA.
