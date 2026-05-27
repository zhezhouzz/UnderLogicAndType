From ContextAlgebra Require Export Resource.
From ContextAlgebra Require Import ResourceRestrict.
From ContextPrelude Require Export Prelude Store.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.

(** * Logic qualifiers

    A logic qualifier is a predicate over a locally-nameless resource whose
    domain is exactly the qualifier domain.  At denotation time an atom-keyed
    world is lifted to the free-lvar view, restricted to the qualifier domain,
    and then passed to the predicate.

    Opening is just key swapping: the domain swaps [LVBound k] with [LVFree x],
    and the predicate swaps the incoming lworld back before interpreting it. *)

Section LogicQualifier.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LWorldOnT := (LWorldOn (V := V)) (only parsing).

Record logic_qualifier : Type := lqual {
  lqual_dom : lvset;
  lqual_prop : LWorldOnT lqual_dom → Prop;
}.

Definition lqual_lvars (q : logic_qualifier) : lvset :=
  lqual_dom q.

Definition lqual_fv (q : logic_qualifier) : aset :=
  lvars_fv (lqual_dom q).

Definition logic_qualifier_denote
    (q : logic_qualifier) (m : WfWorldT) : Prop :=
  match q with
  | lqual D P =>
      ∃ (Hlc : lc_lvars D)
        (Hsub : lvars_fv D ⊆ world_dom (m : WorldT)),
        P (lworld_on_lift D m Hlc Hsub)
  end.

Definition lqual_fvars
    (d : aset) (prop : LWorldOnT (lvars_of_atoms d) → Prop)
    : logic_qualifier :=
  lqual (lvars_of_atoms d) prop.

Definition lqual_open
    (k : nat) (x : atom) (q : logic_qualifier) : logic_qualifier :=
  match q with
  | lqual D P =>
	      lqual (lvars_open k x D)
	        (λ w, P (lworld_on_open_back k x D w))
	  end.

Lemma logic_qualifier_ext (q1 q2 : logic_qualifier) :
  lqual_dom q1 = lqual_dom q2 ->
  (forall (w1 : LWorldOnT (lqual_dom q1))
          (w2 : LWorldOnT (lqual_dom q2)),
      @lw V (lqual_dom q1) w1 = @lw V (lqual_dom q2) w2 ->
      lqual_prop q1 w1 <-> lqual_prop q2 w2) ->
  q1 = q2.
Proof.
  destruct q1 as [D1 P1], q2 as [D2 P2]. simpl.
  intros HD HP. subst D2.
  f_equal.
  apply functional_extensionality. intros w.
  apply propositional_extensionality.
  apply HP. reflexivity.
Qed.

Lemma lqual_open_commute_fresh i j x y q :
  i <> j ->
  x <> y ->
  lqual_open i x (lqual_open j y q) =
  lqual_open j y (lqual_open i x q).
Proof.
  intros Hij Hxy.
  destruct q as [D P].
  cbn [lqual_open].
  apply logic_qualifier_ext.
  - apply lvars_open_commute_fresh; assumption.
  - intros w1 w2 Hlw. cbn [lqual_prop].
    enough
      (lworld_on_open_back j y D
        (lworld_on_open_back i x (lvars_open j y D) w1) =
       lworld_on_open_back i x D
        (lworld_on_open_back j y (lvars_open i x D) w2)) as ->.
    { reflexivity. }
    apply lworld_on_ext.
    eapply lworld_on_open_back_commute_fresh; eauto.
Qed.

Lemma logic_qualifier_denote_restrict q w X :
  lqual_fv q ⊆ X →
  logic_qualifier_denote q (res_restrict w X) ↔
  logic_qualifier_denote q w.
Proof.
  destruct q as [D P]. simpl. intros HfvX. split.
  - intros [Hlc [Hsub HP]].
    exists Hlc.
    assert (Hsubw : lvars_fv D ⊆ world_dom (w : WorldT)).
    {
      intros x Hx.
      pose proof (Hsub x Hx) as Hx_restrict.
      simpl in Hx_restrict.
      apply elem_of_intersection in Hx_restrict as [Hxw _].
      exact Hxw.
    }
    exists Hsubw.
    enough (lworld_on_lift D (res_restrict w X) Hlc Hsub =
            lworld_on_lift D w Hlc Hsubw) as Heq.
    { rewrite <- Heq. exact HP. }
    apply lworld_on_ext. unfold lworld_on_lift. simpl.
    rewrite res_restrict_restrict_eq.
    replace (X ∩ lvars_fv D) with (lvars_fv D) by set_solver.
    reflexivity.
  - intros [Hlc [Hsub HP]].
    exists Hlc.
    assert (Hsubr : lvars_fv D ⊆ world_dom (res_restrict w X : WorldT)).
    {
      simpl. set_solver.
    }
    exists Hsubr.
    enough (lworld_on_lift D w Hlc Hsub =
            lworld_on_lift D (res_restrict w X) Hlc Hsubr) as Heq.
    { rewrite <- Heq. exact HP. }
    apply lworld_on_ext. unfold lworld_on_lift. simpl.
    rewrite res_restrict_restrict_eq.
    replace (X ∩ lvars_fv D) with (lvars_fv D) by set_solver.
    reflexivity.
Qed.

Lemma logic_qualifier_denote_mono
    (q : logic_qualifier) (m0 m : WfWorldT) :
  logic_qualifier_denote q m0 →
  lqual_fv q ⊆ world_dom (m0 : WorldT) →
  m0 ⊑ m →
  logic_qualifier_denote q m.
Proof.
  destruct q as [D P]. simpl. intros [Hlc [Hsub0 HP]] _ Hle.
  exists Hlc.
  assert (Hsub : lvars_fv D ⊆ world_dom (m : WorldT)).
  {
    pose proof (raw_le_dom _ _ Hle) as Hdom.
    set_solver.
  }
  exists Hsub.
  enough (lworld_on_lift D m0 Hlc Hsub0 =
          lworld_on_lift D m Hlc Hsub) as Heq.
  { rewrite <- Heq. exact HP. }
  apply lworld_on_ext. unfold lworld_on_lift. simpl.
  rewrite (res_restrict_le_eq m0 m (lvars_fv D) Hle Hsub0).
  reflexivity.
Qed.

#[global] Instance stale_logic_qualifier : Stale logic_qualifier := lqual_fv.
Arguments stale_logic_qualifier /.

End LogicQualifier.
