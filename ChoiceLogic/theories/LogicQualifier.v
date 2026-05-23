From ChoiceAlgebra Require Export Resource.
From ChoiceAlgebra Require Import ResourceRestrict.
From ChoicePrelude Require Export Prelude Store.

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
