(** * Generic shallow qualifiers *)

From ChoicePrelude Require Export Prelude Store.

Section Qualifier.

Context {V A : Type} `{ValueSig V}.

Local Notation BStoreT := (gmap nat V) (only parsing).
Local Notation StoreT := (gmap atom V) (only parsing).

Inductive qualifier : Type :=
  | qual (B : gset nat) (d : aset) (prop : BStoreT → StoreT → A → Prop).

Definition qual_bvars (q : qualifier) : gset nat :=
  match q with
  | qual B _ _ => B
  end.

Definition qual_dom (q : qualifier) : aset :=
  match q with
  | qual _ d _ => d
  end.

Definition qual_prop (q : qualifier) : BStoreT → StoreT → A → Prop :=
  match q with
  | qual _ _ p => p
  end.

Definition qual_open_value (k : nat) (v : V) (q : qualifier) : qualifier :=
  match q with
  | qual B d p =>
      if decide (k ∈ B) then
        qual (B ∖ {[k]}) d (λ β σ a, p (<[k := v]> β) σ a)
      else q
  end.

Definition qual_open_atom (k : nat) (x : atom) (q : qualifier) : qualifier :=
  match q with
  | qual B d p =>
      if decide (k ∈ B) then
        qual (B ∖ {[k]}) ({[x]} ∪ d)
          (λ β σ a, ∃ v, σ !! x = Some v ∧ p (<[k := v]> β) σ a)
      else q
  end.

Definition qual_subst_value (x : atom) (v : V) (q : qualifier) : qualifier :=
  match q with
  | qual B d p =>
      if decide (x ∈ d) then
        qual B (d ∖ {[x]}) (λ β σ a, p β (<[x := v]> σ) a)
      else q
  end.

Definition qual_subst_map (θ : StoreT) (q : qualifier) : qualifier :=
  match q with
  | qual B d p =>
      qual B (d ∖ dom θ) (λ β σ a, p β (θ ∪ σ) a)
  end.

Definition qual_and (q1 q2 : qualifier) : qualifier :=
  match q1, q2 with
  | qual B1 d1 p1, qual B2 d2 p2 =>
      qual (B1 ∪ B2) (d1 ∪ d2) (λ β σ a, p1 β σ a ∧ p2 β σ a)
  end.

Definition qual_or (q1 q2 : qualifier) : qualifier :=
  match q1, q2 with
  | qual B1 d1 p1, qual B2 d2 p2 =>
      qual (B1 ∪ B2) (d1 ∪ d2) (λ β σ a, p1 β σ a ∨ p2 β σ a)
  end.

Definition qual_top : qualifier :=
  qual ∅ ∅ (λ _ _ _, True).

Definition qual_bot : qualifier :=
  qual ∅ ∅ (λ _ _ _, False).

Definition qual_denote_with {A0 : Type}
    (restrict : aset → A0 → A)
    (q : qualifier)
    (β : BStoreT)
    (σ : StoreT)
    (a : A0) : Prop :=
  match q with
  | qual B d p =>
      p (map_restrict V β B) (store_restrict σ d) (restrict d a)
  end.

Definition lc_qualifier (q : qualifier) : Prop :=
  qual_bvars q = ∅.

#[global] Instance stale_qualifier : Stale qualifier := qual_dom.
Arguments stale_qualifier /.

End Qualifier.
