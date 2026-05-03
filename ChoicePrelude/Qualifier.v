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

Definition lc_qualifier (q : qualifier) : Prop :=
  qual_bvars q = ∅.

#[global] Instance stale_qualifier : Stale qualifier := qual_dom.
Arguments stale_qualifier /.

End Qualifier.
