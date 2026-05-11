(** * ChoiceType.Qualifier

    Type qualifiers are shallow Rocq predicates over stores.  Unlike logic
    qualifiers, they may mention locally-nameless bound variables because
    dependent choice types bind their result coordinate. *)

From ChoiceType Require Export Prelude.

(** ** Syntax *)

Inductive type_qualifier : Type :=
  | qual
      (B : gset nat)
      (d : aset)
      (prop : gmap nat value → gmap atom value → gmap atom value → Prop).

Definition qual_bvars (q : type_qualifier) : gset nat :=
  match q with
  | qual B _ _ => B
  end.

Definition qual_dom (q : type_qualifier) : aset :=
  match q with
  | qual _ d _ => d
  end.

Definition qual_prop (q : type_qualifier) :
    gmap nat value → gmap atom value → gmap atom value → Prop :=
  match q with
  | qual _ _ p => p
  end.

Definition qual_open_atom (k : nat) (x : atom) (q : type_qualifier) : type_qualifier :=
  match q with
  | qual B d p =>
      if decide (k ∈ B) then
        qual (B ∖ {[k]}) ({[x]} ∪ d)
          (λ β σ a,
            ∃ v, σ !! x = Some v ∧
                 p (<[k := v]> β) (store_restrict σ d) (store_restrict a d))
      else q
  end.

Definition qual_swap_atom (x y : atom) (q : type_qualifier) : type_qualifier :=
  match q with
  | qual B d p =>
      qual B (aset_swap x y d)
        (λ β σ a, p β (store_swap x y σ) (store_swap x y a))
  end.

Definition qual_and (q1 q2 : type_qualifier) : type_qualifier :=
  match q1, q2 with
  | qual B1 d1 p1, qual B2 d2 p2 =>
      qual (B1 ∪ B2) (d1 ∪ d2)
        (λ β σ a,
          p1 (map_restrict value β B1) (store_restrict σ d1) (store_restrict a d1) ∧
          p2 (map_restrict value β B2) (store_restrict σ d2) (store_restrict a d2))
  end.

Definition qual_or (q1 q2 : type_qualifier) : type_qualifier :=
  match q1, q2 with
  | qual B1 d1 p1, qual B2 d2 p2 =>
      qual (B1 ∪ B2) (d1 ∪ d2)
        (λ β σ a,
          p1 (map_restrict value β B1) (store_restrict σ d1) (store_restrict a d1) ∨
          p2 (map_restrict value β B2) (store_restrict σ d2) (store_restrict a d2))
  end.

Definition qual_top : type_qualifier :=
  qual ∅ ∅ (λ _ _ _, True).

Definition qual_bot : type_qualifier :=
  qual ∅ ∅ (λ _ _ _, False).

Definition lc_qualifier (q : type_qualifier) : Prop :=
  qual_bvars q = ∅.

Definition body_qualifier (q : type_qualifier) : Prop :=
  ∃ L : aset, ∀ x : atom, x ∉ L → lc_qualifier (qual_open_atom 0 x q).

#[global] Instance stale_qualifier : Stale type_qualifier := qual_dom.
Arguments stale_qualifier /.

(** ** Locally-nameless infrastructure *)

#[global] Instance open_qual_atom_inst : Open atom type_qualifier := qual_open_atom.
Arguments open_qual_atom_inst /.

Notation "q '^q^' x" := (qual_open_atom 0 x q) (at level 20).
Notation "q '^qs^' '(' x ',' y ')'" := (qual_swap_atom x y q) (at level 20).

(** ** Local closure *)

#[global] Instance lc_qual_inst : Lc type_qualifier := lc_qualifier.
Arguments lc_qual_inst /.

(** ** Conjunction of two shallow qualifiers *)

Notation "q1 '&q' q2" := (qual_and q1 q2) (at level 40).

(** ** Denotation helpers *)

Definition qual_interp_full
    (β : gmap nat value) (σ ρ : gmap atom value) (q : type_qualifier) : Prop :=
  match q with
  | qual B d p => p (map_restrict value β B) (store_restrict σ d) (store_restrict ρ d)
  end.

Definition qual_interp (σ : gmap atom value) (q : type_qualifier) : Prop :=
  qual_interp_full ∅ σ σ q.

#[global] Instance denot_qual_inst : Denotation type_qualifier (gmap atom value → Prop) :=
  fun q σ => qual_interp σ q.
Arguments denot_qual_inst /.

(** ** Standard notations from UnderType *)

Fixpoint bv_value (v : value) : gset nat :=
  match v with
  | vconst _ => ∅
  | vfvar _ => ∅
  | vbvar k => {[k]}
  | vlam _ e => bv_tm e
  | vfix _ vf => bv_value vf
  end
with bv_tm (e : tm) : gset nat :=
  match e with
  | tret v => bv_value v
  | tlete e1 e2 => bv_tm e1 ∪ bv_tm e2
  | tprim _ v => bv_value v
  | tapp v1 v2 => bv_value v1 ∪ bv_value v2
  | tmatch v et ef => bv_value v ∪ bv_tm et ∪ bv_tm ef
  end.

Definition denote_value (β : gmap nat value) (σ : gmap atom value) (v : value) : option value :=
  match v with
  | vbvar k => β !! k
  | vfvar x => σ !! x
  | vconst c => Some (vconst c)
  | _ => Some v
  end.

Definition mk_q_eq (v1 v2 : value) : type_qualifier :=
  qual (bv_value v1 ∪ bv_value v2) (fv_value v1 ∪ fv_value v2)
    (fun β σ _ => denote_value β σ v1 = denote_value β σ v2).

Notation "'b0:v=' v" := (mk_q_eq (vbvar 0) v)
  (at level 5, format "b0:v= v").
Notation "'b0:x=' x" := (mk_q_eq (vbvar 0) (vfvar x))
  (at level 5, format "b0:x= x").
Notation "'b0:c=' c" := (mk_q_eq (vbvar 0) (vconst c))
  (at level 5, format "b0:c= c").

Notation "⊤q" := qual_top.
Notation "⊥q" := qual_bot.
