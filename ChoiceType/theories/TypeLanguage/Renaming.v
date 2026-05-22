(** * ChoiceType.TypeLanguage.Renaming

    Renaming transport for type qualifiers.

    Opening remains the primitive operation in [Qualifier.v], because it is the
    same involutive swap used by logic qualifiers.  Type denotation also needs
    binder-depth shifts; those are represented here as a renaming transport:
    the domain is renamed, and the new predicate holds exactly when the input
    store is the renamed image of an old input store satisfying the old
    predicate. *)

From ChoiceType.TypeLanguage Require Export Qualifier.

Local Notation LStoreT := (LStore (V := value)) (only parsing).

Class Shift A := shift_from : nat -> A -> A.
Notation "'↑[' k ']'" := (shift_from k)
  (at level 10, k constr, format "↑[ k ]").

Definition logic_var_shift_from (k : nat) (v : logic_var) : logic_var :=
  match v with
  | LVFree x => LVFree x
  | LVBound n => if decide (k <= n) then LVBound (S n) else LVBound n
  end.

Lemma logic_var_shift_from_lt k n :
  n < k ->
  logic_var_shift_from k (LVBound n) = LVBound n.
Proof.
Admitted.

Lemma logic_var_shift_from_ge k n :
  k <= n ->
  logic_var_shift_from k (LVBound n) = LVBound (S n).
Proof.
Admitted.

Lemma logic_var_open_shift_from_under j k x v :
  j <= k ->
  logic_var_open (S (S k)) x (logic_var_shift_from (S j) v) =
  logic_var_shift_from (S j) (logic_var_open (S k) x v).
Proof.
Admitted.

Lemma logic_var_shift_from_inj k :
  Inj (=) (=) (logic_var_shift_from k).
Proof.
Admitted.

Definition open_env_shift_key_from (k n : nat) : nat :=
  if decide (n < k) then n else S n.

Definition open_env_shift_from (k : nat) (η : gmap nat atom) : gmap nat atom :=
  kmap (open_env_shift_key_from k) η.

Lemma open_env_shift_key_from_zero n :
  open_env_shift_key_from 0 n = S n.
Proof.
Admitted.

Lemma open_env_shift_from_zero η :
  open_env_shift_from 0 η = open_env_lift η.
Proof.
Admitted.

Lemma open_env_shift_from_lookup k η n :
  open_env_shift_from k η !! open_env_shift_key_from k n = η !! n.
Proof.
Admitted.

Lemma logic_var_open_env_shift_from k η v :
  logic_var_open_env (open_env_shift_from k η) (logic_var_shift_from k v) =
  logic_var_shift_from k (logic_var_open_env η v).
Proof.
Admitted.

Definition lvars_shift_from (k : nat) (D : lvset) : lvset :=
  set_map (logic_var_shift_from k) D.

#[global] Instance shift_logic_var_inst : Shift logic_var :=
  logic_var_shift_from.

#[global] Instance shift_lvars_inst : Shift lvset :=
  lvars_shift_from.

Definition lstore_rename
    (f : logic_var -> logic_var) (s : LStoreT) : LStoreT :=
  kmap f s.

Lemma lstore_rename_dom
    (f : logic_var -> logic_var) (Hf : Inj (=) (=) f) (s : LStoreT) :
  dom (lstore_rename f s : LStoreT) = set_map f (dom (s : LStoreT)).
Proof.
Admitted.

Definition lstore_on_rename
    (f : logic_var -> logic_var) (Hf : Inj (=) (=) f)
    {D : lvset} (s : LStoreOn D)
    : LStoreOn (set_map f D).
Proof.
  refine {| lso_store := lstore_rename f (lso_store s) |}.
  rewrite lstore_rename_dom by exact Hf.
  rewrite (lso_dom s). reflexivity.
Defined.

Lemma lstore_rename_id_on_dom
    (f : logic_var -> logic_var) (Hf : Inj (=) (=) f)
    (D : lvset) (s : LStoreOn D) :
  (forall v, v ∈ D -> f v = v) ->
  lso_store (lstore_on_rename f Hf s) = lso_store s.
Proof.
Admitted.

Definition lstore_shift_from (k : nat) (s : LStoreT) : LStoreT :=
  lstore_rename (logic_var_shift_from k) s.

Definition lstore_on_shift_from
    (k : nat) {D : lvset} (s : LStoreOn D)
    : LStoreOn (lvars_shift_from k D) :=
  lstore_on_rename (logic_var_shift_from k) (logic_var_shift_from_inj k) s.

Lemma lstore_shift_from_below_id k D (s : LStoreOn D) :
  (forall n, n ∈ lvars_bv D -> n < k) ->
  lso_store (lstore_on_shift_from k s) = lso_store s.
Proof.
Admitted.

Definition qual_rename
    (f : logic_var -> logic_var) (Hf : Inj (=) (=) f)
    (q : type_qualifier) : type_qualifier :=
  match q with
  | tqual D P =>
      tqual (set_map f D)
        (fun s' =>
           exists s : LStoreOn D,
             lstore_on_rename f Hf s = s' /\ P s)
  end.

Definition qual_shift_from (k : nat) (q : type_qualifier) : type_qualifier :=
  qual_rename (logic_var_shift_from k) (logic_var_shift_from_inj k) q.

#[global] Instance shift_qual_inst : Shift type_qualifier :=
  qual_shift_from.

Lemma lvars_shift_from_fv k D :
  lvars_fv (lvars_shift_from k D) = lvars_fv D.
Proof.
Admitted.

Lemma lvars_shift_from_bv k D :
  lvars_bv (lvars_shift_from k D) =
    set_map (fun n => if decide (k <= n) then S n else n) (lvars_bv D).
Proof.
Admitted.

Lemma lvars_shift_from_mono k D E :
  D ⊆ E ->
  lvars_shift_from k D ⊆ lvars_shift_from k E.
Proof.
Admitted.

Lemma lvars_shift_from_below_id k D :
  (forall n, n ∈ lvars_bv D -> n < k) ->
  lvars_shift_from k D = D.
Proof.
Admitted.

Lemma lvars_open_env_shift_from k η D :
  lvars_open_env (open_env_shift_from k η) (lvars_shift_from k D) =
  lvars_shift_from k (lvars_open_env η D).
Proof.
Admitted.

Lemma open_env_shift_from_fresh_for_lvars k η D :
  open_env_fresh_for_lvars η D ->
  open_env_fresh_for_lvars (open_env_shift_from k η) (lvars_shift_from k D).
Proof.
Admitted.

Lemma lvars_open_shift_from_under j k x D :
  j <= k ->
  lvars_open (S (S k)) x (lvars_shift_from (S j) D) =
  lvars_shift_from (S j) (lvars_open (S k) x D).
Proof.
Admitted.

Lemma lvars_bv_shift_from_under_iff j k D :
  j <= k ->
  S (S k) ∈ lvars_bv (lvars_shift_from (S j) D) <->
  S k ∈ lvars_bv D.
Proof.
Admitted.

Lemma qual_shift_from_vars k q :
  qual_vars (qual_shift_from k q) = lvars_shift_from k (qual_vars q).
Proof.
  destruct q. reflexivity.
Qed.

Lemma qual_shift_from_dom k q :
  qual_dom (qual_shift_from k q) = qual_dom q.
Proof.
Admitted.

Lemma qual_shift_from_lc k q :
  lc_qualifier q ->
  lc_qualifier (qual_shift_from k q).
Proof.
Admitted.

Lemma qual_shift_from_below_id k q :
  (forall n, n ∈ qual_bvars q -> n < k) ->
  qual_shift_from k q = q.
Proof.
Admitted.

Lemma qual_open_shift_from_under j k x q :
  j <= k ->
  qual_open_atom (S (S k)) x (qual_shift_from (S j) q) =
  qual_shift_from (S j) (qual_open_atom (S k) x q).
Proof.
Admitted.

Lemma qual_shift_open_commute k x q :
  qual_open_atom (S (S k)) x (qual_shift_from (S k) q) =
  qual_shift_from (S k) (qual_open_atom (S k) x q).
Proof.
Admitted.
