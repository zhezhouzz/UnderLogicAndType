(** * CoreLang.BasicTyping

    Standard simple (basic) type system for the core language.
    This is the "erased" type system [⊢_basic] referenced by the
    choice-type erasure and lifting functions.

    Contexts are [gmap atom ty]; typing uses the [Typing] typeclass so
    that the notation [Γ ⊢ e ⋮ T] works for both values and terms. *)

From CoreLang Require Export Syntax.

(** ** Primitive-operation type signatures

    Each [prim_op] has exactly one argument. *)

Definition prim_op_type (op : prim_op) : base_ty * base_ty :=
  match op with
  | op_eq0 => (TNat, TBool)
  end.

Lemma prim_op_type_wf :
  prim_op_type op_eq0 = (TNat, TBool).
Proof. reflexivity. Qed.

(** ** Typing judgments *)

(** We define two mutually-inductive relations and expose them via
    the [Typing] typeclass with context type [gmap atom ty]. *)

Reserved Notation "Γ '⊢ᵥ' v '⋮' T" (at level 20, v constr, T constr).
Reserved Notation "Γ '⊢ₑ' e '⋮' T" (at level 20, e constr, T constr).

Inductive value_has_type : gmap atom ty → value → ty → Prop :=
  | VT_Const Γ c :
      Γ ⊢ᵥ (vconst c) ⋮ TBase (base_ty_of_const c)
  | VT_FVar Γ x T :
      Γ !! x = Some T →
      Γ ⊢ᵥ (vfvar x) ⋮ T
  | VT_Lam Γ s T e (L : aset) :
      (∀ x, x ∉ L → <[x := s]>Γ ⊢ₑ (e ^^ x) ⋮ T) →
      Γ ⊢ᵥ (vlam s e) ⋮ (s →ₜ T)
  | VT_Fix Γ sx T vf (L : aset) :
      (** The body receives the ordinary argument first; the resulting value
          is a function waiting for the recursive self reference. *)
      (∀ x, x ∉ L →
        <[x := sx]>Γ ⊢ᵥ (vf ^^ x) ⋮ ((sx →ₜ T) →ₜ T)) →
      Γ ⊢ᵥ (vfix (sx →ₜ T) vf) ⋮ (sx →ₜ T)

with tm_has_type : gmap atom ty → tm → ty → Prop :=
  | TT_Ret Γ v T :
      Γ ⊢ᵥ v ⋮ T →
      Γ ⊢ₑ (tret v) ⋮ T
  | TT_Let Γ T1 T2 e1 e2 (L : aset) :
      Γ ⊢ₑ e1 ⋮ T1 →
      (∀ x, x ∉ L → <[x := T1]>Γ ⊢ₑ (e2 ^^ x) ⋮ T2) →
      Γ ⊢ₑ (tlete e1 e2) ⋮ T2
  | TT_Op Γ op v arg_b ret_b :
      prim_op_type op = (arg_b, ret_b) →
      Γ ⊢ᵥ v ⋮ TBase arg_b →
      Γ ⊢ₑ (tprim op v) ⋮ TBase ret_b
  | TT_App Γ s1 s2 v1 v2 :
      Γ ⊢ᵥ v1 ⋮ (s1 →ₜ s2) →
      Γ ⊢ᵥ v2 ⋮ s1 →
      Γ ⊢ₑ (tapp v1 v2) ⋮ s2
  | TT_Match Γ v T et ef :
      Γ ⊢ᵥ v ⋮ TBase TBool →
      Γ ⊢ₑ et ⋮ T →
      Γ ⊢ₑ ef ⋮ T →
      Γ ⊢ₑ (tmatch v et ef) ⋮ T

where "Γ '⊢ᵥ' v '⋮' T" := (value_has_type Γ v T)
  and "Γ '⊢ₑ' e '⋮' T" := (tm_has_type Γ e T).

Scheme value_has_type_mut := Induction for value_has_type Sort Prop
  with tm_has_type_mut    := Induction for tm_has_type    Sort Prop.

#[global] Hint Constructors value_has_type tm_has_type : core.

(** Typeclass instances for uniform [⊢] notation. *)
#[global] Instance typing_value_inst : Typing (gmap atom ty) value ty :=
  value_has_type.
#[global] Instance typing_tm_inst : Typing (gmap atom ty) tm ty :=
  tm_has_type.
Arguments typing_value_inst /.
Arguments typing_tm_inst /.

(** ** Standard weakening and substitution lemmas (Admitted) *)

Lemma weakening_value Γ Γ' v T :
  Γ ⊢ᵥ v ⋮ T → Γ ⊆ Γ' → Γ' ⊢ᵥ v ⋮ T.
Proof. Admitted.

Lemma weakening_tm Γ Γ' e T :
  Γ ⊢ₑ e ⋮ T → Γ ⊆ Γ' → Γ' ⊢ₑ e ⋮ T.
Proof. Admitted.

Lemma subst_typing_value Γ x s v T vx :
  Γ ⊢ᵥ v ⋮ T → ∅ ⊢ᵥ vx ⋮ s → Γ !! x = Some s →
  delete x Γ ⊢ᵥ ({x := vx} v) ⋮ T.
Proof. Admitted.

Lemma subst_typing_tm Γ x s e T vx :
  Γ ⊢ₑ e ⋮ T → ∅ ⊢ᵥ vx ⋮ s → Γ !! x = Some s →
  delete x Γ ⊢ₑ ({x := vx} e) ⋮ T.
Proof. Admitted.

Lemma typing_value_lc Γ v T : Γ ⊢ᵥ v ⋮ T → lc_value v.
Proof. Admitted.

Lemma typing_tm_lc Γ e T : Γ ⊢ₑ e ⋮ T → lc_tm e.
Proof. Admitted.
