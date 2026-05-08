(** * CoreLang instantiation environments

    This file is the lightweight migration target for the [Instantiation.v]
    layer in UnderType/HATs.  It defines finite substitution environments and
    the generic multi-substitution operation.  Proof-oriented typeclasses and
    tactics live in [InstantiationProps.v] so that clients can import only the
    definitions when they do not need automation. *)

From CoreLang Require Export Syntax.

(** A value environment maps ordinary atoms to CoreLang values. *)
Definition env : Type := gmap atom value.

(** Closed environments contain only closed values.  This is the condition that
    makes finite-map fold order benign for multi-substitution. *)
Definition closed_env (σ : env) : Prop :=
  map_Forall (fun _ v => stale v = ∅) σ.

(** Multi-substitution, parameterized by any [SubstV value A] instance. *)
Definition msubst (σ : env) {A : Type} `{SubstV value A} (a : A) : A :=
  map_fold (fun x vx acc => {x := vx} acc) a σ.

Notation "'m{' σ '}' e" := (msubst σ e)
  (at level 20, format "m{ σ } e", σ constr).

Definition env_delete_step (x : atom) (_ : value) (Γ : gmap atom ty) : gmap atom ty :=
  delete x Γ.

(** Delete from a typing environment every variable instantiated by [σ].
    This is the context-side companion of [msubst]. *)
Definition env_delete (σ : env) (Γ : gmap atom ty) : gmap atom ty :=
  map_fold env_delete_step Γ σ.

Lemma msubst_empty {A : Type} `{SubstV value A} (a : A) :
  m{∅} a = a.
Proof.
  unfold msubst. reflexivity.
Qed.

Lemma env_delete_empty Γ :
  env_delete ∅ Γ = Γ.
Proof. unfold env_delete. reflexivity. Qed.
