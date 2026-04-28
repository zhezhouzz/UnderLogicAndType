(** * ChoiceType.Typing

    Declarative typing rules for the choice type system.

    The current paper presentation has a single judgment [Γ ⊢ e ⋮ τ].
    Star, sum, intersection, and union remain type/context syntax with
    denotational meaning; their direct proof rules are derived/optional and
    are deliberately not part of this core definition. *)

From ChoiceType Require Export Denotation.

(** ** Semantic subtyping and context equivalence *)

Definition sub_type (Γ : ctx) (τ1 τ2 : choice_ty) : Prop :=
  ∀ e, ⟦Γ⟧ ⊫ FImpl (⟦τ1⟧ e) (⟦τ2⟧ e).

Definition ctx_sub (Γ1 Γ2 : ctx) : Prop :=
  (⟦Γ1⟧ ⊫ ⟦Γ2⟧) ∧ (⟦Γ2⟧ ⊫ ⟦Γ1⟧).

(** ** The typing judgment *)

Inductive has_choice_type : ctx → tm → choice_ty → Prop :=

  (** T-Var *)
  | CT_Var x τ :
      has_choice_type
        (CtxBind x τ)
        (tret (vfvar x))
        τ

  (** T-Const *)
  | CT_Const c :
      has_choice_type
        CtxEmpty
        (tret (vconst c))
        (CTOver (base_ty_of_const c) (b0:c= c))

  (** T-Sub *)
  | CT_Sub Γ e τ1 τ2 :
      has_choice_type Γ e τ1 →
      sub_type Γ τ1 τ2 →
      has_choice_type Γ e τ2

  (** T-CtxEq *)
  | CT_CtxEq Γ1 Γ2 e τ :
      has_choice_type Γ1 e τ →
      ctx_sub Γ1 Γ2 →
      has_choice_type Γ2 e τ

  (** T-Let *)
  | CT_Let Γ τ1 τ2 e1 e2 (L : aset) :
      has_choice_type Γ e1 τ1 →
      (∀ x, x ∉ L →
        has_choice_type
          (CtxComma Γ (CtxBind x τ1))
          (e2 ^^ x)
          τ2) →
      has_choice_type Γ (tlete e1 e2) τ2

  (** T-Lam *)
  | CT_Lam Γ x τx τ e (L : aset) :
      (∀ y, y ∉ L →
        has_choice_type
          (CtxComma Γ (CtxBind y τx))
          (e ^^ y)
          ({x := vfvar y} τ)) →
      has_choice_type Γ
        (tret (vlam (erase_ty τx) e))
        (CTArrow x τx τ)

  (** T-AppFun, specialized to ANF function application. *)
  | CT_AppFun Γ x τx τ f y :
      has_choice_type Γ (tret (vfvar f)) (CTArrow x τx τ) →
      has_choice_type Γ (tret (vfvar y)) τx →
      has_choice_type Γ
        (tletapp (vfvar f) (vfvar y) (tret (vbvar 0)))
        ({x := vfvar y} τ)

  (** T-Fix *)
  | CT_Fix Γ x τx τ e (L : aset) :
      (∀ f y, f ∉ L → y ∉ L → f ≠ y →
        has_choice_type
          (CtxComma Γ
            (CtxComma
              (CtxBind y τx)
              (CtxBind f (CTArrow x τx τ))))
          ({0 ~> vfvar y} ({1 ~> vfvar f} e))
          ({x := vfvar y} τ)) →
      has_choice_type Γ
        (tret (vfix (erase_ty (CTArrow x τx τ)) (erase_ty τx) e))
        (CTArrow x τx τ)

  (** T-AppOp.  The current core language records primitive op types at the
      basic layer, so this rule uses lifted basic argument/result types. *)
  | CT_LetOp Γ op vs e_body τ arg_tys ret_b (L : aset) :
      prim_op_type op = (arg_tys, ret_b) →
      Forall2
        (fun v b => has_choice_type Γ (tret v) (lift_ty (TBase b)))
        vs arg_tys →
      (∀ x, x ∉ L →
        has_choice_type
          (CtxComma Γ (CtxBind x (lift_ty (TBase ret_b))))
          (e_body ^^ x)
          τ) →
      has_choice_type Γ (tletop op vs e_body) τ

  (** T-Match.  This is still a compact core-language skeleton; the paper's
      big-oplus presentation can be recovered by choosing a sum context/type
      for the branch family. *)
  | CT_Match Γ v τ branches b (L : aset) :
      has_choice_type Γ (tret v) (lift_ty (TBase b)) →
      (∀ i n body arg_tys,
          branches !! i = Some (n, body) →
          constructor_tys b !! i = Some arg_tys →
          length arg_tys = n →
          ∀ ys : list atom,
            length ys = n →
            NoDup ys →
            Forall (fun y => y ∉ L) ys →
            has_choice_type
              (fold_left
                (fun ctx '(y, bt) => CtxComma ctx (CtxBind y (lift_ty (TBase bt))))
                (zip ys arg_tys) Γ)
              (fold_left (fun e y => e ^^ y) ys body)
              τ) →
      has_choice_type Γ (tmatch v branches) τ.

#[global] Hint Constructors has_choice_type : core.
#[global] Instance typing_choice_inst : Typing ctx tm choice_ty := has_choice_type.
Arguments typing_choice_inst /.

(** ** Small admissible helpers kept only where they name core definitions. *)

Lemma sub_type_refl Γ τ :
  sub_type Γ τ τ.
Proof. unfold sub_type, entails. intros e m _ m' _ Hτ. exact Hτ. Qed.

Lemma ctx_sub_refl Γ :
  ctx_sub Γ Γ.
Proof. unfold ctx_sub, entails. auto. Qed.

(** Substitution preserves choice typing. *)
Lemma subst_typing_choice Γ x τx e τ v :
  has_choice_type (CtxComma (CtxBind x τx) Γ) e τ →
  has_choice_type CtxEmpty (tret v) τx →
  has_choice_type Γ ({x := v} e) ({x := v} τ).
Proof. Admitted.

(** Typing implies basic typing (erasure correctness). *)
Lemma typing_erase Γ e τ :
  has_choice_type Γ e (erase_ty τ) →
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.
Proof. Admitted.
