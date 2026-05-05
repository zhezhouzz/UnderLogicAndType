(** * ChoiceType.InstantiationProps

    Multi-substitution instances for ChoiceType syntax, reusing the generic
    infrastructure from [CoreLang.InstantiationProps] where it applies.
    Choice types open binders with atoms, so the value-open classes from
    CoreLang are mirrored below with atom-open statements.  Contexts are kept
    out of the substitution class hierarchy for now. *)

From CoreLang Require Export InstantiationProps.
From CoreLang Require Import Instantiation.
From Stdlib Require Import Logic.FunctionalExtensionality.
From ChoiceType Require Export LocallyNamelessProps LocallyNamelessInstances.
From ChoiceType Require Import Qualifier Syntax.

(** ** Atom-open classes

    CoreLang's generic [MsubstOpen] family is phrased for syntactic categories
    whose binders open with [value].  Choice qualifiers and choice types open
    with an [atom] instead, so we keep a parallel family here. *)

Class SubstOpenAtom A `{Open atom A} `{SubstV value A} := subst_open_atom :
  forall (a : A) (k : nat) (y x : atom) (v : value),
    x <> y ->
    {x := v} ({k ~> y} a) = {k ~> y} ({x := v} a).

Class MsubstOpenAtom A `{Open atom A} `{SubstV value A} := msubst_open_atom :
  forall (a : A) (k : nat) (x : atom) (σ : env),
    x ∉ dom σ ->
    m{σ} ({k ~> x} a) = {k ~> x} (m{σ} a).

Lemma MsubstOpenAtom_all
    (A : Type)
    (openA : Open atom A)
    (substA : SubstV value A)
    (subst_open_atomA : @SubstOpenAtom A openA substA) :
  @MsubstOpenAtom A openA substA.
Proof.
  unfold MsubstOpenAtom. intros a k x σ Hfresh.
  unfold msubst.
  refine ((fin_maps.map_fold_ind
    (fun σ => x ∉ dom σ ->
      map_fold (fun y vy acc => {y := vy} acc) ({k ~> x} a) σ =
      {k ~> x} (map_fold (fun y vy acc => {y := vy} acc) a σ)) _ _ σ) Hfresh).
  - intros _. reflexivity.
  - intros y vy σ' Hyfresh Hfold IH Hx.
    rewrite !Hfold.
    rewrite IH by (rewrite dom_insert_L in Hx; set_solver).
    rewrite subst_open_atom by set_solver.
    reflexivity.
Qed.

Class MsubstOpenVarAtom A `{Open atom A} `{SubstV value A} := msubst_open_var_atom :
  forall (a : A) (k : nat) (x : atom) (σ : env),
    x ∉ dom σ ->
    m{σ} ({k ~> x} a) = {k ~> x} (m{σ} a).

Lemma MsubstOpenVarAtom_all
    (A : Type)
    (openA : Open atom A)
    (substA : SubstV value A)
    (msubst_open_atomA : @MsubstOpenAtom A openA substA) :
  @MsubstOpenVarAtom A openA substA.
Proof. unfold MsubstOpenVarAtom. intros. apply msubst_open_atom; done. Qed.

Class MsubstIntroAtom A `{Stale A} `{Open atom A} `{SubstV value A} :=
  msubst_intro_atom :
    forall (a : A) (k : nat) (vx : value) (x : atom) (σ : env),
      closed_env σ ->
      stale vx = ∅ ->
      x ∉ dom σ ∪ stale a ->
      {x := vx} ({k ~> x} (m{σ} a)) =
      m{<[x := vx]> σ} ({k ~> x} a).

(** ** Freshness under multi-substitution *)

#[global] Instance MsubstFresh_qualifier : MsubstFresh type_qualifier.
Proof. eapply MsubstFresh_all; typeclasses eauto. Qed.

#[global] Instance MsubstFresh_cty : MsubstFresh choice_ty.
Proof. eapply MsubstFresh_all; typeclasses eauto. Qed.

(** ** Free-variable upper bounds under closed environments *)

#[global] Instance MsubstFv_qualifier : MsubstFv type_qualifier.
Proof. eapply MsubstFv_all; typeclasses eauto. Qed.

#[global] Instance MsubstFv_cty : MsubstFv choice_ty.
Proof. eapply MsubstFv_all; typeclasses eauto. Qed.

(** ** Atom-open multi-substitution instances *)

#[global] Instance SubstOpenAtom_qualifier : SubstOpenAtom type_qualifier.
Proof.
  intros [B d p] k y x v Hxy.
  unfold open_one, subst_one, qual_open_atom, qual_subst_value; simpl.
  destruct (decide (k ∈ B)) as [Hk | Hk]; simpl.
  - destruct (decide (x ∈ {[y]} ∪ d)) as [Hxopen | Hxopen];
      destruct (decide (x ∈ d)) as [Hxd | Hxd]; try set_solver.
    + simpl. rewrite decide_True by done. f_equal.
      * set_solver.
      * repeat (apply functional_extensionality; intro).
        rewrite lookup_insert_ne by done. reflexivity.
    + simpl. rewrite decide_True by done. reflexivity.
  - destruct (decide (x ∈ d)); simpl; rewrite decide_False by done; reflexivity.
Qed.

#[global] Instance SubstOpenAtom_cty : SubstOpenAtom choice_ty.
Proof.
  intros τ k y x v Hxy. revert k.
  induction τ; intros k; unfold open_one, subst_one in *; simpl;
    try (f_equal; [apply IHτ1 | apply IHτ2]; done).
  - f_equal. exact (subst_open_atom φ (S k) y x v Hxy).
  - f_equal. exact (subst_open_atom φ (S k) y x v Hxy).
Qed.

#[global] Instance MsubstOpenAtom_qualifier : MsubstOpenAtom type_qualifier.
Proof. eapply MsubstOpenAtom_all; typeclasses eauto. Qed.

#[global] Instance MsubstOpenAtom_cty : MsubstOpenAtom choice_ty.
Proof. eapply MsubstOpenAtom_all; typeclasses eauto. Qed.

#[global] Instance MsubstOpenVarAtom_qualifier : MsubstOpenVarAtom type_qualifier.
Proof. eapply MsubstOpenVarAtom_all; typeclasses eauto. Qed.

#[global] Instance MsubstOpenVarAtom_cty : MsubstOpenVarAtom choice_ty.
Proof. eapply MsubstOpenVarAtom_all; typeclasses eauto. Qed.
