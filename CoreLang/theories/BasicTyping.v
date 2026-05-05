(** * CoreLang.BasicTyping

    Standard simple (basic) type system for the core language.
    This is the "erased" type system [⊢_basic] referenced by the
    choice-type erasure and lifting functions.

    Contexts are [gmap atom ty]; typing uses the [Typing] typeclass so
    that the notation [Γ ⊢ e ⋮ T] works for both values and terms. *)

From CoreLang Require Export Syntax.
From CoreLang Require Import LocallyNamelessExtra.

(** ** Primitive-operation type signatures

    Each [prim_op] has exactly one argument. *)

Definition prim_op_type (op : prim_op) : base_ty * base_ty :=
  match op with
  | op_eq0 => (TNat, TBool)
  | op_bool_gen => (TBool, TBool)
  | op_nat_gen => (TBool, TNat)
  | op_plus1 => (TNat, TNat)
  | op_minus1 => (TNat, TNat)
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
Proof.
  intros Hty. revert Γ'.
  induction Hty using value_has_type_mut with
      (P0 := fun Γ e T _ => ∀ Γ', Γ ⊆ Γ' → Γ' ⊢ₑ e ⋮ T);
      intros Γ' Hsub; eauto using lookup_weaken.
  - econstructor. intros x Hx.
    eapply H; [exact Hx | by apply insert_mono].
  - econstructor. intros x Hx.
    eapply H; [exact Hx | by apply insert_mono].
  - econstructor; eauto. intros x Hx.
    match goal with
    | IH : ∀ y : atom, y ∉ _ → ∀ Γ', _ |- _ =>
        eapply IH; [exact Hx | by apply insert_mono]
    end.
Qed.

Lemma weakening_tm Γ Γ' e T :
  Γ ⊢ₑ e ⋮ T → Γ ⊆ Γ' → Γ' ⊢ₑ e ⋮ T.
Proof.
  intros Hty. revert Γ'.
  induction Hty using tm_has_type_mut with
      (P := fun Γ v T _ => ∀ Γ', Γ ⊆ Γ' → Γ' ⊢ᵥ v ⋮ T);
      intros Γ' Hsub; eauto using lookup_weaken.
  - econstructor. intros x Hx.
    eapply H; [exact Hx | by apply insert_mono].
  - econstructor. intros x Hx.
    eapply H; [exact Hx | by apply insert_mono].
  - econstructor; eauto. intros x Hx.
    match goal with
    | IH : ∀ y : atom, y ∉ _ → ∀ Γ', _ |- _ =>
        eapply IH; [exact Hx | by apply insert_mono]
    end.
Qed.

Lemma typing_value_lc Γ v T : Γ ⊢ᵥ v ⋮ T → lc_value v.
Proof.
  intros Hty.
  induction Hty using value_has_type_mut with
      (P0 := fun Γ e T _ => lc_tm e);
      eauto.
Qed.

Lemma typing_tm_lc Γ e T : Γ ⊢ₑ e ⋮ T → lc_tm e.
Proof.
  intros Hty.
  induction Hty using tm_has_type_mut with
      (P := fun Γ v T _ => lc_value v);
      eauto.
Qed.

Lemma subst_typing_insert_value Γ x s v T vx :
  <[x := s]> Γ ⊢ᵥ v ⋮ T →
  Γ ⊢ᵥ vx ⋮ s →
  Γ ⊢ᵥ ({x := vx} v) ⋮ T.
Proof.
  intros Hty Hv.
  rename x into xsub.
  remember (<[xsub := s]> Γ) as Γx.
  revert Γ HeqΓx Hv.
  induction Hty using value_has_type_mut with
      (P := fun Γx v T _ =>
        ∀ Γ, Γx = <[xsub := s]> Γ → Γ ⊢ᵥ vx ⋮ s →
          Γ ⊢ᵥ ({xsub := vx} v) ⋮ T)
      (P0 := fun Γx e T _ =>
        ∀ Γ, Γx = <[xsub := s]> Γ → Γ ⊢ᵥ vx ⋮ s →
          Γ ⊢ₑ ({xsub := vx} e) ⋮ T);
      intros Γ0 Heq Hv; subst; simpl.
  - constructor.
  - apply lookup_insert_Some in e as [[-> ->]|[Hne Hlook]].
    + cbn. rewrite decide_True by reflexivity.
      exact Hv.
    + cbn. rewrite decide_False by exact Hne.
      econstructor. exact Hlook.
  - apply VT_Lam with (L := L ∪ {[xsub]} ∪ dom Γ0).
    let b := fresh "opened" in
    intros b Hb;
    change (<[b := s0]> Γ0 ⊢ₑ
      open_tm 0 (vfvar b) (tm_subst xsub vx e) ⋮ T);
    assert (Hxy : xsub <> b) by (intro; subst; apply Hb; set_solver);
    assert (Hlc_vx : lc_value vx) by exact (typing_value_lc _ _ _ Hv);
    assert (Hv' : <[b := s0]> Γ0 ⊢ᵥ vx ⋮ s) by
      (eapply weakening_value; [exact Hv | apply insert_subseteq; apply not_elem_of_dom; set_solver]);
    rewrite <- subst_open_var_tm by eauto;
    eapply H; [set_solver | | exact Hv'];
    rewrite insert_insert_ne by set_solver; reflexivity.
  - apply VT_Fix with (L := L ∪ {[xsub]} ∪ dom Γ0).
    let b := fresh "opened" in
    intros b Hb;
    change (<[b := sx]> Γ0 ⊢ᵥ
      open_value 0 (vfvar b) (value_subst xsub vx vf) ⋮ ((sx →ₜ T) →ₜ T));
    assert (Hxy : xsub <> b) by (intro; subst; apply Hb; set_solver);
    assert (Hlc_vx : lc_value vx) by exact (typing_value_lc _ _ _ Hv);
    assert (Hv' : <[b := sx]> Γ0 ⊢ᵥ vx ⋮ s) by
      (eapply weakening_value; [exact Hv | apply insert_subseteq; apply not_elem_of_dom; set_solver]);
    rewrite <- subst_open_var_value by eauto;
    eapply H; [set_solver | | exact Hv'];
    rewrite insert_insert_ne by set_solver; reflexivity.
  - constructor. eauto.
  - eapply TT_Let with (L := L ∪ {[xsub]} ∪ dom Γ0); eauto.
    let b := fresh "opened" in
    intros b Hb;
    change (<[b := T1]> Γ0 ⊢ₑ
      open_tm 0 (vfvar b) (tm_subst xsub vx e2) ⋮ T2);
    assert (Hxy : xsub <> b) by (intro; subst; apply Hb; set_solver);
    assert (Hlc_vx : lc_value vx) by exact (typing_value_lc _ _ _ Hv);
    assert (Hv' : <[b := T1]> Γ0 ⊢ᵥ vx ⋮ s) by
      (eapply weakening_value; [exact Hv | apply insert_subseteq; apply not_elem_of_dom; set_solver]);
    rewrite <- subst_open_var_tm by eauto;
    eapply H; [set_solver | | exact Hv'];
    rewrite insert_insert_ne by set_solver; reflexivity.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma subst_typing_insert_tm Γ x s e T vx :
  <[x := s]> Γ ⊢ₑ e ⋮ T →
  Γ ⊢ᵥ vx ⋮ s →
  Γ ⊢ₑ ({x := vx} e) ⋮ T.
Proof.
  intros Hty Hv.
  rename x into xsub.
  remember (<[xsub := s]> Γ) as Γx.
  revert Γ HeqΓx Hv.
  induction Hty using tm_has_type_mut with
      (P := fun Γx v T _ =>
        ∀ Γ, Γx = <[xsub := s]> Γ → Γ ⊢ᵥ vx ⋮ s →
          Γ ⊢ᵥ ({xsub := vx} v) ⋮ T)
      (P0 := fun Γx e T _ =>
        ∀ Γ, Γx = <[xsub := s]> Γ → Γ ⊢ᵥ vx ⋮ s →
          Γ ⊢ₑ ({xsub := vx} e) ⋮ T);
      intros Γ0 Heq Hv; subst; simpl.
  - constructor.
  - apply lookup_insert_Some in e as [[-> ->]|[Hne Hlook]].
    + cbn. rewrite decide_True by reflexivity.
      exact Hv.
    + cbn. rewrite decide_False by exact Hne.
      econstructor. exact Hlook.
  - apply VT_Lam with (L := L ∪ {[xsub]} ∪ dom Γ0).
    let b := fresh "opened" in
    intros b Hb;
    change (<[b := s0]> Γ0 ⊢ₑ
      open_tm 0 (vfvar b) (tm_subst xsub vx e) ⋮ T);
    assert (Hxy : xsub <> b) by (intro; subst; apply Hb; set_solver);
    assert (Hlc_vx : lc_value vx) by exact (typing_value_lc _ _ _ Hv);
    assert (Hv' : <[b := s0]> Γ0 ⊢ᵥ vx ⋮ s) by
      (eapply weakening_value; [exact Hv | apply insert_subseteq; apply not_elem_of_dom; set_solver]);
    rewrite <- subst_open_var_tm by eauto;
    eapply H; [set_solver | | exact Hv'];
    rewrite insert_insert_ne by set_solver; reflexivity.
  - apply VT_Fix with (L := L ∪ {[xsub]} ∪ dom Γ0).
    let b := fresh "opened" in
    intros b Hb;
    change (<[b := sx]> Γ0 ⊢ᵥ
      open_value 0 (vfvar b) (value_subst xsub vx vf) ⋮ ((sx →ₜ T) →ₜ T));
    assert (Hxy : xsub <> b) by (intro; subst; apply Hb; set_solver);
    assert (Hlc_vx : lc_value vx) by exact (typing_value_lc _ _ _ Hv);
    assert (Hv' : <[b := sx]> Γ0 ⊢ᵥ vx ⋮ s) by
      (eapply weakening_value; [exact Hv | apply insert_subseteq; apply not_elem_of_dom; set_solver]);
    rewrite <- subst_open_var_value by eauto;
    eapply H; [set_solver | | exact Hv'];
    rewrite insert_insert_ne by set_solver; reflexivity.
  - constructor. eauto.
  - eapply TT_Let with (L := L ∪ {[xsub]} ∪ dom Γ0); eauto.
    let b := fresh "opened" in
    intros b Hb;
    change (<[b := T1]> Γ0 ⊢ₑ
      open_tm 0 (vfvar b) (tm_subst xsub vx e2) ⋮ T2);
    assert (Hxy : xsub <> b) by (intro; subst; apply Hb; set_solver);
    assert (Hlc_vx : lc_value vx) by exact (typing_value_lc _ _ _ Hv);
    assert (Hv' : <[b := T1]> Γ0 ⊢ᵥ vx ⋮ s) by
      (eapply weakening_value; [exact Hv | apply insert_subseteq; apply not_elem_of_dom; set_solver]);
    rewrite <- subst_open_var_tm by eauto;
    eapply H; [set_solver | | exact Hv'];
    rewrite insert_insert_ne by set_solver; reflexivity.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma insert_delete_lookup_ty (Γ : gmap atom ty) x T :
  Γ !! x = Some T →
  <[x := T]> (delete x Γ) = Γ.
Proof.
  intros Hlook. apply map_eq. intros y.
  destruct (decide (x = y)) as [->|Hne].
  - rewrite lookup_insert. rewrite decide_True by reflexivity. symmetry. exact Hlook.
  - rewrite lookup_insert_ne by exact Hne.
    rewrite lookup_delete_ne by congruence.
    reflexivity.
Qed.

Lemma subst_typing_value Γ x s v T vx :
  Γ ⊢ᵥ v ⋮ T → ∅ ⊢ᵥ vx ⋮ s → Γ !! x = Some s →
  delete x Γ ⊢ᵥ ({x := vx} v) ⋮ T.
Proof.
  intros Hty Hv Hlook.
  eapply subst_typing_insert_value.
  rewrite insert_delete_lookup_ty by exact Hlook.
  exact Hty.
  eapply weakening_value; [exact Hv | apply map_empty_subseteq].
Qed.

Lemma subst_typing_tm Γ x s e T vx :
  Γ ⊢ₑ e ⋮ T → ∅ ⊢ᵥ vx ⋮ s → Γ !! x = Some s →
  delete x Γ ⊢ₑ ({x := vx} e) ⋮ T.
Proof.
  intros Hty Hv Hlook.
  eapply subst_typing_insert_tm.
  rewrite insert_delete_lookup_ty by exact Hlook.
  exact Hty.
  eapply weakening_value; [exact Hv | apply map_empty_subseteq].
Qed.
