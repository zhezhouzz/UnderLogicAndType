(** * CoreLang.Properties

    Progress and preservation for the basic type system.
    All proofs are [Admitted] in this overnight skeleton; the
    statements are the ones needed by the denotational semantics. *)

From CoreLang Require Export BasicTyping SmallStep LocallyNamelessProps.

(** ** Canonical forms *)

Lemma canonical_arrow v s T :
  ∅ ⊢ᵥ v ⋮ (s →ₜ T) →
  (∃ s' e, v = vlam s' e) ∨ (∃ Tf vf, v = vfix Tf vf).
Proof.
  intros Hty. inversion Hty; subst; eauto.
  rewrite lookup_empty in H. discriminate.
Qed.

Lemma canonical_base v b :
  ∅ ⊢ᵥ v ⋮ TBase b →
  ∃ c, v = vconst c ∧ base_ty_of_const c = b.
Proof.
  intros Hty. inversion Hty; subst; eauto.
  rewrite lookup_empty in H. discriminate.
Qed.

(** ** Progress *)

Lemma progress e T :
  ∅ ⊢ₑ e ⋮ T →
  is_val e ∨ ∃ e', step e e'.
Proof.
  intros Hty.
  remember ∅ as Γ eqn:HΓ.
  induction Hty; subst.
  - left. apply is_val_tret.
  - destruct (IHHty eq_refl) as [[v Hv] | [e1' Hstep]].
    + subst. right. eexists. apply Step_head. apply HS_Ret.
      eapply typing_tm_lc. econstructor; eauto.
    + right. eexists. apply Step_let; eauto.
      eapply typing_tm_lc. econstructor; eauto.
  - destruct op; simpl in H; inversion H; subst;
      apply canonical_base in H0; destruct H0 as [c [-> Hc]];
      destruct c as [b|n]; simpl in Hc; try discriminate; right.
    + exists (tret (vconst (cbool (n =? 0)))).
      apply Step_head. eapply HS_Op; eauto.
    + exists (tret (vconst (cbool true))).
      apply Step_head. eapply HS_Op; eauto.
    + exists (tret (vconst (cnat 0))).
      apply Step_head. eapply HS_Op; eauto.
    + exists (tret (vconst (cnat (S n)))).
      apply Step_head. eapply HS_Op; eauto.
    + exists (tret (vconst (cnat (Nat.pred n)))).
      apply Step_head. eapply HS_Op; eauto.
  - pose proof H as Hfun.
    apply canonical_arrow in H.
    destruct H as [[s' [body ->]] | [Tf [vf ->]]].
    + right. eexists. apply Step_head. apply HS_Beta.
      eapply typing_tm_lc. econstructor; eauto.
    + right. eexists. apply Step_head. apply HS_Fix.
      eapply typing_tm_lc. econstructor; eauto.
  - apply canonical_base in H. destruct H as [c [-> Hc]].
    destruct c as [b|n]; simpl in Hc; try discriminate.
    destruct b.
    + right. eexists. apply Step_head. apply HS_MatchTrue.
      eapply typing_tm_lc. econstructor; eauto.
    + right. eexists. apply Step_head. apply HS_MatchFalse.
      eapply typing_tm_lc. econstructor; eauto.
Qed.

(** ** Preservation *)

Lemma preservation e e' T :
  ∅ ⊢ₑ e ⋮ T → step e e' → ∅ ⊢ₑ e' ⋮ T.
Proof. Admitted.

(** ** LN lemmas proofs (deferred) *)

(** All LN lemmas stated in [Syntax.v] are proved here by mutual
    induction on the derivations.  We mark them all Admitted for now. *)

(** [open_rec_lc] *)
Lemma open_rec_lc_value_proof k u (v : value) : lc_value v → open_value k u v = v.
Proof. intros Hlc. by apply open_rec_lc_value. Qed.

Lemma open_rec_lc_tm_proof k u (e : tm) : lc_tm e → open_tm k u e = e.
Proof. intros Hlc. by apply open_rec_lc_tm. Qed.

(** [subst_fresh] *)
Lemma subst_fresh_value_proof x u (v : value) :
  x ∉ fv_value v → value_subst x u v = v.
Proof. apply subst_fresh_value_proven. Qed.

Lemma subst_fresh_tm_proof x u (e : tm) :
  x ∉ fv_tm e → tm_subst x u e = e.
Proof. apply subst_fresh_tm_proven. Qed.

(** [subst_open] *)
Lemma subst_open_value_proof x u s (v : value) k :
  lc_value u →
  value_subst x u (open_value k s v) =
  open_value k (value_subst x u s) (value_subst x u v).
Proof. apply subst_open_value. Qed.

Lemma subst_open_tm_proof x u s (e : tm) k :
  lc_value u →
  tm_subst x u (open_tm k s e) =
  open_tm k (value_subst x u s) (tm_subst x u e).
Proof. apply subst_open_tm. Qed.
