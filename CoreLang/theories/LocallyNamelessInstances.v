(** * CoreLang.LocallyNamelessInstances

    Typeclass instances exposing the concrete CoreLang locally-nameless lemmas
    through the reusable classes in [LocallyNameless.Classes]. *)

From LocallyNameless Require Import Classes.
From CoreLang Require Import LocallyNamelessProps LocallyNamelessExtra.

#[global] Instance OpenVar_value : OpenVar value := vfvar.
#[global] Instance OpenArgLc_value : OpenArgLc value := lc_value.

(** ** Opening and closing *)

#[global] Instance CloseOpenVar_value : CloseOpenVar value value.
Proof. intros v x k Hx. exact (close_open_var_value v x k Hx). Qed.

#[global] Instance CloseOpenVar_tm : CloseOpenVar value tm.
Proof. intros e x k Hx. exact (close_open_var_tm e x k Hx). Qed.

#[global] Instance OpenFv_value : OpenFv value value.
Proof. intros v u k. exact (open_fv_value v u k). Qed.

#[global] Instance OpenFv_tm : OpenFv value tm.
Proof. intros e u k. exact (open_fv_tm e u k). Qed.

#[global] Instance OpenFvPrime_value : OpenFvPrime value value.
Proof. intros v u k. exact (open_fv_value' v u k). Qed.

#[global] Instance OpenFvPrime_tm : OpenFvPrime value tm.
Proof. intros e u k. exact (open_fv_tm' e u k). Qed.

#[global] Instance CloseFreshRec_value : CloseFreshRec value.
Proof. intros v x k Hx. exact (close_fresh_rec_value x k v Hx). Qed.

#[global] Instance CloseFreshRec_tm : CloseFreshRec tm.
Proof. intros e x k Hx. exact (close_fresh_rec_tm x k e Hx). Qed.

#[global] Instance CloseRmFv_value : CloseRmFv value.
Proof. intros v x k. exact (close_rm_fv_value x k v). Qed.

#[global] Instance CloseRmFv_tm : CloseRmFv tm.
Proof. intros e x k. exact (close_rm_fv_tm x k e). Qed.

#[global] Instance Fact1_value : Fact1 value value.
Proof. intros u v e i j Hij Heq. exact (open_rec_open_eq_value u v e i j Hij Heq). Qed.

#[global] Instance Fact1_tm : Fact1 value tm.
Proof. intros u v e i j Hij Heq. exact (open_rec_open_eq_tm u v e i j Hij Heq). Qed.

#[global] Instance OpenRecLc_value : OpenRecLc value value.
Proof. intros v Hlc k u. exact (open_rec_lc_value v Hlc k u). Qed.

#[global] Instance OpenRecLc_tm : OpenRecLc value tm.
Proof. intros e Hlc k u. exact (open_rec_lc_tm e Hlc k u). Qed.

#[global] Instance OpenCloseVar_value : OpenCloseVar value value.
Proof. intros v x Hlc. exact (open_close_var_value x v Hlc). Qed.

#[global] Instance OpenCloseVar_tm : OpenCloseVar value tm.
Proof. intros e x Hlc. exact (open_close_var_tm x e Hlc). Qed.

#[global] Instance OpenSwap_value : OpenSwap value value.
Proof. intros v i j u w Hu Hw Hij. exact (open_swap_value v i j u w Hu Hw Hij). Qed.

#[global] Instance OpenSwap_tm : OpenSwap value tm.
Proof. intros e i j u w Hu Hw Hij. exact (open_swap_tm e i j u w Hu Hw Hij). Qed.

#[global] Instance OpenLcRespect_value : OpenLcRespect value value.
Proof.
  intros v u w k Hopen Hu Hw.
  exact (open_lc_respect_value k u w v Hu Hw Hopen).
Qed.

#[global] Instance OpenLcRespect_tm : OpenLcRespect value tm.
Proof.
  intros e u w k Hopen Hu Hw.
  exact (open_lc_respect_tm k u w e Hu Hw Hopen).
Qed.

(** ** Value substitution *)

#[global] Instance SubstFresh_value : SubstFresh value.
Proof. intros v x u Hx. exact (subst_fresh_value_proven x u v Hx). Qed.

#[global] Instance SubstFresh_tm : SubstFresh tm.
Proof. intros e x u Hx. exact (subst_fresh_tm_proven x u e Hx). Qed.

#[global] Instance SubstOpen_value : SubstOpen value.
Proof. intros v u w x k Hw. exact (subst_open_value x u w k v Hw). Qed.

#[global] Instance SubstOpen_tm : SubstOpen tm.
Proof. intros e u w x k Hw. exact (subst_open_tm x u w k e Hw). Qed.

#[global] Instance SubstOpenVar_value : SubstOpenVar value.
Proof. intros x y u v k Hxy Hu. exact (subst_open_var_value x y u k v Hxy Hu). Qed.

#[global] Instance SubstOpenVar_tm : SubstOpenVar tm.
Proof. intros x y u e k Hxy Hu. exact (subst_open_var_tm x y u k e Hxy Hu). Qed.

#[global] Instance SubstLc_value : SubstLc value.
Proof. intros v Hlc x u Hu. exact (subst_lc_value x u v Hlc Hu). Qed.

#[global] Instance SubstLc_tm : SubstLc tm.
Proof. intros e Hlc x u Hu. exact (subst_lc_tm x u e Hlc Hu). Qed.

#[global] Instance SubstIntro_value : SubstIntro value.
Proof. intros v x w k Hx Hw. exact (subst_intro_value x w k v Hx Hw). Qed.

#[global] Instance SubstIntro_tm : SubstIntro tm.
Proof. intros e x w k Hx Hw. exact (subst_intro_tm x w k e Hx Hw). Qed.

#[global] Instance FvOfSubst_value : FvOfSubst value.
Proof. intros x u v. exact (fv_of_subst_value x u v). Qed.

#[global] Instance FvOfSubst_tm : FvOfSubst tm.
Proof. intros x u e. exact (fv_of_subst_tm x u e). Qed.

#[global] Instance FvOfSubstClosed_value : FvOfSubstClosed value.
Proof. intros x u v Hu. exact (fv_of_subst_value_closed x u v Hu). Qed.

#[global] Instance FvOfSubstClosed_tm : FvOfSubstClosed tm.
Proof. intros x u e Hu. exact (fv_of_subst_tm_closed x u e Hu). Qed.
