(** * LocallyNameless.Classes

    Reusable theorem classes for locally-nameless developments.

    Unlike UnderType's original infrastructure, opening is parameterized by
    the payload type [O].  CoreLang opens terms with values, while ChoiceType
    qualifiers and types open binders with atoms. *)

From CoreLang Require Export Syntax.

(** ** Opening payloads *)

Class OpenVar O := open_var : atom -> O.

Class OpenArgLc O := open_arg_lc : O -> Prop.

#[global] Instance OpenVar_atom : OpenVar atom := fun x => x.
#[global] Instance OpenArgLc_atom : OpenArgLc atom := fun _ => True.
#[global] Instance Stale_atom : Stale atom := fun x => {[x]}.

(** ** Pure open/close/freshness classes *)

Class CloseOpenVar O A `{OpenVar O} `{Stale A} `{Open O A} `{Close A} :=
  close_open_var :
    forall (e : A) (x : atom) (k : nat),
      x # e ->
      {k <~ x} ({k ~> open_var x} e) = e.

Class OpenFv O A `{Stale O} `{Stale A} `{Open O A} :=
  open_fv :
    forall (e : A) (u : O) (k : nat),
      stale ({k ~> u} e) ⊆ stale u ∪ stale e.

Class OpenFvPrime O A `{Stale A} `{Open O A} :=
  open_fv' :
    forall (e : A) (u : O) (k : nat),
      stale e ⊆ stale ({k ~> u} e).

Class CloseVarFv A `{Stale A} `{Close A} :=
  close_var_fv :
    forall (e : A) (x : atom) (k : nat),
      stale ({k <~ x} e) = stale e ∖ {[x]}.

Class CloseFreshRec A `{Stale A} `{Close A} :=
  close_fresh_rec :
    forall (e : A) (x : atom) (k : nat),
      x # e ->
      {k <~ x} e = e.

Class CloseRmFv A `{Stale A} `{Close A} :=
  close_rm_fv :
    forall (e : A) (x : atom) (k : nat),
      x # ({k <~ x} e).

Class Fact1 O A `{Open O A} :=
  fact1 :
    forall (u v : O) (e : A) i j,
      i <> j ->
      {i ~> u} ({j ~> v} e) = {j ~> v} e ->
      {i ~> u} e = e.

Class OpenRecLc O A `{Open O A} `{Lc A} :=
  open_rec_lc :
    forall (e : A),
      is_lc e ->
      forall (k : nat) (u : O), {k ~> u} e = e.

Class OpenCloseVar O A `{OpenVar O} `{Open O A} `{Close A} `{Lc A} :=
  open_close_var :
    forall (e : A) (x : atom),
      is_lc e ->
      {0 ~> open_var x} ({0 <~ x} e) = e.

Class OpenSwap O A `{OpenArgLc O} `{Open O A} :=
  open_swap :
    forall (t : A) i j (u v : O),
      open_arg_lc u ->
      open_arg_lc v ->
      i <> j ->
      {i ~> v} ({j ~> u} t) = {j ~> u} ({i ~> v} t).

Class OpenLcRespect O A `{OpenArgLc O} `{Open O A} `{Lc A} :=
  open_lc_respect :
    forall (t : A) (u v : O) (k : nat),
      is_lc ({k ~> u} t) ->
      open_arg_lc u ->
      open_arg_lc v ->
      is_lc ({k ~> v} t).

Class OpenIdemp O A `{OpenArgLc O} `{Open O A} :=
  open_idemp :
    forall (t : A) (u v : O) (k : nat),
      open_arg_lc v ->
      {k ~> u} ({k ~> v} t) = {k ~> v} t.

(** ** Value-substitution classes *)

Class SubstFresh A `{Stale A} `{SubstV value A} :=
  subst_fresh :
    forall (e : A) (x : atom) (u : value),
      x # e ->
      {x := u} e = e.

Class SubstOpen A `{Open value A} `{SubstV value A} :=
  subst_open :
    forall (e : A) (u w : value) (x : atom) (k : nat),
      is_lc w ->
      {x := w} ({k ~> u} e) =
      {k ~> {x := w} u} ({x := w} e).

Class SubstOpenVar A `{Open value A} `{SubstV value A} :=
  subst_open_var :
    forall x y (u : value) (e : A) (k : nat),
      x <> y ->
      is_lc u ->
      {x := u} ({k ~> vfvar y} e) =
      {k ~> vfvar y} ({x := u} e).

Class SubstLc A `{SubstV value A} `{Lc A} :=
  subst_lc :
    forall (e : A),
      is_lc e ->
      forall (x : atom) (u : value),
        is_lc u ->
        is_lc ({x := u} e).

Class SubstIntro A `{Stale A} `{Open value A} `{SubstV value A} :=
  subst_intro :
    forall (e : A) (x : atom) (w : value) (k : nat),
      x # e ->
      is_lc w ->
      {x := w} ({k ~> vfvar x} e) = {k ~> w} e.

Class FvOfSubst A `{Stale A} `{SubstV value A} :=
  fv_of_subst :
    forall x (u : value) (e : A),
      stale ({x := u} e) ⊆ (stale e ∖ {[x]}) ∪ stale u.

Class FvOfSubstClosed A `{Stale A} `{SubstV value A} :=
  fv_of_subst_closed :
    forall x (u : value) (e : A),
      stale u = ∅ ->
      stale ({x := u} e) = stale e ∖ {[x]}.
