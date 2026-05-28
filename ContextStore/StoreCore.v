(** * Generic stores: core definitions *)

From ContextBase Require Import Prelude LogicVar BaseTactics.
From Stdlib Require Import Logic.ProofIrrelevance.

Section AbstractStoreCore.

Context {V : Type} `{ValueSig V}.

Definition StoreA (K : Type) `{Countable K} : Type := gmap K V.

Typeclasses Transparent StoreA.

Record StoreAOn {K : Type} `{Countable K} (D : gset K) : Type := {
  storeAO_store : StoreA K;
  storeAO_dom : dom (storeAO_store : StoreA K) = D;
}.

Local Arguments storeAO_store {_ _ _ _} _.
Local Arguments storeAO_dom {_ _ _ _} _.

Definition storeA_on_ext {K : Type} `{Countable K} (D : gset K)
    (s1 s2 : StoreAOn D) :
  storeAO_store s1 = storeAO_store s2 ->
  s1 = s2.
Proof.
  destruct s1 as [s1 H1], s2 as [s2 H2]. simpl.
  intros ->. f_equal. apply proof_irrelevance.
Qed.

Definition storeA_compat {K : Type} `{Countable K}
    (s1 s2 : StoreA K) : Prop :=
  map_compat V s1 s2.

Definition storeA_agree_on {K : Type} `{Countable K}
    (D : gset K) (s1 s2 : StoreA K) : Prop :=
  forall x, x ∈ D -> s1 !! x = s2 !! x.

Definition storeA_restrict {K : Type} `{Countable K}
    (s : StoreA K) (X : gset K) : StoreA K :=
  map_restrict V s X.

Definition storeA_map_key
    {K K' : Type} `{Countable K} `{Countable K'}
    (f : K → K') (s : StoreA K) : StoreA K' :=
  kmap f s.

Definition storeA_rekey {K : Type} `{Countable K}
    (f : K → K) (s : StoreA K) : StoreA K :=
  storeA_map_key f s.

Definition storeA_swap {K : Type} `{Countable K}
    (x y : K) (s : StoreA K) : StoreA K :=
  storeA_rekey (swap x y) s.

Definition storeA_shift {K : Type} `{Countable K} `{!ShiftKey K}
    (k : nat) (s : StoreA K) : StoreA K :=
  storeA_rekey (key_shift k) s.

Definition storeA_bind {K : Type} `{Countable K}
    (s1 s2 s : StoreA K) : Prop :=
  dom s1 ## dom s2 ∧ s = @union (gmap K V) _ s1 s2.

Lemma storeA_map_eq {K : Type} `{Countable K} (s1 s2 : StoreA K) :
  (∀ x, s1 !! x = s2 !! x) →
  s1 = s2.
Proof.
  intros Hlook. apply (map_eq (M:=gmap K)). exact Hlook.
Qed.

Lemma storeA_agree_on_mono {K : Type} `{Countable K}
    D E (s1 s2 : StoreA K) :
  D ⊆ E ->
  storeA_agree_on E s1 s2 ->
  storeA_agree_on D s1 s2.
Proof.
  intros Hsub Hag x Hx. apply Hag, Hsub, Hx.
Qed.

Lemma storeA_agree_on_refl {K : Type} `{Countable K}
    D (s : StoreA K) :
  storeA_agree_on D s s.
Proof.
  intros x Hx. reflexivity.
Qed.

Lemma storeA_agree_on_sym {K : Type} `{Countable K}
    D (s1 s2 : StoreA K) :
  storeA_agree_on D s1 s2 ->
  storeA_agree_on D s2 s1.
Proof.
  intros Hag x Hx. symmetry. apply Hag, Hx.
Qed.

Lemma storeA_agree_on_union {K : Type} `{Countable K}
    D1 D2 (s1 s2 : StoreA K) :
  storeA_agree_on D1 s1 s2 ->
  storeA_agree_on D2 s1 s2 ->
  storeA_agree_on (D1 ∪ D2) s1 s2.
Proof.
  intros H1 H2 x Hx.
  apply elem_of_union in Hx as [Hx|Hx]; [apply H1|apply H2]; exact Hx.
Qed.

Lemma storeA_agree_on_insert_same {K : Type} `{Countable K}
    D (s1 s2 : StoreA K) x v :
  storeA_agree_on (D ∖ {[x]}) s1 s2 ->
  storeA_agree_on D (<[x := v]> s1) (<[x := v]> s2).
Proof.
  intros Hag y Hy.
  destruct (decide (y = x)) as [->|Hyx].
  - change ((<[x := v]> (s1 : gmap K V) !! x) =
      (<[x := v]> (s2 : gmap K V) !! x)).
    rewrite !map_lookup_insert. reflexivity.
  - change ((<[x := v]> (s1 : gmap K V) !! y) =
      (<[x := v]> (s2 : gmap K V) !! y)).
    rewrite !map_lookup_insert_ne by congruence.
    apply Hag. apply elem_of_difference. split; [exact Hy|better_set_solver].
Qed.

Lemma storeA_agree_on_insert_same_keep {K : Type} `{Countable K}
    D (s1 s2 : StoreA K) x v :
  storeA_agree_on D s1 s2 ->
  storeA_agree_on (D ∪ {[x]}) (<[x := v]> s1) (<[x := v]> s2).
Proof.
  intros Hag.
  apply storeA_agree_on_union.
  - intros y Hy.
    destruct (decide (y = x)) as [->|Hyx].
    + change ((<[x := v]> (s1 : gmap K V) !! x) =
        (<[x := v]> (s2 : gmap K V) !! x)).
      rewrite !map_lookup_insert. reflexivity.
    + change ((<[x := v]> (s1 : gmap K V) !! y) =
        (<[x := v]> (s2 : gmap K V) !! y)).
      rewrite !map_lookup_insert_ne by congruence. apply Hag, Hy.
  - intros y Hy.
    rewrite elem_of_singleton in Hy. subst y.
    change ((<[x := v]> (s1 : gmap K V) !! x) =
      (<[x := v]> (s2 : gmap K V) !! x)).
    rewrite !map_lookup_insert. reflexivity.
Qed.

Lemma storeA_bind_dom {K : Type} `{Countable K}
    (s1 s2 s : StoreA K) :
  storeA_bind s1 s2 s →
  dom s = dom s1 ∪ dom s2.
Proof.
  intros [_ ->].
  change (dom (@union (gmap K V) _ (s1 : gmap K V) (s2 : gmap K V)) =
    dom (s1 : gmap K V) ∪ dom (s2 : gmap K V)).
  better_set_solver.
Qed.

End AbstractStoreCore.

Arguments storeAO_store {_ _ _ _ _} _.
Arguments storeAO_dom {_ _ _ _ _} _.

(** ** Generic stores: key actions *)

Section AbstractStoreCore.

Context {V : Type} `{ValueSig V}.

Lemma storeA_rekey_lookup {K : Type} `{Countable K}
    (f : K → K) (Hf : Inj (=) (=) f) (s : StoreA K) (z : K) :
  ((storeA_rekey f s : gmap K V) !! f z) =
  ((s : gmap K V) !! z).
Proof.
  unfold storeA_rekey, storeA_map_key.
  change (kmap (M2:=gmap K) f s !! f z = s !! z).
  rewrite (lookup_kmap (M1:=gmap K) (M2:=gmap K)
    (Inj0:=Hf) f s z).
  reflexivity.
Qed.

Lemma storeA_rekey_dom {K : Type} `{Countable K}
    (f : K → K) (Hf : Inj (=) (=) f) (s : StoreA K) :
  dom (storeA_rekey f s : gmap K V) = set_map f (dom (s : gmap K V)).
Proof.
  unfold storeA_rekey, storeA_map_key.
  change (dom (kmap (M2:=gmap K) f s) =
    set_map f (dom (s : gmap K V))).
  rewrite (dom_kmap_L (M:=gmap K) (M2:=gmap K)
    (Inj0:=Hf) f (s : gmap K V)).
  reflexivity.
Qed.

Definition storeA_rekey_inj_on_dom {K : Type} `{Countable K}
    (f : K → K) (s : StoreA K) : Prop :=
  forall x y,
    x ∈ dom (s : gmap K V) ->
    y ∈ dom (s : gmap K V) ->
    f x = f y ->
    x = y.

Lemma storeA_rekey_mapped_fst_nodup {K : Type} `{Countable K}
    (f : K → K) (s : StoreA K) :
  storeA_rekey_inj_on_dom f s ->
  NoDup ((prod_map f id <$> map_to_list (s : gmap K V)).*1).
Proof.
  intros Hinj.
  replace ((prod_map f id <$> map_to_list (s : gmap K V)).*1)
    with ((fun p : K * V => f p.1) <$> map_to_list (s : gmap K V)).
  2:{
    induction (map_to_list (s : gmap K V)) as [|[x v] l IH];
      simpl; [reflexivity|].
    f_equal. exact IH.
  }
  apply NoDup_fmap_2_strong.
  - intros [x vx] [y vy] Hx Hy Heq. simpl in Heq.
    assert (Hxy : x = y).
    {
      apply Hinj.
      - apply elem_of_dom. exists vx. rewrite <- elem_of_map_to_list. exact Hx.
      - apply elem_of_dom. exists vy. rewrite <- elem_of_map_to_list. exact Hy.
      - exact Heq.
    }
    subst y.
    assert (vx = vy).
    {
      rewrite elem_of_map_to_list in Hx.
      rewrite elem_of_map_to_list in Hy.
      rewrite Hx in Hy. inversion Hy. reflexivity.
    }
    subst vy. reflexivity.
  - apply NoDup_map_to_list.
Qed.

Lemma storeA_rekey_lookup_Some_inj_on {K : Type} `{Countable K}
    (f : K → K) (s : StoreA K) (z : K) (v : V) :
  storeA_rekey_inj_on_dom f s ->
  ((storeA_rekey f s : gmap K V) !! z = Some v <->
    exists x, z = f x /\ (s : gmap K V) !! x = Some v).
Proof.
  intros Hinj.
  unfold storeA_rekey, storeA_map_key, kmap.
  rewrite <- elem_of_list_to_map.
  - rewrite list_elem_of_fmap.
    split.
    + intros [[x vx] [Hz Hv]]. simpl in Hz. inversion Hz. subst.
      rewrite elem_of_map_to_list in Hv.
      exists x. split; [reflexivity|exact Hv].
    + intros [x [Hz Hx]]. exists (x, v). split.
      * subst z. reflexivity.
      * rewrite elem_of_map_to_list. exact Hx.
  - apply storeA_rekey_mapped_fst_nodup. exact Hinj.
Qed.

Lemma storeA_rekey_lookup_None_inj_on {K : Type} `{Countable K}
    (f : K → K) (s : StoreA K) (z : K) :
  storeA_rekey_inj_on_dom f s ->
  ((storeA_rekey f s : gmap K V) !! z = None <->
    forall x, z = f x -> (s : gmap K V) !! x = None).
Proof.
  intros Hinj.
  rewrite <- !not_elem_of_dom.
  split.
  - intros Hnone x Hz.
    apply not_elem_of_dom. intros Hx.
    apply Hnone. apply elem_of_dom in Hx as [v Hv].
    apply elem_of_dom. exists v.
    apply storeA_rekey_lookup_Some_inj_on; [exact Hinj|].
    exists x. split; [exact Hz|exact Hv].
  - intros Hnone Hz.
    apply elem_of_dom in Hz as [v Hv].
    apply storeA_rekey_lookup_Some_inj_on in Hv as [x [Hz Hx]];
      [|exact Hinj].
    rewrite (Hnone x Hz) in Hx. discriminate.
Qed.

Lemma storeA_rekey_dom_inj_on {K : Type} `{Countable K}
    (f : K → K) (s : StoreA K) :
  storeA_rekey_inj_on_dom f s ->
  dom (storeA_rekey f s : gmap K V) = set_map f (dom (s : gmap K V)).
Proof.
  intros Hinj.
  apply set_eq. intros z.
  rewrite elem_of_dom, elem_of_map.
  split.
  - intros [v Hv].
    apply storeA_rekey_lookup_Some_inj_on in Hv as [x [Hz Hx]];
      [|exact Hinj].
    exists x. split; [exact Hz|].
    apply elem_of_dom. exists v. exact Hx.
  - intros [x [Hz Hx]].
    apply elem_of_dom in Hx as [v Hv].
    exists v.
    apply storeA_rekey_lookup_Some_inj_on; [exact Hinj|].
    exists x. split; [exact Hz|exact Hv].
Qed.

Lemma storeA_rekey_lookup_none_inj_on {K : Type} `{Countable K}
    (f : K → K) (s : StoreA K) (x : K) :
  (s : gmap K V) !! x = None ->
  (forall y,
      y ∈ dom (s : gmap K V) ->
      f y <> f x) ->
  (storeA_rekey f s : gmap K V) !! f x = None.
Proof.
  intros Hnone Hfresh.
  apply not_elem_of_dom. intros Hin.
  apply elem_of_dom in Hin as [v Hv].
  unfold storeA_rekey, storeA_map_key, kmap in Hv.
  apply elem_of_list_to_map_2 in Hv.
  apply list_elem_of_fmap in Hv as [[y vy] [Hy Hlook]].
  simpl in Hy. injection Hy as Hkey Hval. subst vy.
  rewrite elem_of_map_to_list in Hlook.
  apply (Hfresh y); [apply elem_of_dom; eauto|symmetry; exact Hkey].
Qed.

Lemma storeA_rekey_insert_inj_on {K : Type} `{Countable K}
    (f : K → K) z v (s : StoreA K) :
  (s : gmap K V) !! z = None ->
  storeA_rekey_inj_on_dom f (<[z := v]> (s : gmap K V)) ->
  storeA_rekey f (<[z := v]> s) =
  <[f z := v]> (storeA_rekey f s : gmap K V).
Proof.
  intros Hnone Hinj.
  apply storeA_map_eq. intros y.
  change (((storeA_rekey f (<[z := v]> s) : gmap K V) !! y) =
    ((<[f z := v]> (storeA_rekey f s : gmap K V)) !! y)).
  destruct (decide (y = f z)) as [->|Hy].
  - rewrite lookup_insert_eq.
    apply storeA_rekey_lookup_Some_inj_on.
    + exact Hinj.
    + exists z. split; [reflexivity|].
      change ((<[z := v]> (s : gmap K V)) !! z = Some v).
      rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by (intros Heq; apply Hy; symmetry; exact Heq).
    destruct ((storeA_rekey f s : gmap K V) !! y) as [w|] eqn:Hylook.
    + apply storeA_rekey_lookup_Some_inj_on.
      * exact Hinj.
      * apply storeA_rekey_lookup_Some_inj_on in Hylook as [x [Hyx Hx]].
        -- exists x. split; [exact Hyx|].
           change ((<[z := v]> (s : gmap K V)) !! x = Some w).
           rewrite lookup_insert_ne.
           ++ exact Hx.
           ++ intros ->. apply Hy. exact Hyx.
        -- intros a b Ha Hb Hab.
           apply Hinj.
           ++ change (a ∈ dom (<[z := v]> (s : gmap K V))).
              rewrite dom_insert_L. apply elem_of_union_r. exact Ha.
           ++ change (b ∈ dom (<[z := v]> (s : gmap K V))).
              rewrite dom_insert_L. apply elem_of_union_r. exact Hb.
           ++ exact Hab.
    + apply storeA_rekey_lookup_None_inj_on.
      * exact Hinj.
      * intros x Hyx.
        destruct (decide (x = z)) as [->|Hxz].
        -- exfalso. apply Hy. exact Hyx.
        -- change ((<[z := v]> (s : gmap K V)) !! x = None).
           rewrite lookup_insert_ne by (intros Heq; apply Hxz; symmetry; exact Heq).
           assert (Hinj_s : storeA_rekey_inj_on_dom f s).
           {
             intros a b Ha Hb Hab.
              apply Hinj.
              ** change (a ∈ dom (<[z := v]> (s : gmap K V))).
                 rewrite dom_insert_L. apply elem_of_union_r. exact Ha.
              ** change (b ∈ dom (<[z := v]> (s : gmap K V))).
                 rewrite dom_insert_L. apply elem_of_union_r. exact Hb.
              ** exact Hab.
           }
           pose proof (storeA_rekey_lookup_None_inj_on f s y Hinj_s)
             as [Hto _].
           exact (Hto Hylook x Hyx).
Qed.

Lemma storeA_rekey_ext_on_dom {K : Type} `{Countable K}
    (f g : K → K) (s : StoreA K) :
  (forall x, x ∈ dom (s : gmap K V) -> f x = g x) ->
  storeA_rekey f s = storeA_rekey g s.
Proof.
  intros Hext.
  unfold storeA_rekey, storeA_map_key, kmap.
  f_equal.
  set (l := map_to_list (s : gmap K V)).
  assert (Hdom : forall x v, (x, v) ∈ l -> x ∈ dom (s : gmap K V)).
  {
    subst l. intros x v Hin.
    apply elem_of_dom. exists v.
    rewrite <- elem_of_map_to_list. exact Hin.
  }
  clearbody l.
  induction l as [|[x v] l IH]; simpl; [reflexivity|].
  f_equal.
  - simpl. rewrite Hext by (apply (Hdom x v); left; reflexivity).
    reflexivity.
  - apply IH. intros y w Hin.
    apply (Hdom y w). right. exact Hin.
Qed.

Lemma storeA_rekey_compose_inj_on {K : Type} `{Countable K}
    (f g : K → K) (s : StoreA K) :
  storeA_rekey_inj_on_dom g s ->
  storeA_rekey_inj_on_dom f (storeA_rekey g s) ->
  storeA_rekey f (storeA_rekey g s) =
  storeA_rekey (fun x => f (g x)) s.
Proof.
  intros Hg Hf.
  assert (Hcomp : storeA_rekey_inj_on_dom (fun x => f (g x)) s).
  {
    intros x y Hx Hy Heq.
    apply Hg; [exact Hx|exact Hy|].
    apply Hf.
    - rewrite storeA_rekey_dom_inj_on by exact Hg.
      apply elem_of_map. exists x. split; [reflexivity|exact Hx].
    - rewrite storeA_rekey_dom_inj_on by exact Hg.
      apply elem_of_map. exists y. split; [reflexivity|exact Hy].
    - exact Heq.
  }
  apply storeA_map_eq. intros z.
  change (((storeA_rekey f (storeA_rekey g s) : gmap K V) !! z) =
    ((storeA_rekey (fun x => f (g x)) s : gmap K V) !! z)).
  destruct ((storeA_rekey f (storeA_rekey g s) : gmap K V) !! z)
    as [v|] eqn:HL.
  - apply storeA_rekey_lookup_Some_inj_on in HL as [y [Hz Hy]];
      [|exact Hf].
    apply storeA_rekey_lookup_Some_inj_on in Hy as [x [Hy Hx]];
      [|exact Hg].
    symmetry. apply storeA_rekey_lookup_Some_inj_on; [exact Hcomp|].
    subst y. exists x. split; [exact Hz|exact Hx].
  - destruct ((storeA_rekey (fun x => f (g x)) s : gmap K V) !! z)
      as [v|] eqn:HR; [|reflexivity].
    exfalso.
    apply storeA_rekey_lookup_Some_inj_on in HR as [x [Hz Hx]];
      [|exact Hcomp].
    assert (Hgx : (storeA_rekey g s : gmap K V) !! g x = Some v).
    {
      apply storeA_rekey_lookup_Some_inj_on; [exact Hg|].
      exists x. split; [reflexivity|exact Hx].
    }
    assert (HLsome :
      (storeA_rekey f (storeA_rekey g s) : gmap K V) !! z = Some v).
    {
      apply storeA_rekey_lookup_Some_inj_on; [exact Hf|].
      exists (g x). split; [exact Hz|exact Hgx].
    }
    rewrite HL in HLsome. discriminate.
Qed.

Lemma storeA_rekey_compose {K : Type} `{Countable K}
    (f g : K → K) (Hf : Inj (=) (=) f) (Hg : Inj (=) (=) g)
    (s : StoreA K) :
  storeA_rekey (V:=V) (K:=K) f (storeA_rekey (V:=V) (K:=K) g s) =
  storeA_rekey (V:=V) (K:=K) (fun x => f (g x)) s.
Proof.
  apply storeA_rekey_compose_inj_on.
  - intros a b _ _ Hab. apply Hg. exact Hab.
  - intros a b _ _ Hab. apply Hf. exact Hab.
Qed.

Definition storeA_on_rekey {K : Type} `{Countable K}
    (f : K → K) (Hf : Inj (=) (=) f)
    {D : gset K} (s : StoreAOn (V:=V) D) : StoreAOn (V:=V) (set_map f D).
Proof.
  destruct s as [s Hdom].
  refine {| storeAO_store := storeA_rekey f s |}.
  change (dom (storeA_rekey f s : gmap K V) = set_map f D).
  rewrite storeA_rekey_dom by exact Hf.
  replace (dom (s : gmap K V)) with D by (symmetry; exact Hdom).
  reflexivity.
Defined.

Lemma storeA_rekey_empty {K : Type} `{Countable K}
    (f : K → K) :
  storeA_rekey f (∅ : StoreA K) = (∅ : gmap K V).
Proof.
  unfold storeA_rekey, storeA_map_key.
  change (kmap (M2:=gmap K) f (∅ : gmap K V) =
    (∅ : gmap K V)).
  apply kmap_empty.
Qed.

Lemma storeA_rekey_insert {K : Type} `{Countable K}
    (f : K → K) (Hf : Inj (=) (=) f) z v (s : StoreA K) :
  storeA_rekey f (<[z := v]> s) =
  <[f z := v]> (storeA_rekey f s : gmap K V).
Proof.
  unfold storeA_rekey, storeA_map_key.
  change (kmap f (<[z := v]> (s : gmap K V)) =
    (<[f z := v]> (kmap f (s : gmap K V)) : gmap K V)).
  refine (@kmap_insert K (gmap K) _ _ _ _ _ _ _ _ _
    K (gmap K) _ _ _ _ _ _ _ _ _
    f _ V (s : gmap K V) z v).
Qed.

Lemma storeA_rekey_delete {K : Type} `{Countable K}
    (f : K → K) (Hf : Inj (=) (=) f) z (s : StoreA K) :
  storeA_rekey f (delete z s) =
  delete (f z) (storeA_rekey f s : gmap K V).
Proof.
  unfold storeA_rekey, storeA_map_key.
  change (kmap (M2:=gmap K) f (delete z (s : gmap K V)) =
    delete (f z) (kmap (M2:=gmap K) f (s : gmap K V))).
  refine (@kmap_delete K (gmap K) _ _ _ _ _ _ _ _ _
    K (gmap K) _ _ _ _ _ _ _ _ _
    f _ V (s : gmap K V) z).
Qed.

Lemma storeA_rekey_union {K : Type} `{Countable K}
    (f : K → K) (Hf : Inj (=) (=) f) (s1 s2 : StoreA K) :
  storeA_rekey f (@union (gmap K V) _ s1 s2) =
  @union (gmap K V) _
    (storeA_rekey f s1 : gmap K V) (storeA_rekey f s2 : gmap K V).
Proof.
  unfold storeA_rekey, storeA_map_key.
  change (kmap f (@union (gmap K V) _ (s1 : gmap K V) (s2 : gmap K V)) =
    @union (gmap K V) _
      (kmap f (s1 : gmap K V))
      (kmap f (s2 : gmap K V))).
  refine (@kmap_union K (gmap K) _ _ _ _ _ _ _ _ _
    K (gmap K) _ _ _ _ _ _ _ _ _
    f _ V (s1 : gmap K V) (s2 : gmap K V)).
Qed.

Lemma storeA_map_key_lookup {K K' : Type} `{Countable K} `{Countable K'}
    (f : K → K') (Hf : Inj (=) (=) f) (s : StoreA K) (z : K) :
  ((storeA_map_key f s : gmap K' V) !! f z) =
  ((s : gmap K V) !! z).
Proof.
  unfold storeA_map_key.
  change (kmap (M1:=gmap K) (M2:=gmap K') f s !! f z = s !! z).
  rewrite (lookup_kmap (M1:=gmap K) (M2:=gmap K')
    (Inj0:=Hf) f s z).
  reflexivity.
Qed.

Lemma storeA_map_key_dom {K K' : Type} `{Countable K} `{Countable K'}
    (f : K → K') (Hf : Inj (=) (=) f) (s : StoreA K) :
  dom (storeA_map_key f s : gmap K' V) = set_map f (dom (s : gmap K V)).
Proof.
  unfold storeA_map_key.
  change (dom (kmap (M1:=gmap K) (M2:=gmap K') f s) =
    set_map f (dom (s : gmap K V))).
  rewrite (dom_kmap_L (M:=gmap K) (M2:=gmap K')
    (Inj0:=Hf) f (s : gmap K V)).
  reflexivity.
Qed.

Lemma storeA_map_key_insert {K K' : Type} `{Countable K} `{Countable K'}
    (f : K → K') (Hf : Inj (=) (=) f) z v (s : StoreA K) :
  storeA_map_key f (<[z := v]> s) =
  <[f z := v]> (storeA_map_key f s : gmap K' V).
Proof.
  unfold storeA_map_key.
  change (kmap f (<[z := v]> (s : gmap K V)) =
    (<[f z := v]> (kmap f (s : gmap K V)) : gmap K' V)).
  refine (@kmap_insert K (gmap K) _ _ _ _ _ _ _ _ _
    K' (gmap K') _ _ _ _ _ _ _ _ _
    f _ V (s : gmap K V) z v).
Qed.

Lemma storeA_on_rekey_id_on_dom {K : Type} `{Countable K}
    (f : K → K) (Hf : Inj (=) (=) f)
    (D : gset K) (s : StoreAOn (V:=V) D) :
  (forall x, x ∈ D -> f x = x) ->
  storeAO_store (storeA_on_rekey f Hf s) = storeAO_store s.
Proof.
  intros Hid.
  destruct s as [s Hdom]. cbn [storeAO_store storeA_on_rekey].
  apply (map_eq (M:=gmap K)). intros z.
  destruct ((s : gmap K V) !! z) as [v|] eqn:Hz.
  - assert (HzD : z ∈ D).
    { rewrite <- Hdom. by apply elem_of_dom_2 in Hz. }
    rewrite <- (Hid z HzD) at 1.
    rewrite storeA_rekey_lookup by exact Hf. exact Hz.
  - destruct ((storeA_rekey f s : gmap K V) !! z) as [v|] eqn:Hzr;
      [|reflexivity].
    exfalso.
    assert (Hzdom : z ∈ dom (storeA_rekey f s : gmap K V)).
    { by apply elem_of_dom_2 in Hzr. }
    rewrite storeA_rekey_dom in Hzdom by exact Hf.
    apply elem_of_map in Hzdom as [u [Hzu HuD]].
    assert (HuD' : u ∈ D).
    { rewrite <- Hdom. exact HuD. }
    rewrite Hid in Hzu by exact HuD'. subst z.
    change (u ∈ dom (s : gmap K V)) in HuD.
    apply elem_of_dom in HuD as [w Hw]. congruence.
Qed.

End AbstractStoreCore.

Section AbstractStoreCore.

Context {V : Type} `{ValueSig V}.

Lemma storeA_swap_lookup {K : Type} `{Countable K}
    (x y : K) (s : StoreA K) (z : K) :
  ((@storeA_swap V K _ _ x y s : gmap K V) !! swap x y z) =
  ((s : gmap K V) !! z).
Proof.
  unfold storeA_swap.
  change (kmap (M2:=gmap K) (swap x y) s !! swap x y z = s !! z).
  pose proof (swap_inj x y) as Hinj.
  rewrite (lookup_kmap (M1:=gmap K) (M2:=gmap K)
    (Inj0:=Hinj) (swap x y) s z).
  reflexivity.
Qed.

Lemma storeA_swap_lookup_inv {K : Type} `{Countable K}
    (x y : K) (s : StoreA K) (z : K) :
  ((@storeA_swap V K _ _ x y s : gmap K V) !! z) =
  ((s : gmap K V) !! swap x y z).
Proof.
  rewrite <- (swap_involutive x y z) at 1.
  apply storeA_swap_lookup.
Qed.

Lemma storeA_swap_dom {K : Type} `{Countable K}
    (x y : K) (s : StoreA K) :
  dom (@storeA_swap V K _ _ x y s : gmap K V) =
  set_swap x y (dom (s : gmap K V)).
Proof.
  unfold storeA_swap, set_swap.
  change (dom (kmap (M2:=gmap K) (swap x y) s) =
    set_map (swap x y) (dom s)).
  pose proof (swap_inj x y) as Hinj.
  rewrite (dom_kmap_L (M:=gmap K) (M2:=gmap K)
    (Inj0:=Hinj) (swap x y) s).
  reflexivity.
Qed.

Lemma storeA_swap_delete {K : Type} `{Countable K}
    (x y z : K) (s : StoreA K) :
   @storeA_swap V K _ _ x y (delete z s) =
  delete (swap x y z) (@storeA_swap V K _ _ x y s : gmap K V).
Proof.
  unfold storeA_swap.
  change (kmap (M2:=gmap K) (swap x y) (delete z (s : gmap K V)) =
    delete (swap x y z)
      (kmap (M2:=gmap K) (swap x y) (s : gmap K V))).
  refine (@kmap_delete K (gmap K) _ _ _ _ _ _ _ _ _
    K (gmap K) _ _ _ _ _ _ _ _ _
    (swap x y) _ V (s : gmap K V) z).
  apply swap_inj.
Qed.

Lemma storeA_swap_insert {K : Type} `{Countable K}
    (x y z : K) (v : V) (s : StoreA K) :
   @storeA_swap V K _ _ x y (<[z := v]> s) =
  <[swap x y z := v]> (@storeA_swap V K _ _ x y s : gmap K V).
Proof.
  unfold storeA_swap.
  change (kmap (swap x y) (<[z := v]> (s : gmap K V)) =
    (<[swap x y z := v]>
      (kmap (swap x y) (s : gmap K V)) : gmap K V)).
  refine (@kmap_insert K (gmap K) _ _ _ _ _ _ _ _ _
    K (gmap K) _ _ _ _ _ _ _ _ _
    (swap x y) _ V (s : gmap K V) z v).
  apply swap_inj.
Qed.

Lemma storeA_swap_union {K : Type} `{Countable K}
    (x y : K) (s1 s2 : StoreA K) :
   @storeA_swap V K _ _ x y (@union (gmap K V) _ s1 s2) =
  @union (gmap K V) _ (@storeA_swap V K _ _ x y s1 : gmap K V) (@storeA_swap V K _ _ x y s2 : gmap K V).
Proof.
  unfold storeA_swap.
  change (kmap (swap x y) (@union (gmap K V) _ (s1 : gmap K V) (s2 : gmap K V)) =
    @union (gmap K V) _
      (kmap (swap x y) (s1 : gmap K V))
      (kmap (swap x y) (s2 : gmap K V))).
  refine (@kmap_union K (gmap K) _ _ _ _ _ _ _ _ _
    K (gmap K) _ _ _ _ _ _ _ _ _
    (swap x y) _ V (s1 : gmap K V) (s2 : gmap K V)).
  apply swap_inj.
Qed.

Lemma storeA_swap_involutive {K : Type} `{Countable K}
    (x y : K) (s : StoreA K) :
   @storeA_swap V K _ _ x y (@storeA_swap V K _ _ x y s : StoreA K) = s.
Proof.
  apply storeA_map_eq. intros z.
  change (((@storeA_swap V K _ _ x y
    (@storeA_swap V K _ _ x y s) : gmap K V) !! z) =
    ((s : gmap K V) !! z)).
  rewrite storeA_swap_lookup_inv, storeA_swap_lookup_inv.
  better_base_solver.
Qed.

Lemma storeA_swap_sym {K : Type} `{Countable K}
    (x y : K) (s : StoreA K) :
   @storeA_swap V K _ _ x y s =  @storeA_swap V K _ _ y x s.
Proof.
  apply storeA_map_eq. intros z.
  change (((@storeA_swap V K _ _ x y s : gmap K V) !! z) =
    ((@storeA_swap V K _ _ y x s : gmap K V) !! z)).
  rewrite !storeA_swap_lookup_inv.
  rewrite swap_sym. reflexivity.
Qed.

Lemma storeA_swap_fresh {K : Type} `{Countable K}
    (x y : K) (s : StoreA K) :
  x ∉ dom (s : gmap K V) ->
  y ∉ dom (s : gmap K V) ->
   @storeA_swap V K _ _ x y s = s.
Proof.
  intros Hx Hy. apply storeA_map_eq. intros z.
  change (((@storeA_swap V K _ _ x y s : gmap K V) !! z) =
    ((s : gmap K V) !! z)).
  rewrite storeA_swap_lookup_inv.
  destruct (decide (z = x)) as [->|Hzx].
	  - base_swap_normalize.
	    change (((s : gmap K V) !! y) = ((s : gmap K V) !! x)).
    assert (Hsx : (s : gmap K V) !! x = None) by better_map_solver.
    assert (Hsy : (s : gmap K V) !! y = None) by better_map_solver.
    change (((s : gmap K V) !! x) = None) in Hsx.
    change (((s : gmap K V) !! y) = None) in Hsy.
    rewrite Hsx, Hsy.
    reflexivity.
	  - destruct (decide (z = y)) as [->|Hzy].
	    + base_swap_normalize.
	      change (((s : gmap K V) !! x) = ((s : gmap K V) !! y)).
      assert (Hsx : (s : gmap K V) !! x = None) by better_map_solver.
      assert (Hsy : (s : gmap K V) !! y = None) by better_map_solver.
      change (((s : gmap K V) !! x) = None) in Hsx.
      change (((s : gmap K V) !! y) = None) in Hsy.
      rewrite Hsx, Hsy.
      reflexivity.
	    + better_base_solver.
Qed.

Lemma storeA_swap_conjugate {K : Type} `{Countable K}
    (a b x y : K) (s : StoreA K) :
   @storeA_swap V K _ _ a b (@storeA_swap V K _ _ x y s : StoreA K) =
   @storeA_swap V K _ _ (swap a b x) (swap a b y)
    (@storeA_swap V K _ _ a b s : StoreA K).
Proof.
  apply storeA_map_eq. intros z.
  change (((@storeA_swap V K _ _ a b
    (@storeA_swap V K _ _ x y s) : gmap K V) !! z) =
    ((@storeA_swap V K _ _ (swap a b x) (swap a b y)
      (@storeA_swap V K _ _ a b s) : gmap K V) !! z)).
  rewrite !storeA_swap_lookup_inv.
  rewrite swap_conjugate_inv. reflexivity.
Qed.

Lemma storeA_swap_commute_fresh {K : Type} `{Countable K}
    (a b c d : K) (s : StoreA K) :
  c <> a ->
  c <> b ->
  d <> a ->
  d <> b ->
  @storeA_swap V K _ _ a b (@storeA_swap V K _ _ c d s : StoreA K) =
  @storeA_swap V K _ _ c d (@storeA_swap V K _ _ a b s : StoreA K).
Proof.
  intros Hca Hcb Hda Hdb.
  rewrite storeA_swap_conjugate.
  rewrite (swap_fresh a b c) by congruence.
  rewrite (swap_fresh a b d) by congruence.
  reflexivity.
Qed.

Lemma storeA_swap_conjugate_inv {K : Type} `{Countable K}
    (a b x y : K) (s : StoreA K) :
   @storeA_swap V K _ _ x y (@storeA_swap V K _ _ a b s : StoreA K) =
   @storeA_swap V K _ _ a b
    (@storeA_swap V K _ _ (swap a b x) (swap a b y) s : StoreA K).
Proof.
  apply storeA_map_eq. intros z.
  change (((@storeA_swap V K _ _ x y
    (@storeA_swap V K _ _ a b s) : gmap K V) !! z) =
    ((@storeA_swap V K _ _ a b
      (@storeA_swap V K _ _ (swap a b x) (swap a b y) s) :
      gmap K V) !! z)).
  rewrite !storeA_swap_lookup_inv.
  rewrite swap_conjugate. reflexivity.
Qed.

End AbstractStoreCore.

Section AbstractStoreCore.

Context {V : Type} `{ValueSig V}.

Lemma storeA_shift_lookup {K : Type} `{Countable K} `{!ShiftKey K}
    (k : nat) (s : StoreA K) (z : K) :
  ((storeA_shift k s : gmap K V) !! key_shift k z) =
  ((s : gmap K V) !! z).
Proof.
  unfold storeA_shift.
  apply storeA_rekey_lookup, key_shift_inj.
Qed.

Lemma storeA_shift_dom {K : Type} `{Countable K} `{!ShiftKey K}
    (k : nat) (s : StoreA K) :
  dom (storeA_shift k s : gmap K V) =
  set_map (key_shift k) (dom (s : gmap K V)).
Proof.
  unfold storeA_shift.
  apply storeA_rekey_dom, key_shift_inj.
Qed.

Lemma storeA_shift_empty {K : Type} `{Countable K} `{!ShiftKey K} k :
  storeA_shift k (∅ : StoreA K) = (∅ : gmap K V).
Proof.
  unfold storeA_shift.
  apply storeA_rekey_empty.
Qed.

Lemma storeA_shift_insert {K : Type} `{Countable K} `{!ShiftKey K}
    k z v (s : StoreA K) :
  storeA_shift k (<[z := v]> s) =
  <[key_shift k z := v]> (storeA_shift k s : gmap K V).
Proof.
  unfold storeA_shift.
  apply storeA_rekey_insert, key_shift_inj.
Qed.

Lemma storeA_shift_union {K : Type} `{Countable K} `{!ShiftKey K}
    k (s1 s2 : StoreA K) :
  storeA_shift k (@union (gmap K V) _ (s1 : gmap K V) (s2 : gmap K V)) =
  (storeA_shift k s1 : gmap K V) ∪ (storeA_shift k s2 : gmap K V).
Proof.
  unfold storeA_shift.
  apply storeA_rekey_union, key_shift_inj.
Qed.

End AbstractStoreCore.
