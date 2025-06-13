From stdpp Require Import base gmultiset gmap fin_maps ssreflect.

Notation "x ∉ Γ" := (Γ !! x = None).

(* Ported from https://coq.zulipchat.com/#narrow/channel/237977-Coq-users/topic/Proving.20Inversion.20of.20Fin.2Et/near/497910905 *)
Section existT_inj2_uip.
  Variables (A : Type) (P : A → Type).

  Implicit Type (x : A).

  Fact exist_inj2_helper x (px : P x) (y : sigT P) :
      @existT _ _ x px = y
    → ∃e : x = projT1 y, eq_rect x P px _ e = projT2 y.
  Proof. intros []; exists eq_refl; auto. Qed.

  Fact exists_inj2 x y (px : P x) (py : P y) :
      existT x px = existT y py
    → ∃e : x = y, eq_rect x P px _ e = py.
  Proof. intros (e & ?)%exist_inj2_helper. exists e; subst; simpl; auto. Qed.

  Fact exist_inj2_uip :
     (∀ x (e : x = x), e = eq_refl)
    → ∀ x (p1 p2 : P x), existT x p1 = existT x p2 → p1 = p2.
  Proof.
    intros UIP x p1 p2 (e & He)%exists_inj2.
    now rewrite (UIP _ e) in He.
  Qed.
End existT_inj2_uip.

Section SigmaCountable.
  Context {A} `{EqDecision A} `{Countable A}.
  Context (B : A -> Type) `{∀ x, EqDecision (B x)} `{∀ x, Countable (B x)}.
  Context `{EqDecision (sigT B)}.
  Global Program Instance sigma_countable_helper : Countable (sigT B) := {|
    encode xy := prod_encode (encode (projT1 xy)) (encode (projT2 xy));
    decode p :=
    x ← prod_decode_fst p ≫= decode;
    y ← prod_decode_snd p ≫= decode;
    Some (existT x y)
  |}.
  Next Obligation.
    intros [x y]; simpl.
    rewrite -> prod_decode_encode_fst, prod_decode_encode_snd; simpl.
    by repeat (rewrite decode_encode; simpl).
  Qed.
End SigmaCountable.

Definition rel_trivial {A B K} : K → A → B → Type := fun _ _ _ => True.

(* Forall2-definitions valued in Type rather than Prop *)
Section Forall2.
  (** Lifting a relation point-wise to option *)
  Inductive option_Forall2 {A B} (R: A → B → Type) : option A → option B → Type :=
    | Some_Forall2 x y : R x y → option_Forall2 R (Some x) (Some y)
    | None_Forall2 : option_Forall2 R None None.

  Global Hint Mode MapFold - - ! : typeclass_instances.
  Global Hint Mode MapFold ! - - : typeclass_instances.

  Definition gmap_Forall2 `{∀ A, Lookup K A (M A)} {A B}
      (R : K → A → B → Type) (m1 : M A) (m2 : M B) : Type :=
    ∀ i, option_Forall2 (R i) (m1 !! i) (m2 !! i).

  Section gmap_Forall2.
    (* Erm is there an easier way to do this? *)
    Context {K A B} (R : K → A → B → Type).
    Context `{Countable K}.
    Definition M := gmap K.

    Lemma gmap_Forall2_impl (R' : K → A → B → Type) (m1 : M A) (m2 : M B) :
      gmap_Forall2 R m1 m2 →
      (∀ i x1 x2, R i x1 x2 → R' i x1 x2) →
      gmap_Forall2 R' m1 m2.
    Proof. intros Hm ? i. destruct (Hm i); constructor; eauto. Qed.
  
    Lemma gmap_Forall2_fmap_r (m1 : M A) (m2 : M B)
      {B'} `{EqDecision B'} `{Countable B'} (R' : K → A → B' → Type) (f : B -> B') :
      gmap_Forall2 R m1 m2 →
      (∀ i x1 x2, R i x1 x2 → R' i x1 (f x2)) →
      gmap_Forall2 R' m1 (f <$> m2).
    Proof. intros Hm ? i. rewrite lookup_fmap. destruct (Hm i); constructor; eauto. Qed.

    Lemma gmap_Forall2_fmap_l (m1 : M A) (m2 : M B)
      {A'} `{EqDecision A'} `{Countable A'} (R' : K → A' → B → Type) (f : A -> A') :
      gmap_Forall2 R m1 m2 →
      (∀ i x1 x2, R i x1 x2 → R' i (f x1) x2) →
      gmap_Forall2 R' (f <$> m1) m2.
    Proof. intros Hm ? i. rewrite lookup_fmap. destruct (Hm i); constructor; eauto. Qed.

    Lemma gmap_Forall2_empty : gmap_Forall2 R (∅ : M A) ∅.
    Proof. intros i. rewrite !lookup_empty. constructor. Qed.
    Lemma gmap_Forall2_empty_inv_l (m2 : M B) : gmap_Forall2 R ∅ m2 → m2 = ∅.
    Proof.
      intros Hm. apply map_eq; intros i. rewrite -> lookup_empty, eq_None_not_Some.
      intros [x Hi]. specialize (Hm i). rewrite -> lookup_empty, Hi in Hm. inv Hm.
    Qed.
    Lemma gmap_Forall2_empty_inv_r (m1 : M A) : gmap_Forall2 R m1 ∅ → m1 = ∅.
    Proof.
      intros Hm. apply map_eq; intros i. rewrite -> lookup_empty, eq_None_not_Some.
      intros [x Hi]. specialize (Hm i). rewrite -> lookup_empty, Hi in Hm. inv Hm.
    Qed.
  
    Lemma gmap_Forall2_delete (m1 : M A) (m2 : M B) i :
      gmap_Forall2 R m1 m2 → gmap_Forall2 R (delete i m1) (delete i m2).
    Proof.
      intros Hm j. destruct (decide (i = j)) as [->|].
      - rewrite !lookup_delete. constructor.
      - by rewrite -> !lookup_delete_ne by done.
    Qed.
  
    Lemma gmap_Forall2_insert_2 {m1 : M A} {m2 : M B} {i} {x1} {x2} :
      R i x1 x2 → gmap_Forall2 R m1 m2 → gmap_Forall2 R (<[i:=x1]> m1) (<[i:=x2]> m2).
    Proof.
      intros Hx Hm j. destruct (decide (i = j)) as [->|].
      - rewrite !lookup_insert. by constructor.
      - by rewrite -> !lookup_insert_ne by done.
    Qed.

    Definition gIFF (P Q : Type) : Type := (P → Q) * (Q → P).

    Definition gIFF_compose (P1 P2 P3 : Type) : gIFF P1 P2 → gIFF P2 P3 → gIFF P1 P3.
    Proof. firstorder. Qed.

    Lemma gmap_Forall2_insert {m1 : M A} {m2 : M B} {i} x1 x2 :
      m1 !! i = None → m2 !! i = None →
      gIFF (gmap_Forall2 R (<[i:=x1]> m1) (<[i:=x2]> m2)) (R i x1 x2 * gmap_Forall2 R m1 m2).
    Proof.
      intros Hi1 Hi2. split. 2: intros []; by eapply gmap_Forall2_insert_2. 
      intros Hm. split.
      - specialize (Hm i). rewrite !lookup_insert in Hm. by inv Hm.
      - intros j. destruct (decide (i = j)) as [->|].
        + rewrite Hi1 Hi2. constructor.
        + specialize (Hm j). by rewrite -> !lookup_insert_ne in Hm by done.
    Qed.

    Lemma gmap_Forall2_insert_inv_l {m1 : M A} {m2 : M B} i x1 :
      m1 !! i = None →
      gmap_Forall2 R (<[i:=x1]> m1) m2 →
      { x2 & { m2' & (m2 = <[i:=x2]> m2') * (m2' !! i = None) * R i x1 x2 * gmap_Forall2 R m1 m2' : Type }}.
    Proof.
      intros ? Hm. pose proof (Hm i) as Hi. rewrite lookup_insert in Hi.
      destruct (m2 !! i) as [x2|] eqn:?; inv Hi.
      exists x2, (delete i m2). repeat constructor.
      - by rewrite insert_delete.
      - by rewrite lookup_delete.
      - done.
      - rewrite <-(delete_insert m1 i x1) by done. by apply gmap_Forall2_delete.
    Qed.

    Lemma gmap_Forall2_insert_inv_r {m1 : M A} {m2 : M B} i x2 :
      m2 !! i = None →
      gmap_Forall2 R m1 (<[i:=x2]> m2) →
      { x1 & { m1' & (m1 = <[i:=x1]> m1') * (m1' !! i = None) * R i x1 x2 * gmap_Forall2 R m1' m2 : Type }}.
    Proof.
      intros ? Hm. pose proof (Hm i) as Hi. rewrite lookup_insert in Hi.
      destruct (m1 !! i) as [x1|] eqn:?; inv Hi.
      exists x1, (delete i m1). repeat constructor.
      - by rewrite insert_delete.
      - by rewrite lookup_delete.
      - done.
      - rewrite <-(delete_insert m2 i x2) by done. by apply gmap_Forall2_delete.
    Qed.

    Local Definition filter_out (m1 : M A) (m2 : list (K * B)) : M A.
      induction m2.
      - exact m1.
      - exact (delete a.1 IHm2).
    Defined.

    Local Lemma delete_filter_out k a m1 m2 : k ∉ m1 → k ∉ (list_to_map m2 : M B) →
      delete k (filter_out (<[k := a]> m1) m2) = delete k (filter_out m1 m2).
    Proof.
      intros Hk. induction m2; simpl.
      - rewrite delete_insert; [|done]. by rewrite delete_notin.
      - destruct a0 as [k' v]. simpl. intros Hk'.
        eapply lookup_insert_None in Hk'. destruct Hk'.
        rewrite delete_commute. rewrite IHm2; [|done]. by rewrite delete_commute.
    Qed.

    Local Lemma filter_out_notin m2 i m1 : i ∉ m2 ->
      filter_out m1 (map_to_list m2) !! i = m1 !! i.
    Proof.
      intros Hi. induction m2 using map_first_key_ind.
      - by rewrite map_to_list_empty.
      - rewrite map_to_list_insert_first_key. 2, 3: done. simpl.
        eapply lookup_insert_None in Hi. destruct Hi.
        rewrite lookup_delete_ne. 1: eapply IHm2. all: done.
    Qed.

    Local Lemma filter_notin_out m1 m2 i : i ∉ m1 ->
      filter_out m1 m2 !! i = None.
    Proof.
      induction m2; [done|]. intro Hi. simpl. rewrite lookup_delete_None.
      right. by apply IHm2.
    Qed.

    Local Lemma filter_out_in m1 m2 i x : (i, x) ∈ m2 ->
      filter_out m1 m2 !! i = None.
    Proof.
      intros Hi. induction m2.
      - inversion Hi.
      - inversion Hi; simpl.
        1: by rewrite lookup_delete.
        destruct a. simpl. destruct (decide (i = k)); simplify_eq.
        + by rewrite lookup_delete.
        + rewrite lookup_delete_ne; [|done]. by eapply IHm2.
    Qed.

    Lemma gmap_Forall2_filter_r' {m1 : M A} {m2 : M B} {m2' : list (K * B)} :
      m2 ##ₘ list_to_map m2' → NoDup (m2'.*1) →
      gmap_Forall2 R m1 (m2 ∪ list_to_map m2') →
      gmap_Forall2 R (filter_out m1 m2') m2.
    Proof.
      intros Hm2 Hm Hdup. unfold filter_out.
      revert m2 m1 Hdup Hm Hm2. induction m2'; simpl; simplify_eq.
      - intros m2 m1 Hm _ _. by rewrite map_union_empty in Hm.
      - destruct a. simpl. intros m2 m1 Hm Hdup Hm2. eapply map_disjoint_insert_r in Hm2.
        destruct Hm2 as [Hk Hdisj]. replace m2 with (delete k m2).
        2: by rewrite delete_notin.
        rewrite -insert_union_r in Hm; [|done].
        assert (NoDup m2'.*1) as Hdup' by (inversion Hdup; done).
        assert (k ∉ (list_to_map m2' : gmap K B)) as Hk'.
        1: eapply not_elem_of_list_to_map_1. by inversion Hdup.
        eapply gmap_Forall2_insert_inv_r in Hm.
        2: by eapply lookup_union_None_2.
        destruct Hm as (a' & m1' & (((-> & Hkm1') & HRk) & Hm)).
        rewrite delete_filter_out; [|done|done]. eapply gmap_Forall2_delete.
        by eapply IHm2'.
    Qed.

    Lemma gmap_Forall2_filter_r {m1 : M A} {m2 m2' : M B} :
      m2 ##ₘ m2' →
      gmap_Forall2 R m1 (m2 ∪ m2') →
      gmap_Forall2 R (filter_out m1 (map_to_list m2')) m2.
    Proof.
      intros Hdisj HR. eapply gmap_Forall2_filter_r'.
      1, 3: rewrite list_to_map_to_list.
      1, 2: done.
      eapply NoDup_fst_map_to_list.
    Qed.

    Lemma gmap_Forall2_union_inv_r {m1_ : M A} {m2 m2' : M B} :
      m2 ##ₘ m2' → gmap_Forall2 R m1_ (m2 ∪ m2') →
      { m1 & { m1' & (m1_ = m1 ∪ m1') * gmap_Forall2 R m1 m2 * gmap_Forall2 R m1' m2' : Type } }.
    Proof.
      intros Hdisj Hm. eexists. eexists. repeat split.
      2, 3: eapply gmap_Forall2_filter_r; [done|].
      3: rewrite map_union_comm. 2, 3: done. 2: done.
      eapply map_eq. intros i. rewrite lookup_union.
      specialize (Hm i). rewrite lookup_union in Hm.
      destruct (m2 !! i) eqn: Hm2.
      - pose proof Hm2 as Hm2'. eapply elem_of_map_to_list in Hm2'.
        rewrite union_Some_l in Hm. inversion Hm.
        assert (i ∉ m2') as Hn. 1: by eapply map_disjoint_Some_l.
        rewrite filter_out_notin; [|done]. rewrite <- H1.
        by rewrite union_Some_l.
      - rewrite left_id in Hm.
        destruct (m2' !! i) eqn: Hm2'.
        + pose proof Hm2' as Hm2''. eapply elem_of_map_to_list in Hm2''.
          inversion Hm. rewrite (filter_out_notin m2); [|done]. rewrite <- H1.
          eapply (filter_out_in m1_) in Hm2''. by rewrite Hm2''.
        + inversion Hm. rewrite filter_out_notin; [|done]. rewrite <- H1.
          rewrite left_id. by rewrite filter_notin_out.
    Qed.

    Lemma gmap_Forall2_disjoint {m1 m1' : M A} {m2 m2' : M B} :
      m2 ##ₘ m2' → gmap_Forall2 R m1 m2 → gmap_Forall2 R m1' m2' →
      m1 ##ₘ m1'.
    Proof.
      intros Hdisj HR HR'. eapply map_disjoint_spec. intros.
      specialize (HR i). specialize (HR' i). rewrite H0 in HR. rewrite H1 in HR'.
      inversion HR. inversion HR'. eapply map_disjoint_spec. all: done.
    Qed.

    Lemma gmap_Forall2_singleton i x1 x2 :
      gIFF (gmap_Forall2 R ({[ i := x1 ]} : M A) {[ i := x2 ]}) (R i x1 x2).
    Proof.
      rewrite <-!insert_empty. eapply gIFF_compose. 1: eapply gmap_Forall2_insert; done.
      constructor. 1: by intros []. intros. constructor. 1: done. eapply gmap_Forall2_empty.
    Qed.

    Lemma gmap_Forall2_singleton_inv_l i x1 m2 :
      gmap_Forall2 R ({[ i := x1 ]} : M A) m2 →
      { x2 &  (m2 = {[ i := x2 ]}) * R i x1 x2 : Type }.
    Proof.
      intros HR. eapply gmap_Forall2_insert_inv_l in HR.
      destruct HR as (x2 & m2' & (((-> & Hm2') & HRi) & HR)).
      eexists. eapply gmap_Forall2_empty_inv_l in HR. rewrite HR.
      all: done.
    Qed.

    Lemma gmap_Forall2_singleton_inv_r i x2 m1 :
      gmap_Forall2 R m1 ({[ i := x2 ]} : M B) →
      { x1 & (m1 = {[ i := x1 ]}) * R i x1 x2 : Type }.
    Proof.
      intros HR. eapply gmap_Forall2_insert_inv_r in HR.
      destruct HR as (x1 & m1' & (((-> & Hm1') & HRi) & HR)).
      eexists. eapply gmap_Forall2_empty_inv_r in HR. rewrite HR.
      all: done.
    Qed.

    Lemma gmap_Forall2_lookup_None {m1 : M A} {m2 : M B} {i} :
      gmap_Forall2 R m1 m2 -> i ∉ m1 <-> i ∉ m2.
    Proof. intros Hm. split; intros Hi. all: by destruct (Hm i). Qed.
  End gmap_Forall2.
End Forall2.

Section codom.
  Context `{Countable K, Countable V}.

  Definition codom (m : gmap K (gmultiset V)) : gmultiset V := map_fold (fun _ a b => a ⊎ b) ∅ m.

  (* Ported from Alexandre's proof *)
  Lemma codom_insert (m : gmap K (gmultiset V)) (k : K) (ms : gmultiset V) :
    k ∉ m -> codom (<[k := ms]> m) = ms ⊎ codom m.
  Proof.
    intros. apply (map_fold_insert_L (fun _ a b => a ⊎ b)). 2: done. intros. multiset_solver.
  Qed.

  Lemma codom_empty : codom ∅ = ∅.
  Proof. apply map_fold_empty. Qed.

  Lemma codom_singleton k ms : codom {[ k := ms ]} = ms.
  Proof. unfold codom. rewrite map_fold_singleton. multiset_solver. Qed.

  Lemma codom_union m1 m2 :
    m1 ##ₘ m2 -> codom (m1 ∪ m2) = codom m1 ⊎ codom m2.
  Proof.
    revert m2.
    induction m1 using map_first_key_ind; intros m2 Hdisj.
    - rewrite -> codom_empty, left_id_L. multiset_solver. apply map_empty_union.
    - apply map_disjoint_insert_l in Hdisj. destruct Hdisj.
      rewrite <- insert_union_l, codom_insert, codom_insert. 3: by rewrite lookup_union_r.
      by rewrite -> IHm1, (assoc_L (⊎)). done.
  Qed.
End codom.
