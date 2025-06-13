From Coq.Logic Require Import Eqdep_dec.
From stdpp Require Import base tactics gmap gmultiset option fin_maps ssreflect.
From ST Require Import stdsharp syntax syntax_instances.
From Coq.Program Require Import Equality.

(* Process languages *)
Structure ProcLang := mkProgLang {
  NObj : Type;
  NObj_eq_dec : EqDecision NObj;
  NObj_countable : Countable NObj;
  stepObj : sym * NObj -> Action -> gmultiset (AtomicObj NObj) -> Prop;
}.

Section subst.
  Context (σ : substObj).

  Definition lookup (t : varOrSym) : option sym.
    destruct t.
    - destruct (σ !! v).
      + exact (Some s).
      + exact None.
    - exact None.
  Defined.    

  Definition substVar (t : varOrSym) : varOrSym.
    destruct (lookup t).
    - exact (Sym s).
    - exact t.
  Defined.
End subst.

Fixpoint substTerm (σ : substObj) (P : term) : term :=
  match P with
  | fwd src => fwd (substVar σ src)
  | cut P1 P2 x A => cut (substTerm σ P1) (substTerm (delete x σ) P2) x A
  | send_1 => send_1
  | recv_1 x P => recv_1 x (substTerm (delete x σ) P)
  | recv_lolli y P => recv_lolli y (substTerm (delete y σ) P)
  | send_lolli x y P => send_lolli (substVar σ x) (substVar σ y) (substTerm σ P)
  | send_tensor y P => send_tensor (substVar σ y) (substTerm σ P)
  | recv_tensor x y P => recv_tensor (substVar σ x) y (substTerm (delete y σ) P)
  | recv_with P1 P2 => recv_with (substTerm σ P1) (substTerm σ P2)
  | send_with x sel P => send_with (substVar σ x) sel (substTerm σ P)
  | send_plus sel P => send_plus sel (substTerm σ P)
  | recv_plus x P1 P2 => recv_plus (substVar σ x) (substTerm σ P1) (substTerm σ P2)
  end.

Lemma substVar_insert_ne {σ : substObj} x y a : x ≠ y -> substVar (<[x := a]> σ) (Var y) = substVar σ (Var y).
Proof. intros. unfold substVar, lookup. by rewrite lookup_insert_ne. Qed.

Lemma substVar_notin {σ : substObj} y : y ∉ σ -> substVar σ (Var y) = Var y.
Proof. unfold substVar, lookup. by intros ->. Qed.

Lemma substVar_insert_eq {σ : substObj} x a : substVar (<[x := a]> σ) (Var x) = Sym a.
Proof. intros. unfold substVar, lookup. by rewrite lookup_insert. Qed.

Lemma substVar_insert_None {σ : substObj} x a : substVar (<[x := a]> σ) (Var x) = Sym a.
Proof. unfold substVar, lookup. by rewrite lookup_insert. Qed. 

Lemma substVar_empty a : substVar ∅ a = a.
Proof. unfold substVar, lookup. destruct a; [|done]. by rewrite lookup_empty. Qed.

Lemma substVar_insert v a σ x : v ∉ σ -> substVar (<[v:=a]> σ) x = substVar {[v := a]} (substVar σ x).
Proof.
  intros H. unfold substVar, lookup. destruct x; [|done]. destruct (σ !! v0) eqn: P.
  - rewrite lookup_insert_ne. 2: eapply (lookup_ne σ); by rewrite H P. by rewrite P.
  - destruct (decide (v = v0)); simplify_eq.
    + by rewrite lookup_insert lookup_singleton.
    + rewrite lookup_insert_ne; [|done]. rewrite lookup_singleton_ne; [|done]. by rewrite P.
Qed.

Lemma substVar_union_inv_r σ1 σ2 x : σ1 ##ₘ σ2 -> (∃ t, σ1 !! x = Some t) ->
  substVar (σ1 ∪ σ2) (Var x) = substVar σ1 (Var x).
Proof.
  intros Hdisj (t & Ht). induction σ2 using map_first_key_ind.
  - by rewrite map_union_empty.
  - destruct (decide (i = x)); simplify_eq.
    + exfalso. eapply map_disjoint_spec. 1, 2: done.
      eapply lookup_insert.
    + rewrite <- insert_union_r. 2: eapply map_disjoint_insert_l; by symmetry.
      rewrite substVar_insert_ne; [|done]. rewrite IHσ2. done.
      by eapply map_disjoint_insert_r.
Qed.

Lemma subst_empty P : substTerm ∅ P = P.
Proof. induction P; simpl; f_equal; eauto using substVar_empty. Qed.

Ltac subst_delete_insert_solver v x IH := destruct (decide (v = x)); simplify_eq;
  [ repeat (rewrite delete_insert; [|done]); rewrite delete_notin; [|done]; by rewrite subst_empty
  | repeat (rewrite delete_insert_ne; [|done]); rewrite delete_empty;
    rewrite IH; [done|by rewrite lookup_delete_ne] ].

(* See Lemma substitution x a P γ *)
Lemma subst_insert v a σ P : v ∉ σ ->
  substTerm (<[v := a]> σ) P = substTerm {[v := a]} (substTerm σ P).
Proof.
  revert σ. induction P; simpl; intros σ Hv.
  - f_equal. destruct src; [|done]. destruct (decide (v = v0)); simplify_eq.
    + rewrite substVar_insert_eq. rewrite substVar_notin; [|done]. by rewrite substVar_insert_eq.
    + rewrite substVar_insert_ne. 2: done. unfold substVar, lookup.
      destruct (σ !! v0); [done|]. by rewrite lookup_singleton_ne.
  - rewrite IHP1; [|done]. f_equal. subst_delete_insert_solver v x IHP2. 
  - done.
  - subst_delete_insert_solver v x IHP.
  - f_equal. subst_delete_insert_solver v y IHP.
  - f_equal. 3: by eapply IHP. all: by eapply substVar_insert.
  - f_equal; [by eapply substVar_insert|by eapply IHP].
  - f_equal; [by eapply substVar_insert|subst_delete_insert_solver v y IHP].
  - rewrite IHP1; [|done]. by rewrite IHP2; [|done].
  - f_equal; [by eapply substVar_insert|by eapply IHP].
  - f_equal. by eapply IHP.
  - rewrite IHP1; [|done]. rewrite IHP2; [|done]. f_equal. by eapply substVar_insert.
Qed.

Ltac subst_delete_delete_solver v x σ σ' IH := destruct (decide (v = x)); simplify_eq;
  [ by do 2 (rewrite delete_idemp)
  | rewrite (delete_commute σ); rewrite (delete_commute σ'); by eapply IH ].

Ltac subst_lookup_simple_solver v v0 := destruct (decide (v = v0)); simplify_eq;
  [ by do 2 (rewrite lookup_delete)
  | do 2 (rewrite lookup_delete_ne; [|done]); by f_equal ].

Ltac injection_and_clear HP := injection HP; clear HP; intros.

Lemma subst_delete v σ σ' P : substTerm σ P = substTerm σ' P ->
  substTerm (delete v σ) P = substTerm (delete v σ') P.
Proof.
  revert σ σ'. induction P; simpl; intros σ σ' HP; simpl in HP; unfold substVar, lookup in *.
  - destruct src; [|done]. subst_lookup_simple_solver v v0.
  - injection_and_clear HP. rewrite (IHP1 σ σ'); [|done]. f_equal.
    subst_delete_delete_solver v x σ σ' IHP2.
  - done.
  - f_equal. subst_delete_delete_solver v x σ σ' IHP.
  - f_equal. subst_delete_delete_solver v y σ σ' IHP.
  - injection_and_clear HP. rewrite (IHP _ _ H).
    destruct x; [|f_equal]; (destruct y; [|f_equal]).
    2, 3: by subst_lookup_simple_solver v v0.
    destruct (decide (v = v1)); destruct (decide (v = v0)); simplify_eq.
    all: try (repeat (rewrite lookup_delete)). 1: done.
    all: try (repeat (rewrite lookup_delete_ne; [|done])); by f_equal.
  - injection_and_clear HP. f_equal. 2: by eapply IHP.
    destruct y; [|done]. subst_lookup_simple_solver v v0.
  - injection_and_clear HP. destruct x. all: f_equal.
    2, 3: rewrite (delete_commute σ); rewrite (delete_commute σ'); by eapply IHP.
    by subst_lookup_simple_solver v v0.
  - injection_and_clear HP. by f_equal; [eapply IHP1|eapply IHP2].
  - injection_and_clear HP. f_equal. 2: by eapply IHP.
    destruct x; [|done]. subst_lookup_simple_solver v v0.
  - injection_and_clear HP. f_equal. by eapply IHP.
  - injection_and_clear HP. f_equal.
    + destruct x; [|done]. subst_lookup_simple_solver v v0.
    + by apply IHP1.
    + by apply IHP2.
Qed.

Lemma subst_union_inv_r P σ1' σ1 σ2 : σ1 ##ₘ σ2 -> σ1' ##ₘ σ2 ->
  substTerm σ1' P = substTerm σ1 P ->
  substTerm (σ1' ∪ σ2) P = substTerm (σ1 ∪ σ2) P.
Proof.
  intros Hdisj Hdisj' H.
  induction σ2 using map_first_key_ind.
  - by do 2 (rewrite map_union_empty).
  - eapply map_disjoint_insert_r in Hdisj, Hdisj'.
    destruct Hdisj. destruct Hdisj'.
    do 2 (rewrite <- insert_union_r; [|done]).
    rewrite subst_insert. rewrite IHσ2; [|done|done]. rewrite <- subst_insert; [done|].
    all: by rewrite lookup_union_None.
Qed.

Lemma subst_union_inv_l P σ1 σ2 σ2' :
  substTerm σ2' P = substTerm σ2 P -> σ1 ##ₘ σ2 -> σ1 ##ₘ σ2' ->
  substTerm (σ1 ∪ σ2') P = substTerm (σ1 ∪ σ2) P.
Proof.
  intros. rewrite map_union_comm. rewrite (map_union_comm σ1).
  eapply subst_union_inv_r. all: done.
Qed.

Lemma subst_discard_n P Γ σ σ' A : σ ##ₘ σ' -> typed_term Γ P A ->
  gmap_Forall2 rel_trivial σ Γ ->
  substTerm (σ ∪ σ') P = substTerm σ P.
Proof.
  intros Hdisj HP Hσ. revert σ σ' Hdisj Hσ. induction HP; simpl; intros σ σ' Hdisj Hσ.
  - f_equal. eapply gmap_Forall2_singleton_inv_r in Hσ. destruct Hσ as (a & -> & _).
    rewrite map_union_comm; [|done]. rewrite <- insert_union_singleton_r.
    2: by eapply map_disjoint_singleton_l. by rewrite !substVar_insert_eq.
  - eapply gmap_Forall2_union_inv_r in Hσ; [|done].
    destruct Hσ as (σ1 & σ2 & ((-> & Hσ1) & Hσ2)).
    eapply map_disjoint_union_l in Hdisj. destruct Hdisj as (Hdisj & Hdisj').
    assert (σ1 ##ₘ σ2) as Hdisj1 by by eapply gmap_Forall2_disjoint; [exact H|exact Hσ1|exact Hσ2].
    f_equal.
    + rewrite <- map_union_assoc. rewrite (map_union_comm σ2 σ'); [|done].
      rewrite map_union_assoc. eapply subst_union_inv_r. 2: eapply map_disjoint_union_l; split; [|done].
      1, 2: done. by eapply IHHP1.
    + rewrite (map_union_comm σ1 σ2); [|done].
      replace (σ2 ∪ σ1 ∪ σ') with (σ2 ∪ σ' ∪ σ1).
      2: rewrite <- !map_union_assoc; f_equal; by eapply map_union_comm.
      rewrite !delete_union. eapply subst_union_inv_r.
      1, 2: eapply map_disjoint_delete_r. 2: eapply map_disjoint_union_l; split.
      1, 2, 3: by eapply map_disjoint_delete_l.
      replace (delete x σ2) with (delete x (<[x := 42]> σ2)) by by rewrite delete_insert_delete.
      replace (delete x σ') with (delete x (delete x σ')) by by eapply delete_idemp.
      rewrite <- delete_union. eapply subst_delete.
      eapply IHHP2. 2: by eapply gmap_Forall2_insert_2.
      rewrite map_disjoint_insert_l; split.
      eapply lookup_delete. by eapply map_disjoint_delete_r.
  - done.
  - f_equal. eapply gmap_Forall2_insert_inv_r in Hσ; [|done].
    destruct Hσ as (a' & σ'' & ((-> & Hx) & _) & Hσ).
    rewrite delete_union delete_insert; [|done].
    eapply map_disjoint_insert_l in Hdisj. destruct Hdisj.
    rewrite delete_notin; [|done]. by eapply IHHP.
  - f_equal. replace (delete y (σ ∪ σ')) with (delete y ((<[y := 42]> σ) ∪ delete y σ')).
    2: do 2 (rewrite delete_union); rewrite delete_idemp; by rewrite delete_insert_delete.
    replace (delete y σ) with (delete y (<[y := 42]> σ)).
    2: by rewrite delete_insert_delete.
    eapply subst_delete. eapply IHHP. 2: by eapply gmap_Forall2_insert_2.
    rewrite map_disjoint_insert_l; split.
    by eapply lookup_delete. by eapply map_disjoint_delete_r.
  - eapply gmap_Forall2_insert_inv_r in Hσ. 2: by rewrite lookup_insert_ne.
    destruct Hσ as (a' & σ'' & ((-> & Hx) & _) & Hσ).
    eapply gmap_Forall2_insert_inv_r in Hσ; [|done].
    destruct Hσ as (a'' & σ''' & ((-> & Hx') & _) & Hσ').
    eapply map_disjoint_insert_l in Hdisj. destruct Hdisj as (Hxσ' & Hdisj).
    eapply map_disjoint_insert_l in Hdisj. destruct Hdisj as (Hyσ' & Hdisj).
    f_equal. 1, 2: eapply substVar_union_inv_r.
    1, 3: eapply map_disjoint_insert_l; split; [done|by eapply map_disjoint_insert_l].
    eexists. eapply lookup_insert. eexists. rewrite lookup_insert_ne; [|done]. eapply lookup_insert.
    rewrite insert_commute; [|done]. rewrite <- insert_union_l.
    rewrite -> (subst_insert y). 2: eapply lookup_union_None; split; [|done].
    rewrite -> (subst_insert y). 2, 3: by rewrite lookup_insert_ne. f_equal.
    eapply IHHP. eapply map_disjoint_insert_l; by split.
    by eapply gmap_Forall2_insert_2.
  - eapply gmap_Forall2_insert_inv_r in Hσ; [|done].
    destruct Hσ as (a' & σ'' & ((-> & Hx) & _) & Hσ).
    f_equal.
    + eapply substVar_union_inv_r; [done|]. eexists. eapply lookup_insert.
    + rewrite <- insert_union_l. rewrite -> (subst_insert y). rewrite -> (subst_insert y).
      f_equal. eapply IHHP. 4: eapply lookup_union_None; split.
      1, 5: by eapply map_disjoint_insert_l.
      all: done.
  - eapply gmap_Forall2_insert_inv_r in Hσ; [|done].
    destruct Hσ as (a' & σ'' & ((-> & Hx) & _) & Hσ).
    f_equal. eapply substVar_union_inv_r; [done|]. eexists. eapply lookup_insert.
    rewrite <- insert_union_l.
    set U1 := <[x:=a']> (σ'' ∪ σ').
    set U2 := <[x:=a']> σ''.
    replace (delete y U1) with (delete y (<[y:=a']> (delete y U1))).
    2: rewrite delete_insert; [done|eapply lookup_delete].
    replace (delete y U2) with (delete y (<[y:=a']> (delete y U2))).
    2: rewrite delete_insert; [done|eapply lookup_delete].
    eapply subst_delete. unfold U1. rewrite delete_insert_ne; [|done].
    rewrite delete_union. do 2 (rewrite insert_union_l).
    rewrite <- delete_insert_ne; [|done].
    eapply IHHP. all: unfold U2. 1: eapply map_disjoint_insert_l; split.
    by eapply lookup_delete.
    by eapply map_disjoint_delete_r, map_disjoint_delete_l.
    eapply gmap_Forall2_insert_2; [done|]. rewrite delete_insert_ne; [|done].
    rewrite delete_notin. 2: by eapply gmap_Forall2_lookup_None.
    by eapply gmap_Forall2_insert_2.
  - rewrite IHHP1. rewrite IHHP2. all: done.
  - eapply gmap_Forall2_insert_inv_r in Hσ; [|done].
    destruct Hσ as (a' & σ'' & ((-> & Hx) & _) & Hσ). f_equal.
    + eapply substVar_union_inv_r; [done|]. eexists. eapply lookup_insert.
    + eapply IHHP; [done|]. by eapply gmap_Forall2_insert_2.
  - f_equal. by eapply IHHP.
  - eapply gmap_Forall2_insert_inv_r in Hσ; [|done].
    destruct Hσ as (a' & σ'' & ((-> & Hx) & _) & Hσ).
    f_equal. eapply substVar_union_inv_r; [done|]. eexists. eapply lookup_insert.
    2: eapply IHHP2. 1: eapply IHHP1. 2, 4: eapply gmap_Forall2_insert_2. all: done.
Qed.

Lemma subst_discard_1 v a P Γ σ A : typed_term Γ P A -> v ∉ Γ ->
  gmap_Forall2 rel_trivial σ Γ ->
  substTerm (<[v := a]> σ) P = substTerm σ P.
Proof.
  intros HP Hv HR. rewrite insert_union_singleton_r.
  eapply subst_discard_n. 2, 3: done.
  eapply map_disjoint_singleton_r. all: by eapply gmap_Forall2_lookup_None.
Qed.

Inductive term_step : sym * term -> Action -> gmultiset (AtomicObj term) -> Prop :=
| step_fwd : ∀ a b, term_step (a, fwd (Sym b)) ∅ {[+ fwd[ a ](b) +]}
(* say something about the freshness of b' *)
| step_cut : ∀ a x P1 P2 A b', term_step (a, cut P1 P2 x A) ∅ {[+ proc[ a ](substTerm {[x := b']} P2); proc[ b' ](P1) +]}
| step_send1 : ∀ a, term_step (a, send_1) (a ! ∅) ∅
| step_recv1 : ∀ a b x P, term_step (a, recv_1 x P) (b ? ∅) {[+ proc[ a ](P) +]}
| step_recv_lolli : ∀ a b x P, term_step (a, recv_lolli x P) (a ? Payload_sym b) {[+ proc[ a ](substTerm {[x := b]} P) +]}
| step_send_lolli : ∀ a b c P, term_step (c, send_lolli (Sym b) (Sym a) P) (b ! Payload_sym a) {[+ proc[c](P) +]}
| step_send_tensor : ∀ a b P, term_step (a, send_tensor (Sym b) P) (a ! Payload_sym b) {[+ proc[a](P) +]}
| step_recv_tensor : ∀ a b c x P, term_step (c, recv_tensor (Sym b) x P) (b ? Payload_sym a) {[+ proc[c](substTerm {[x := a]} P) +]}
| step_recv_with1 : ∀ a P1 P2, term_step (a, recv_with P1 P2) (a ? π1) {[+ proc[ a ](P1) +]}
| step_recv_with2 : ∀ a P1 P2, term_step (a, recv_with P1 P2) (a ? π2) {[+ proc[ a ](P2) +]}
| step_send_with : ∀ a b sel P, term_step (a, send_with (Sym b) sel P) (b ! Payload_choice sel) {[+ proc[ a ](P) +]}
| step_send_plus : ∀ a sel P, term_step (a, send_plus sel P) (a ! Payload_choice sel) {[+ proc[ a ](P) +]}
| step_recv_plus1 : ∀ a b P1 P2, term_step (a, recv_plus (Sym b) P1 P2) (b ? π1) {[+ proc[ a ](P1) +]}
| step_recv_plus2 : ∀ a b P1 P2, term_step (a, recv_plus (Sym b) P1 P2) (b ? π2) {[+ proc[ a ](P2) +]}. 

Definition SessionTypes : ProcLang.
Proof. by eapply mkProgLang, term_step. Defined. 

Inductive flipbit_step : sym * flipbit_type -> Action -> gmultiset (AtomicObj flipbit_type) -> Prop :=
| step_flipbit_recv1 : ∀ a, flipbit_step (a, TToRecv) (a ? π1) {[+ proc[ a ](TRecved1) +]}
| step_flipbit_recv2 : ∀ a, flipbit_step (a, TToRecv) (a ? π2) {[+ proc[ a ](TRecved2) +]}
| step_flipbit_send2 : ∀ a, flipbit_step (a, TRecved1) (a ! π2) {[+ proc[ a ](TSentBit) +]}
| step_flipbit_send1 : ∀ a, flipbit_step (a, TRecved2) (a ! π1) {[+ proc[ a ](TSentBit) +]}
| step_flipbit_end : ∀ a, flipbit_step (a, TSentBit) (a ! ∅) ∅.

Definition FlipBit : ProcLang.
Proof. by eapply mkProgLang, flipbit_step. Defined.

Definition LangTable (x : LangName) : ProcLang :=
  match x with
  | LangName_session_type => SessionTypes
  | LangName_flip_bit => FlipBit
  end.

Instance NObj_eq_dec_inst {lang : LangName} : EqDecision (NObj (LangTable lang)).
  by apply NObj_eq_dec.
Defined.

Definition ObjBody := {lang & NObj (LangTable lang)}.
Definition Obj := AtomicObj ObjBody.

Lemma Exist_P_inj2 (lang : LangName) (P1 P2 : NObj (LangTable lang)) :
  @existT _ (fun lang => NObj (LangTable lang)) lang P1 = existT lang P2 -> P1 = P2.
Proof.
  apply exist_inj2_uip. intros. by apply UIP_dec, LangName_eq_dec.
Qed.

Instance ObjBody_eq_dec : EqDecision ObjBody.
  intros [] [].
  destruct (decide (x = x0)); simplify_eq; try (right; congruence).
  destruct (decide (n = n0)); simplify_eq.
  + by left.
  + right. injection. intro nP. apply n1. by apply Exist_P_inj2.
Defined.

Instance Obj_eq_dec : EqDecision Obj.
  solve_decision.
Defined.

Instance ObjBody_countable : Countable ObjBody.
  unfold ObjBody. eapply sigma_countable_helper.
  intros []; by apply NObj_countable.
Defined.

Definition Cfg := gmultiset Obj.
Definition NCfg : Type := Cfg * ObjBody.

Definition inst (Ω : NCfg) (a : sym) : Cfg.
  destruct Ω as [Ω [lang P]].
  exact (Ω ⊎ {[+ proc[ a ] (existT lang P) +]}).
Defined.

Definition add_NCfg_Cfg (Ω : NCfg) (Ω' : Cfg) : NCfg :=
    match Ω with (Ω, P) => (Ω' ⊎ Ω, P) end.

Definition rhs_to_Cfg (lang : LangName) (rhs : AtomicObj (NObj (LangTable lang))) : Obj.
  destruct rhs as [a P | a b].
  - exact (proc[ a ] (existT lang P)).
  - exact (fwd[ a ] b).
Defined.

Inductive Cfg_step : Cfg -> Action -> Cfg -> Prop :=
| Cfg_step_obj lang a P α Ω :
  stepObj (LangTable lang) (a, P) α Ω ->
  Cfg_step {[+ (proc[ a ] (existT lang P) : Obj) +]} α (gmultiset_map (rhs_to_Cfg lang) Ω)
| Cfg_step_fwd a b P :
  Cfg_step {[+ proc[ b ]( P ); fwd[ a ] b +]} ∅ {[+ proc[ a ]( P ) +]}
| Cfg_step_frame α Ω Ω' Ω₀ :
  Cfg_step Ω α Ω' -> Cfg_step (Ω ⊎ Ω₀) α (Ω' ⊎ Ω₀)
| Cfg_step_comm a c Ω₁ Ω₁' Ω₂ Ω₂' :
  Cfg_step Ω₁ (a ! c) Ω₁' -> Cfg_step Ω₂ (a ? c) Ω₂' ->
  Cfg_step (Ω₁ ⊎ Ω₂) Action_silent (Ω₁' ⊎ Ω₂').

Lemma Cfg_step_frame_rev α Ω Ω' Ω₀ : Cfg_step Ω α Ω' -> Cfg_step (Ω₀ ⊎ Ω) α (Ω₀ ⊎ Ω').
Proof.
  replace (Ω₀ ⊎ Ω') with (Ω' ⊎ Ω₀) by multiset_solver.
  replace (Ω₀ ⊎ Ω) with (Ω ⊎ Ω₀) by multiset_solver.
  by apply Cfg_step_frame.
Qed.

Lemma Cfg_step_obj_forded a lang proc α Ω Ω' :
  stepObj (LangTable lang) (a, proc) α Ω' -> Ω = gmultiset_map (rhs_to_Cfg lang) Ω' ->
  Cfg_step {[+ (proc[ a ] (existT lang proc) : Obj) +]} α Ω.
Proof. intros H ->. by apply Cfg_step_obj. Qed.

Inductive Cfg_steps : Cfg -> Cfg -> Prop :=
| Cfg_steps_refl Ω : Cfg_steps Ω Ω
| Cfg_steps_cons Ω Ω' Ω'' : Cfg_step Ω ∅ Ω' -> Cfg_steps Ω' Ω'' -> Cfg_steps Ω Ω''.

Lemma Cfg_steps_append : ∀ Ω Ω' Ω'', Cfg_steps Ω Ω' -> Cfg_steps Ω' Ω'' -> Cfg_steps Ω Ω''.
Proof. induction 1; eauto using Cfg_steps. Qed. 

Lemma Cfg_steps_single : ∀ Ω Ω', Cfg_step Ω ∅ Ω' -> Cfg_steps Ω Ω'.
Proof. eauto using Cfg_steps. Qed. 

Lemma Cfg_steps_frame Ω Ω' Ω₀ : Cfg_steps Ω Ω' -> Cfg_steps (Ω ⊎ Ω₀) (Ω' ⊎ Ω₀).
Proof.
  induction 1.
  - constructor.
  - eapply Cfg_steps_cons. 2: done. by apply Cfg_step_frame.  
Qed.

Lemma Cfg_steps_frame_rev Ω Ω' Ω₀ : Cfg_steps Ω Ω' -> Cfg_steps (Ω₀ ⊎ Ω) (Ω₀ ⊎ Ω').
Proof.
  induction 1.
  - constructor.
  - eapply Cfg_steps_cons. 2: done. by apply Cfg_step_frame_rev.  
Qed.

Definition NCfg_steps (Ω Ω' : NCfg) : Prop := ∀ a, Cfg_steps (inst Ω a) (inst Ω' a).

Lemma NCfg_steps_append : ∀ Ω Ω' Ω'', NCfg_steps Ω Ω' -> NCfg_steps Ω' Ω'' -> NCfg_steps Ω Ω''.
Proof. unfold NCfg_steps. intros. eauto using Cfg_steps_append. Qed.

Definition termInterpAux (Ω' : NCfg) (A : type) (valueInterp : NCfg -> type -> Prop) : Prop :=
  ∃ Ω, NCfg_steps Ω' Ω ∧ valueInterp Ω A.

Fixpoint valueInterp (Ω : NCfg) (A : type) : Prop :=
  let termInterp Ω A := termInterpAux Ω A valueInterp in
  match A with
    | T1 => ∀ a, Cfg_step (inst Ω a) (a ! ∅) ∅
    | TTensor A B => ∀ b, ∃ a, ∃ Ω1, ∃ Ω2,
      termInterp Ω1 A ∧ termInterp Ω2 B ∧ Cfg_step (inst Ω b) (b ! Payload_sym a) (inst Ω1 a ⊎ inst Ω2 b)
    | TLolli A B => ∀ b, ∀ a, ∀ Ω1, ∃ Ω2,
      termInterp Ω1 A -> termInterp Ω2 B ∧ Cfg_step (inst Ω b ⊎ inst Ω1 a) (b ? Payload_sym a) (inst Ω2 b)
    | TWith A B => (∀ a, ∃ Ω1, termInterp Ω1 A ∧ Cfg_step (inst Ω a) (a ? π1) (inst Ω1 a))
      ∧ (∀ a,∃ Ω2, termInterp Ω2 B ∧ Cfg_step (inst Ω a) (a ? π2) (inst Ω2 a))
    | TPlus A B => (∀ a, ∃ Ω1, termInterp Ω1 A ∧ Cfg_step (inst Ω a) (a ! π1) (inst Ω1 a))
      ∨ (∀ a,∃ Ω2, termInterp Ω2 B ∧ Cfg_step (inst Ω a) (a ! π2) (inst Ω2 a))
    end.

Definition termInterp (Ω : NCfg) (A : type) := termInterpAux Ω A valueInterp.

Lemma backwards_closure (Ω Ω' : NCfg) (A : type) :
  NCfg_steps Ω Ω' -> termInterp Ω' A -> termInterp Ω A.
Proof. intros st1 (Ω'' & st2 & H). eexists. eauto using NCfg_steps_append. Qed.

Lemma valueInterp_termInterp Ω A : valueInterp Ω A -> termInterp Ω A.
Proof. intros. eexists. split; [|done]. intros a. constructor. Qed.

(* Complementary processes *)
Definition compl := gmap var (sym * NCfg).

Definition substOf : compl -> substObj := fmap fst.

Lemma substOf_union {S S' : compl} : substOf (S ∪ S') = substOf S ∪ substOf S'.
Proof. unfold substOf. by rewrite map_fmap_union. Qed.

Lemma substOf_insert {S : compl} x v : substOf (<[x := v]> S) = <[x := fst v]> (substOf S).
Proof. unfold substOf. by rewrite fmap_insert. Qed.

Lemma substOf_delete {S : compl} x : substOf (delete x S) = delete x (substOf S).
Proof. unfold substOf. by rewrite fmap_delete. Qed.

(* Semantically well-typedness of complementary processes *)
Definition typed_compl (S : compl) (Γ : sourceCtx) :=
  gmap_Forall2 (fun _ s => termInterp (snd s)) S Γ.

Lemma typed_compl_insert (S : compl) (Γ : sourceCtx) v a A Ω :
  v ∉ S -> typed_compl S Γ -> termInterp Ω A -> typed_compl (<[v := (a, Ω)]> S) (<[v := A]> Γ).
Proof. intros Hv HS HΩ. by eapply gmap_Forall2_insert_2. Qed.

Lemma typed_compl_singleton {S : compl} v A :
  typed_compl S {[v := A]} ->
  {Ω' & ((S = {[v := Ω']}) * termInterp (snd Ω') A : Type)}.
Proof.
  intros H. eapply gmap_Forall2_singleton_inv_r in H.
  destruct H as (a & -> & H). eexists. split; done.
Qed.

Lemma typed_compl_lookup_None S Γ x : typed_compl S Γ ->
  x ∉ Γ -> x ∉ substOf S.
Proof.
  intros. unfold substOf. rewrite lookup_fmap fmap_None.
  by eapply gmap_Forall2_lookup_None.
Qed.

Notation "st! a" := (existT LangName_session_type a) (at level 50).

Section applyCompl.
  Definition applyComplAux : sym * NCfg -> Cfg := λ '(a, Ω), inst Ω a.
  Definition applyCompl (S : compl) (obj : ObjBody) : NCfg :=
    (codom (applyComplAux <$> S), obj).

  Lemma applyCompl_empty obj : applyCompl ∅ obj = (∅, obj).
  Proof. unfold applyCompl. by rewrite codom_empty. Qed.

  Lemma applyCompl_insert {S : compl} {v} {obj} a Ω :
    v ∉ S -> applyCompl (<[v := (a, Ω)]> S) obj = add_NCfg_Cfg (applyCompl S obj) (inst Ω a).
  Proof.
    intros. unfold applyCompl. rewrite fmap_insert codom_insert. 1: done. 
    rewrite lookup_fmap. by rewrite H.
  Qed.

  Lemma applyCompl_union {S1 S2 : compl} {obj} : S1 ##ₘ S2 ->
    applyCompl (S1 ∪ S2) obj = (codom (applyComplAux <$> S1) ⊎ codom (applyComplAux <$> S2), obj).
  Proof.
    intros Hdisj. unfold applyCompl. f_equal. rewrite -codom_union. 2: by eapply map_disjoint_fmap.
    by rewrite map_fmap_union.
  Qed.

  Lemma applyCompl_singleton v Ω obj : applyCompl {[v := Ω]} obj = (applyComplAux Ω, obj).
  Proof. unfold applyCompl. by rewrite map_fmap_singleton codom_singleton. Qed.

  Lemma applyCompl_notIn x {S : compl} : x ∉ S -> x ∉ applyComplAux <$> S.
  Proof. intros. rewrite lookup_fmap. by rewrite H. Qed.
End applyCompl.

Lemma substOf_discard_1 `{Countable sym} :
  ∀ v a P Γ S A, v ∉ Γ -> typed_term Γ P A -> typed_compl S Γ ->
  substTerm (<[v := a]> (substOf S)) P = substTerm (substOf S) P.
Proof.
  intros. eapply subst_discard_1; [done|done|]. eapply gmap_Forall2_fmap_l.
  3, 4: done. all: done.
Qed.

Lemma substOf_discard_n `{Countable sym} :
  ∀ P Γ S S' A, typed_term Γ P A -> typed_compl S Γ ->
  S ##ₘ S' -> substTerm (substOf S ∪ substOf S') P = substTerm (substOf S) P.
Proof.
  intros. eapply subst_discard_n.
  - by eapply map_disjoint_fmap.
  - done.
  - by eapply gmap_Forall2_fmap_l.
Qed.

Ltac by_def_of_logical_relations := simpl; unfold termInterp, termInterpAux; simpl valueInterp.
Ltac by_def_of_logical_relations_in H := unfold termInterp, termInterpAux in H; simpl valueInterp in H.
Definition fix_stepping_rhs := gmultiset_map (rhs_to_Cfg LangName_session_type).

Theorem fundamental Γ P A S :
  typed_term Γ P A -> typed_compl S Γ ->
  termInterp (applyCompl S (st! substTerm (substOf S) P)) A.
Proof.
  intros HP. revert S. induction HP.
  - (* fwd *)
    by_def_of_logical_relations. intros S HS.
    destruct (typed_compl_singleton x A HS) as (Ω & -> & Ω' & Hstep & HvalueInterp). eexists.
    unfold substOf. rewrite applyCompl_singleton map_fmap_singleton substVar_insert_None.
    destruct Ω as (a & Ω & lang & obj). split; [|done].
    intros b. simpl. eapply Cfg_steps_append; [|by apply Hstep]. simpl.
    set CfgObj_a := {[+ proc[ a ] existT lang obj +]}.
    set CfgObj_b := {[+ proc[ b ] existT lang obj +]}.
    eapply Cfg_steps_append.
    + by eapply Cfg_steps_single, Cfg_step_frame_rev, Cfg_step_obj_forded; [constructor|]. 
    + rewrite gmultiset_map_singleton. simpl.
      set CfgFwd := {[+ fwd[ b ] a +]}.
      replace (Ω ⊎ CfgObj_a ⊎ CfgFwd) with (Ω ⊎ (CfgObj_a ⊎ CfgFwd)) by multiset_solver.
      unfold CfgObj_a, CfgFwd. eapply Cfg_steps_single, Cfg_step_frame_rev, Cfg_step_fwd.
  - (* cut *)
    by_def_of_logical_relations. intros S HS.
    eapply gmap_Forall2_union_inv_r in HS; [|done]. destruct HS as (S1 & S2 & ((-> & Hσ1) & Hσ2)).
    pose proof (HP1' := IHHP1 S1 Hσ1).
    rewrite applyCompl_union. 2: by eapply gmap_Forall2_disjoint.
    eapply backwards_closure. intros a. 2: eapply IHHP2; eapply typed_compl_insert.
    4: by eapply IHHP1. 3: done. rewrite applyCompl_insert. 2, 3: by eapply gmap_Forall2_lookup_None.
    rewrite substOf_insert. simpl fst. simpl inst.
    set CfgS1 := codom (applyComplAux <$> S1).
    set CfgS2 := codom (applyComplAux <$> S2).
    set CfgP12 := {[+ proc[ a ] (st! cut (substTerm _ P1) (substTerm _ P2) _ A) +]}.
    replace (CfgS1 ⊎ CfgS2 ⊎ CfgP12) with (CfgP12  ⊎ (CfgS1 ⊎ CfgS2)) by multiset_solver.
    eapply Cfg_steps_append. eapply Cfg_steps_frame, Cfg_steps_single, Cfg_step_obj. simpl.
    econstructor. instantiate (3 := 42). instantiate (1 := 42).
    (* ^ here we pick a silly name for P1, works because of existential *)
    rewrite gmultiset_map_disj_union. do 2 (rewrite gmultiset_map_singleton). unfold rhs_to_Cfg.
    rewrite substOf_union. eapply substOf_discard_n in HP1. 2: eapply Hσ1.
    2: by eapply gmap_Forall2_disjoint. rewrite HP1.
    (* Now everything besides P2 is done, we use frame only to simplify the goal *)
    set CfgP1 := {[+ proc[ 42 ] (st! substTerm _ P1) +]}.
    set CfgP2_12 := {[+ proc[ a ] (st! substTerm _ (substTerm _ P2)) +]}.
    set CfgP2_2 := {[+ proc[ a ] (st! substTerm _ P2) +]}.
    replace (CfgP2_12 ⊎ CfgP1 ⊎ (CfgS1 ⊎ CfgS2)) with
       (CfgS1 ⊎ CfgP1 ⊎ CfgS2 ⊎ CfgP2_12) by multiset_solver.
    eapply Cfg_steps_frame_rev. unfold CfgP2_12, CfgP2_2.
    rewrite map_union_comm. 2: unfold substOf; eapply map_disjoint_fmap; by eapply gmap_Forall2_disjoint.
    rewrite delete_union. rewrite <- subst_insert.
    2: eapply lookup_union_None; split; eapply lookup_delete.
    replace (delete x (substOf S2)) with (substOf S2).
    2: rewrite delete_notin; [done|]. 2: by eapply typed_compl_lookup_None.
    rewrite insert_union_l.
    assert (substTerm (<[x:=42]> (substOf S2) ∪ delete x (substOf S1)) P2
          = substTerm (<[x:=42]> (substOf S2)) P2).
    2: rewrite H1; by constructor.
    pose proof (HP1'' := HP1'). destruct HP1'' as (Ω, (_ & HvalΩ)). replace 42 with (fst (42, Ω)) by done.
    rewrite <- substOf_insert. rewrite <- substOf_delete.
    eapply substOf_discard_n. 1: done.
    + eapply gmap_Forall2_insert_2; [|done]. by eapply valueInterp_termInterp.
    + eapply map_disjoint_insert_l. split; [eapply lookup_delete|].
      eapply map_disjoint_delete_r. symmetry. by eapply gmap_Forall2_disjoint.
  - (* send_1 *)
    by_def_of_logical_relations. intros S HS. eexists. split; [constructor|]. intro.
    unfold inst. apply gmap_Forall2_empty_inv_r in HS. rewrite HS. rewrite applyCompl_empty.
    set Cfg := {[+ proc[ a] (st! send_1) +]}.
    rewrite gmultiset_disj_union_left_id. eapply Cfg_step_obj_forded; [constructor|multiset_solver].
  - (* recv_1 *)
    by_def_of_logical_relations. intros S HS.
    destruct (gmap_Forall2_insert_inv_r _ _ T1 H HS) as ((a & Ω) & S' & ((-> & Hx) & HΩ) & HS').
    destruct (IHHP S' HS') as (Ω' & (HstepΩ' & HΩ')). eexists. split; [|done].
    rewrite (applyCompl_insert _ _ Hx). intros a'. eapply Cfg_steps_append. 2: by apply HstepΩ'.
    unfold substOf. rewrite fmap_insert. simpl.
    simple refine (let Hσ : x ∉ fst <$> S' := _ in _). 1: by rewrite lookup_fmap Hx.
    rewrite delete_insert; [|done].
    by_def_of_logical_relations_in HΩ. destruct HΩ as (Ω1 & HΩ1 & HΩstep). specialize (HΩstep a).
    set CfgS := codom (applyComplAux <$> S').
    set CfgΩ := inst Ω a.
    set CfgPrecv := {[+ proc[ a'] (st! recv_1 x _) +]}.
    set CfgP := {[+ proc[ a'] (st! substTerm _ P) +]}.
    replace (CfgΩ ⊎ CfgS ⊎ CfgPrecv) with ((CfgΩ ⊎ CfgPrecv) ⊎ CfgS) by multiset_solver.
    replace (CfgS ⊎ CfgP) with (CfgP ⊎ CfgS) by multiset_solver.
    eapply Cfg_steps_frame. replace CfgP with (∅ ⊎ CfgP) by multiset_solver. eapply Cfg_steps_append.
    + eapply Cfg_steps_frame. apply HΩ1.
    + eapply Cfg_steps_single, Cfg_step_comm; [done|].
      eapply Cfg_step_obj_forded. 1: eapply step_recv1. by rewrite gmultiset_map_singleton.
  - (* recv_lolli *)
    by_def_of_logical_relations. intros S HS. eexists. split; [constructor|].
    intros b a Ω1. eexists. intro HΩ1A.
    simple refine (let H' : y ∉ S := ?[H'] in _). 1: by apply (gmap_Forall2_lookup_None _ HS).
    simple refine (let H'fst : y ∉ fst <$> S := ?[H'fst] in _). 1: by rewrite lookup_fmap H'. split.
    + by apply IHHP, typed_compl_insert with (a := a).
    + unfold substOf at 1. rewrite delete_notin. 2: done. simpl.
      rewrite fmap_insert codom_insert. 2: by rewrite lookup_fmap H'.
      (* Coq doesn't seem to understand typeclasses when doing `replace` *)
      set CfgΩ1 := applyComplAux (a, Ω1).
      set CfgPrecv := {[+ proc[ b ] (st! recv_lolli y (substTerm _ P)) +]}.
      set CfgP := {[+ proc[ b ] (st! substTerm (substOf _) P) +]}.
      set CfgS := codom (applyComplAux <$> S).
      set CfgΩ1' := inst Ω1 a.
      replace (CfgΩ1 ⊎ CfgS ⊎ CfgP) with ((CfgS ⊎ CfgΩ1) ⊎ CfgP) by multiset_solver.
      replace (CfgS ⊎ CfgPrecv ⊎ CfgΩ1') with ((CfgS ⊎ CfgΩ1') ⊎ CfgPrecv) by multiset_solver.
      eapply Cfg_step_frame_rev, Cfg_step_obj_forded; [constructor|].
      rewrite gmultiset_map_singleton. unfold CfgP, rhs_to_Cfg.
      rewrite <- subst_insert. unfold substOf. by rewrite fmap_insert.
      done.
  - (* send_lolli *)
    intros S HS.
    apply gmap_Forall2_insert_inv_r in HS.
    destruct HS as ((b & Ω) & S' & ((-> & Hx) & HS') & HS).
    2: by rewrite lookup_insert_ne.
    apply gmap_Forall2_insert_inv_r in HS. 2: done.
    destruct HS as ((a & Ω') & S'' & ((-> & Hy) & HS'') & HS).
    rewrite !applyCompl_insert. 2, 3: done. simpl. unfold substOf.
    rewrite !fmap_insert. simpl. rewrite substVar_insert_None.
    rewrite substVar_insert_ne; [|done]. rewrite substVar_insert_eq.
    by_def_of_logical_relations_in HS'. destruct HS' as (Ω0 & HΩ0 & HΩ0step).
    specialize (HΩ0step b a).
    destruct (HΩ0step Ω') as (Ω2 & HΩ2 & HΩ2step); [exact HS''|].
    eapply backwards_closure.
    set CfgΩb := inst Ω b.
    set CfgΩ'a := inst Ω' a.
    set CfgS := codom (applyComplAux <$> S'').
    intros c. simpl.
    set CfgSendba := {[+ proc[ c ] (st! send_lolli (Sym b) (Sym a) (substTerm _ P)) +]}.
    eapply Cfg_steps_append.
    { replace (CfgΩb ⊎ (CfgΩ'a ⊎ CfgS) ⊎ CfgSendba) with (CfgΩb ⊎ (CfgΩ'a ⊎ CfgS ⊎ CfgSendba)) by multiset_solver.
      eapply Cfg_steps_frame, HΩ0. }
    eapply Cfg_steps_append.
    {
      replace (inst Ω0 b ⊎ (CfgΩ'a ⊎ CfgS ⊎ CfgSendba)) with ((CfgSendba ⊎ (inst Ω0 b ⊎ CfgΩ'a)) ⊎ CfgS) by multiset_solver.
      eapply Cfg_steps_frame, Cfg_steps_single, Cfg_step_comm.
      2: apply HΩ2step.
      eapply Cfg_step_obj_forded; [constructor|done].
    }
    rewrite gmultiset_map_singleton. simpl.
    assert ((inst (inst Ω2 b ⊎ CfgS,st! substTerm (<[x:=b]> (<[y:=a]> (fst <$> S''))) P) c) = {[+ proc[ c] (st! substTerm (<[x:=b]> (<[y:=a]> (fst <$> S''))) P) +]}
    ⊎ inst Ω2 b ⊎ CfgS) as ->.
    { simpl. multiset_solver. }
    eapply Cfg_steps_refl.
    assert (typed_compl (<[x:=(b, Ω2)]>  S'') (<[x:=B]> Γ)).
    { eapply typed_compl_insert. 2, 3: done.
      by rewrite lookup_insert_ne in Hx. }
    specialize (IHHP _ X).
    rewrite applyCompl_insert in IHHP. simpl in IHHP.
    unfold substOf in IHHP. rewrite fmap_insert in IHHP. simpl in IHHP.
    rewrite insert_commute; [|done].
    2: by rewrite lookup_insert_ne in Hx.
    replace (<[x:=b]> (fst <$> S'')) with (substOf (<[x:=(b, Ω2)]> S'')).
    2: unfold substOf; by rewrite fmap_insert.
    eapply substOf_discard_1 with (a := a) in HP. 3: done. rewrite HP. unfold substOf.
    rewrite fmap_insert. by eapply IHHP. eapply lookup_insert_None. split.
    2: eapply H1.
    done.
  - (* send_tensor *)
    intros S HS. 
    apply gmap_Forall2_insert_inv_r in HS.
    destruct HS as ((a & Ω) & S' & ((-> & Hx) & HS') & HS).
    by_def_of_logical_relations. eexists. split. 3: done.
    rewrite applyCompl_insert. simpl.
    unfold substOf. rewrite fmap_insert. rewrite substVar_insert_None. simpl.
    unfold NCfg_steps.
    intro b. apply Cfg_steps_refl. exact Hx.
    intro b. exists a. do 2 eexists. repeat split.
    3: {
      simpl.
      set CfgS' := codom (applyComplAux <$> S').
      set ProcP := substTerm (<[y:=a]> (fst <$> S')) P.
      set ProcSend := st! send_tensor (Sym a) ProcP.
      assert ((inst (CfgS', ProcSend) b) = CfgS' ⊎ {[+ proc[ b] (ProcSend) +]}) as H' by by simpl.
      replace (inst Ω a ⊎ CfgS' ⊎ {[+ proc[ b] ProcSend +]}) with (inst Ω a ⊎ (CfgS' ⊎ {[+ proc[ b] ProcSend +]})) by multiset_solver.
      rewrite <-H'. eapply Cfg_step_frame_rev. simpl.
      assert ((inst (CfgS', st! ProcP) b) = (CfgS' ⊎ {[+ proc[ b ] (st! ProcP) +]})) as -> by by simpl.
      eapply Cfg_step_frame_rev.
      eapply Cfg_step_obj_forded; [constructor|].
      by rewrite gmultiset_map_singleton.
    }
    exact HS'. unfold termInterp in IHHP.
    specialize (IHHP _ HS).
    unfold substOf in IHHP. unfold applyCompl in IHHP.
    eapply substOf_discard_1 with (a := a) in HP. 2, 3: done.
    rewrite HP. eapply IHHP.
  - (* recv_tensor *)
    intros S HS.
    apply gmap_Forall2_insert_inv_r in HS.
    destruct HS as ((b & Ω) & S' & ((-> & Hx) & HS') & HS). 2: done.
    simpl in HS'. destruct HS' as (Ω' & HΩΩ' & HΩ'AxB).
    by_def_of_logical_relations_in HΩ'AxB.
    specialize (HΩ'AxB b). destruct HΩ'AxB as (a & Ω1 & Ω2 & HΩ1 & HΩ2 & HΩstep).
    rewrite applyCompl_insert. 2: done. simpl.
    unfold substOf. rewrite fmap_insert substVar_insert_None. simpl.
    eapply backwards_closure.
    intro c. eapply Cfg_steps_append. simpl.
    set CfgΩb := inst Ω b.
    set CfgS := codom (applyComplAux <$> S').
    set recv_term := (st! recv_tensor (Sym b) y (substTerm _ P)).
    set CfgRecv := {[+ proc[ c ] recv_term +]}.
    replace (CfgΩb ⊎ CfgS ⊎ CfgRecv) with (CfgΩb ⊎ (CfgS ⊎ CfgRecv)) by multiset_solver.
    apply Cfg_steps_frame. apply HΩΩ'.
    (* It seems that the previous 'set' are lost :( I don't like this *)
    set CfgΩ'b := inst Ω' b. set CfgS := codom (applyComplAux <$> S'). set recv_term := (st! recv_tensor (Sym b) y (substTerm (delete y (<[x:=b]> (fst <$> S'))) P)).
    set CfgRecv := {[+ proc[ c ] recv_term +]}.
    eapply Cfg_steps_append.
    eapply Cfg_steps_single.
    replace (CfgΩ'b ⊎ (CfgS ⊎ CfgRecv)) with ((CfgΩ'b ⊎ CfgRecv) ⊎ CfgS) by multiset_solver.
    eapply Cfg_step_frame. eapply Cfg_step_comm.
    eapply HΩstep.
    eapply Cfg_step_obj_forded; [constructor|by rewrite gmultiset_map_singleton]. simpl.
    set rest_term := (st! substTerm {[y := a]} (substTerm _ P)).
    replace (inst Ω1 a ⊎ inst Ω2 b ⊎ {[+ proc[ c ] rest_term +]} ⊎ CfgS) with (inst (inst Ω1 a ⊎ inst Ω2 b ⊎ CfgS, rest_term) c).
    2: { simpl. multiset_solver. }
    eapply Cfg_steps_refl.
    assert (typed_compl (<[y:=(a,Ω1)]> (<[x:=(b,Ω2)]> S')) (<[y:=A]> (<[x:=B]> Γ))).
    { eapply typed_compl_insert.
      - rewrite lookup_insert_ne.
        eapply gmap_Forall2_lookup_None. apply HS. exact H0. exact H1.
      - eapply typed_compl_insert.
        eapply gmap_Forall2_lookup_None. apply HS. exact H. exact HS.
        exact HΩ2.
      - exact HΩ1. }
    specialize (IHHP _ X).
    repeat rewrite applyCompl_insert in IHHP. simpl in IHHP. 2: done.
    2: { rewrite lookup_insert_ne.
         eapply gmap_Forall2_lookup_None. apply HS. exact H0. exact H1. }
    unfold substOf in IHHP. repeat rewrite fmap_insert in IHHP. simpl in IHHP.
    rewrite <-subst_insert. 2: by rewrite lookup_delete.
    rewrite delete_insert_ne; [|done]. rewrite delete_notin.
    2: by eapply typed_compl_lookup_None.
    by replace (inst Ω1 a ⊎ inst Ω2 b ⊎ codom (applyComplAux <$> S'))
      with (inst Ω1 a ⊎ (inst Ω2 b ⊎ codom (applyComplAux <$> S'))) by multiset_solver.
  - (* recv_with *)
    by_def_of_logical_relations. intros. eexists. split; [constructor|].
    split; intros; eexists; split.
    + by apply IHHP1.
    + eapply Cfg_step_frame_rev, Cfg_step_obj_forded; [constructor|by rewrite gmultiset_map_singleton].
    + by apply IHHP2.
    + eapply Cfg_step_frame_rev, Cfg_step_obj_forded; [constructor|by rewrite gmultiset_map_singleton].
  - (* send_with *)
    by_def_of_logical_relations. intros S HS.
    destruct (gmap_Forall2_insert_inv_r _ _ (A ⊛ B) H HS) as ((a & Ω) & S' & ((-> & Hx) & HΩ) & HS').
    destruct HΩ as (Ω'' & HΩsteps'' & HΩv1'' & HΩv2'').
    destruct (HΩv1'' a) as (Ω1 & HΩ1 & HΩ1step).
    destruct (HΩv2'' a) as (Ω2 & HΩ2 & HΩ2step).
    rewrite applyCompl_insert; [simpl|done]. 
    unfold substOf. rewrite fmap_insert. rewrite substVar_insert_None. simpl in *.
    destruct sel.
    {assert (typed_compl (<[x:=(a, Ω1)]> S') (<[x:=A]> Γ)) as HΩ1IH.
      { eapply typed_compl_insert.
        1: done.
        1: eapply HS'.
        eapply HΩ1. }
      specialize (IHHP (<[x:=(a, Ω1)]> S') HΩ1IH).
      eapply backwards_closure.
      2: eapply IHHP.
      eapply NCfg_steps_append with (Ω':=(inst Ω'' a ⊎ codom (applyComplAux <$> S'), st! send_with (Sym a) true (substTerm (<[x:=a]> (fst <$> S')) P))); simpl.
      * intros b. eapply Cfg_steps_frame. eapply Cfg_steps_frame. by eapply HΩsteps''.
      * intros b. simpl.
        rewrite fmap_insert codom_insert.
        2: eapply applyCompl_notIn; eapply Hx.
        unfold substOf.
        simpl. 
        set CfgΩ'' := inst Ω'' a.
        set CfgΩ1 := inst Ω1 a.
        set CfgS' := codom (applyComplAux <$> S').
        set CfgSend := {[+ proc[ b ] (st! send_with (Sym a) true (substTerm _ P)) +]}.
        set CfgP := {[+ proc[ b ] (st! substTerm _ P) +]}.
        replace (CfgΩ'' ⊎ CfgS' ⊎ CfgSend) with (CfgS' ⊎ (CfgΩ'' ⊎ CfgSend)) by multiset_solver.
        replace (CfgΩ1 ⊎ CfgS' ⊎ CfgP) with (CfgS' ⊎ (CfgΩ1 ⊎ CfgP)) by multiset_solver.
        eapply Cfg_steps_frame_rev. eapply Cfg_steps_cons.
        1: rewrite gmultiset_disj_union_comm. eapply Cfg_step_comm.
        2: eapply HΩ1step.
        1: eapply Cfg_step_obj_forded; [constructor|by rewrite gmultiset_map_singleton].
        simpl.
        rewrite gmultiset_disj_union_comm.
        unfold CfgΩ1, CfgP.
        rewrite fmap_insert. simpl.
        eapply Cfg_steps_refl.
      }
    {assert (typed_compl (<[x:=(a, Ω2)]> S') (<[x:=B]> Γ)) as HΩ2IH.
      { eapply typed_compl_insert.
        1: done.
        1: eapply HS'.
        eapply HΩ2. }
      specialize (IHHP (<[x:=(a, Ω2)]> S') HΩ2IH).
      eapply backwards_closure.
      2: eapply IHHP.
      eapply NCfg_steps_append with (Ω':=(inst Ω'' a ⊎ codom (applyComplAux <$> S'), st! send_with (Sym a) false (substTerm (<[x:=a]> (fst <$> S')) P))); simpl.
      * unfold NCfg_steps. intros b. eapply Cfg_steps_frame. eapply Cfg_steps_frame. by eapply HΩsteps''.
      * unfold NCfg_steps. intros b. simpl.
        rewrite fmap_insert codom_insert.
        2: eapply applyCompl_notIn; eapply Hx.
        unfold substOf.
        simpl. 
        set CfgΩ'' := inst Ω'' a.
        set CfgΩ2 := inst Ω2 a.
        set CfgS' := codom (applyComplAux <$> S').
        set CfgSend := {[+ proc[ b] (st! send_with (Sym a) false (substTerm (<[x:=a]> (fst <$> S')) P)) +]}.
        set CfgP := {[+ proc[ b] (st! substTerm (fst <$> <[x:=(a, Ω2)]> S') P) +]}.
        replace (CfgΩ'' ⊎ CfgS' ⊎ CfgSend) with (CfgS' ⊎ (CfgΩ'' ⊎ CfgSend)) by multiset_solver.
        replace (CfgΩ2 ⊎ CfgS' ⊎ CfgP) with (CfgS' ⊎ (CfgΩ2 ⊎ CfgP)) by multiset_solver.
        eapply Cfg_steps_frame_rev. eapply Cfg_steps_cons.
        1: rewrite gmultiset_disj_union_comm. eapply Cfg_step_comm.
        2: eapply HΩ2step.
        1: eapply Cfg_step_obj_forded; [constructor|by rewrite gmultiset_map_singleton].
        simpl.
        rewrite gmultiset_disj_union_comm.
        unfold CfgΩ2, CfgP.
        rewrite fmap_insert. simpl.
        eapply Cfg_steps_refl.
      }
  - (* send_plus *)
    intros S HS. by_def_of_logical_relations.
    destruct sel; eexists; split.
    1, 3: constructor.
    1: left.
    2: right.
    1, 2: intros; eexists; split; [eapply IHHP; eapply HS|];
    simpl; eapply Cfg_step_frame_rev; eapply Cfg_step_obj_forded;
    [constructor|by rewrite gmultiset_map_singleton].
  - (* recv_plus *)
    intros S HS. by_def_of_logical_relations.
    destruct (gmap_Forall2_insert_inv_r _ _ (A ⊕ B) H HS) as ((a & Ω) & S' & ((-> & Hx) & HΩ) & HS'). simpl in *.
    destruct HΩ as (Ω'' & HΩsteps'' & HΩv'').
    rewrite applyCompl_insert; [simpl|done]. 
    unfold substOf. rewrite fmap_insert. rewrite substVar_insert_None. simpl in *.
    destruct HΩv'' as [HΩv1''|HΩv2'']; 
    [destruct (HΩv1'' a) as (Ω1 & HΩ1 & HΩ1step)|destruct (HΩv2'' a) as (Ω2 & HΩ2 & HΩ2step)].
    { assert (typed_compl (<[x:=(a, Ω1)]> S') (<[x:=A]> Γ)) as HΩ1IH.
      1: by eapply typed_compl_insert.
      eapply backwards_closure.
      2: eapply IHHP1, HΩ1IH.
      unfold applyCompl.
      eapply NCfg_steps_append with (Ω':=(inst Ω'' a ⊎ codom (applyComplAux <$> S'), st! recv_plus (Sym a) (substTerm (<[x:=a]> (fst <$> S')) P1) (substTerm (<[x:=a]> (fst <$> S')) P2))); simpl.
      + intros b. eapply Cfg_steps_frame, Cfg_steps_frame. by eapply HΩsteps''.
      + intros b. simpl.
        rewrite fmap_insert codom_insert.
        2: eapply applyCompl_notIn; eapply Hx.
        unfold substOf.
        simpl. 
        set CfgΩ'' := inst Ω'' a.
        set CfgΩ1 := inst Ω1 a.
        set CfgS' := codom (applyComplAux <$> S').
        set CfgRecv := {[+ proc[ b] (st! recv_plus (Sym a) (substTerm (<[x:=a]> (fst <$> S')) P1) (substTerm (<[x:=a]> (fst <$> S')) P2)) +]}.
        set CfgP := {[+ proc[ b] (st! substTerm (fst <$> <[x:=(a, Ω1)]> S') P1) +]}.
        replace (CfgΩ'' ⊎ CfgS' ⊎ CfgRecv) with (CfgS' ⊎ (CfgΩ'' ⊎ CfgRecv)) by multiset_solver.
        replace (CfgΩ1 ⊎ CfgS' ⊎ CfgP) with (CfgS' ⊎ (CfgΩ1 ⊎ CfgP)) by multiset_solver.
        eapply Cfg_steps_frame_rev, Cfg_steps_cons.
        1: eapply Cfg_step_comm.
        1: eapply HΩ1step.
        1: eapply Cfg_step_obj_forded; [constructor|by rewrite gmultiset_map_singleton].
        simpl.
        unfold CfgΩ1, CfgP.
        rewrite fmap_insert.
        eapply Cfg_steps_refl.
    }
    { assert (typed_compl (<[x:=(a, Ω2)]> S') (<[x:=B]> Γ)) as HΩ2IH.
    { eapply typed_compl_insert.
      1: done.
      1: eapply HS'.
      eapply HΩ2. }
     eapply backwards_closure.
     2: eapply IHHP2, HΩ2IH.
     unfold applyCompl.
     eapply NCfg_steps_append with (Ω':=(inst Ω'' a ⊎ codom (applyComplAux <$> S'), st! recv_plus (Sym a) (substTerm (<[x:=a]> (fst <$> S')) P1) (substTerm (<[x:=a]> (fst <$> S')) P2))); simpl.
      + intros b. eapply Cfg_steps_frame. eapply Cfg_steps_frame. by eapply HΩsteps''.
      + intros b. simpl.
      rewrite fmap_insert codom_insert.
      2: eapply applyCompl_notIn; eapply Hx.
      unfold substOf.
      simpl. 
      set CfgΩ'' := inst Ω'' a.
      set CfgΩ2 := inst Ω2 a.
      set CfgS' := codom (applyComplAux <$> S').
      set CfgRecv := {[+ proc[ b] (st! recv_plus (Sym a) (substTerm (<[x:=a]> (fst <$> S')) P1) (substTerm (<[x:=a]> (fst <$> S')) P2)) +]}.
      set CfgP := {[+ proc[ b] (st! substTerm (fst <$> <[x:=(a, Ω2)]> S') P2) +]}.
      replace (CfgΩ'' ⊎ CfgS' ⊎ CfgRecv) with (CfgS' ⊎ (CfgΩ'' ⊎ CfgRecv)) by multiset_solver.
      replace (CfgΩ2 ⊎ CfgS' ⊎ CfgP) with (CfgS' ⊎ (CfgΩ2 ⊎ CfgP)) by multiset_solver.
      eapply Cfg_steps_frame_rev. eapply Cfg_steps_cons.
      1: eapply Cfg_step_comm.
      1: eapply HΩ2step.
      1: eapply Cfg_step_obj_forded; [constructor|by rewrite gmultiset_map_singleton].
      simpl.
      unfold CfgΩ2, CfgP. 
      rewrite fmap_insert. simpl.
      eapply Cfg_steps_refl.
    }
Qed.

Theorem adequacy P a : typed_term ∅ P T1 →
  ∃ Ω, Cfg_steps {[+ proc[ a ] st! P +]} Ω ∧
         Cfg_step Ω (a ! ∅) ∅.
Proof.
  intros H. eapply fundamental in H. 2: eapply gmap_Forall2_empty.
  by_def_of_logical_relations_in H. destruct H as (Ω & Hsteps & Hstep).
  exists (inst Ω a). split; [|done]. rewrite applyCompl_empty in Hsteps.
  rewrite subst_empty in Hsteps. specialize (Hsteps a). unfold inst in Hsteps at 1.
  rewrite gmultiset_disj_union_left_id in Hsteps. by eapply Hsteps.
Qed.

Ltac by_def_of_labeled_transitions := eapply Cfg_step_frame_rev; eapply Cfg_step_obj_forded; [constructor|by rewrite gmultiset_map_singleton].

Notation "bf! x" := (existT LangName_flip_bit x) (at level 20).

Lemma TToRecv_terminates: termInterp ( ∅, bf! TToRecv ) (TWith (T1 ⊕ T1) (T1 ⊕ T1)).
Proof.
  by_def_of_logical_relations.
  eexists. repeat split.
  unfold NCfg_steps.
  intro a. eapply Cfg_steps_refl.
  {
    intro a. eexists. split.
    2: {
      simpl. 
      set term := bf! TToRecv.
      assert ((inst (∅, bf! TRecved1) a) = (∅ ⊎ {[+ proc[ a ] bf! TRecved1 +]})) as -> by by simpl.
      by_def_of_labeled_transitions.
    }
    by_def_of_logical_relations.
    eexists. split.
    intro b. eapply Cfg_steps_refl.
    right. intro b. eexists. split.
    2: {
      simpl. 
      assert ((inst (∅, bf! TSentBit) b) = (∅ ⊎ {[+ proc[ b ] bf! TSentBit +]})) as -> by by simpl.
      by_def_of_labeled_transitions.
    }
    by_def_of_logical_relations.
    eexists. repeat split.
    intro c. eapply Cfg_steps_refl.
    intro c. simpl.
    rewrite gmultiset_disj_union_left_id.
    eapply Cfg_step_obj_forded; [constructor|].
    multiset_solver.
  } 
  intro a. eexists. split.
  2: {
    simpl. 
    set term := bf! TToRecv.
    assert ((inst (∅, bf! TRecved2) a) = (∅ ⊎ {[+ proc[ a ] bf! TRecved2 +]})) as -> by by simpl.
    by_def_of_labeled_transitions.
  }
  by_def_of_logical_relations.
  eexists. split.
  intro b. eapply Cfg_steps_refl.
  left. intro b. eexists. split.
  2:{
    simpl. set term := bf! TRecved2.
    assert ((inst (∅, bf! TSentBit) b) = (∅ ⊎ {[+ proc[ b ] bf! TSentBit +]})) as -> by by simpl.
    by_def_of_labeled_transitions.
  }
  by_def_of_logical_relations.
  eexists. split.
  intro c. eapply Cfg_steps_refl.
  intro c. simpl.
  rewrite gmultiset_disj_union_left_id.
  eapply Cfg_step_obj_forded; [constructor|].
  multiset_solver.
Qed.

Print Assumptions fundamental.
Print Assumptions TToRecv_terminates.
