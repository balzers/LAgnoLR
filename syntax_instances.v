From Coq Require Import String.
From stdpp Require Import base tactics gmap gmultiset option fin_maps.
From ST Require Import stdsharp syntax.

Instance type_eq_dec : EqDecision type.
Proof. solve_decision. Defined.

Section TypeCountable.
  Definition type_to_gentree (A : type) : gen_tree unit.
  Proof. induction A.
    1: by apply GenLeaf.
    - apply GenNode; [exact 1|by refine [IHA1; IHA2]]. 
    - apply GenNode; [exact 2|by refine [IHA1; IHA2]].
    - apply GenNode; [exact 3|by refine [IHA1; IHA2]].
    - apply GenNode; [exact 4|by refine [IHA1; IHA2]].
  Defined.

  Definition type_from_gentree : gen_tree unit -> option type.
  Proof.
    refine (let fix java n := match n with
      | GenLeaf () => Some T1
      | GenNode tag [l; r] => _
      | _ => None end in java).
    refine (lhs ← java l ; rhs ← java r ; _).
    refine (match tag with
      | 1 => Some (TTensor _ _)
      | 2 => Some (TLolli _ _)
      | 3 => Some (TWith _ _)
      | 4 => Some (TPlus _ _) | _ => None end).
    1, 3, 5, 7: exact lhs.
    all: exact rhs.
  Defined.

  Global Instance type_countable : Countable type.
  Proof.
    apply (inj_countable type_to_gentree type_from_gentree).
    intro A. induction A. 1: done.
    all: simpl; rewrite IHA1; rewrite IHA2; done.
  Defined.
End TypeCountable.

Instance direction_eq_dec : EqDecision direction.
Proof. solve_decision. Defined.

Instance payload_empty : Empty payload.
Proof. exact Payload_terminate. Defined.

Instance payload_eq_dec : EqDecision payload.
Proof. solve_decision. Defined.

Instance Action_empty : Empty Action.
Proof. exact Action_silent. Defined.

Instance Action_eq_dec : EqDecision Action.
Proof. solve_decision. Defined.

Instance AtomicObj_eq_dec {NObj : Type} `{NObj_eq_dec : EqDecision NObj} : EqDecision (AtomicObj NObj).
Proof. solve_decision. Defined.

Section AtomicObjCountable.
  Context (NObj : Type).
  Context `{NObj_eq_dec : EqDecision NObj}.
  Context `{NObj_countable : Countable NObj}.

  Definition AtomicObj' : Type := sym * (NObj + sym).
  Definition AtomicObj_to_prime (P : AtomicObj NObj) : AtomicObj' :=
    match P with
    | proc[ a ](P) => (a, inl P)
    | fwd[ a ](b) => (a, inr b)
    end.
  Definition AtomicObj_from_prime (P : AtomicObj') : option (AtomicObj NObj) :=
    match P with
    | (a, inl P) => Some (proc[ a ](P))
    | (a, inr b) => Some (fwd[ a ](b))
    end.

  Global Instance AtomicObj_countable : Countable (AtomicObj NObj).
  Proof.
    apply (inj_countable AtomicObj_to_prime AtomicObj_from_prime).
    by intros [].
  Defined.
End AtomicObjCountable.


Instance LangName_eq_dec : EqDecision LangName.
Proof. solve_decision. Defined.

(* Is there a way to do this in less than 2 lines? *)
Instance LangName_countable : Countable LangName.
Proof.
  apply (inj_countable' (λ x, match x with
  | LangName_session_type => 0
  | LangName_flip_bit => 1
  end) (λ x, match x with
  | 0 => LangName_session_type
  | _ => LangName_flip_bit
  end)).
  by intros [].
Defined.

Instance varOrSym_eq_dec : EqDecision varOrSym.
Proof. solve_decision. Defined.

Instance varOrSym_countable : Countable varOrSym.
Proof.
  apply (inj_countable' (λ x, match x with
  | Var v => inl v
  | Sym s => inr s
  end) (λ x, match x with
  | inl v => Var v
  | inr s => Sym s
  end)).
  by intros [].
Defined.

Instance term_eq_dec : EqDecision term.
Proof. solve_decision. Defined.

Section term_countable.
  Inductive data :=
  | data_varSym (x : varOrSym)
  | data_type (A : type)
  | data_bool (b : bool)
  | data_unit.

  Instance data_eq_dec : EqDecision data.
  Proof. solve_decision. Defined.

  Instance data_countable : Countable data.
  Proof.
    apply (inj_countable' (λ x, match x with
    | data_varSym x => inl x
    | data_type A => inr (inl A)
    | data_bool b => inr (inr (inl b))
    | data_unit => inr (inr (inr ()))
    end) (λ x, match x with
    | inl x => data_varSym x
    | inr (inl A) => data_type A
    | inr (inr (inl b)) => data_bool b
    | inr (inr (inr ())) => data_unit
    end)).
    by intros [].
  Defined.

  Definition term_to_gentree (P : term) : gen_tree data.
  Proof.
    refine (let mkVarSym vs := GenLeaf (data_varSym vs) in _).
    refine (let mkVar v := mkVarSym (Var v) in _).
    refine (let mkType A := GenLeaf (data_type A) in _).
    refine (let mkBool b := GenLeaf (data_bool b) in _).
    induction P.
    - apply GenNode; [exact 0|by refine [mkVarSym src]].
    - apply GenNode; [exact 1|by refine [IHP1; IHP2; mkVar x; mkType A]].
    - apply GenNode; [exact 2|by refine [GenLeaf data_unit]].
    - apply GenNode; [exact 3|by refine [mkVar x; IHP]].
    - apply GenNode; [exact 4|by refine [mkVar y; IHP]].
    - apply GenNode; [exact 5|by refine [mkVarSym x; mkVarSym y; IHP]].
    - apply GenNode; [exact 6|by refine [mkVarSym y; IHP]].
    - apply GenNode; [exact 7|by refine [mkVarSym x; mkVar y; IHP]].
    - apply GenNode; [exact 8|by refine [IHP1; IHP2]].
    - apply GenNode; [exact 9|by refine [mkVarSym x; mkBool sel; IHP]].
    - apply GenNode; [exact 10|by refine [mkBool sel; IHP]].
    - apply GenNode; [exact 11|by refine [mkVarSym x; IHP1; IHP2]].
  Defined.

  Definition varSym_from (t : gen_tree data) : option varOrSym :=
    match t with
    | GenLeaf (data_varSym vs) => Some vs
    | _ => None
    end.

  Definition var_from (t : gen_tree data) : option var :=
    match varSym_from t with
    | Some (Var vs) => Some vs
    | _ => None
    end.

  Definition bool_from (t : gen_tree data) : option bool :=
    match t with
    | GenLeaf (data_bool b) => Some b
    | _ => None
    end.

  Definition type_from (t : gen_tree data) : option type :=
    match t with
    | GenLeaf (data_type A) => Some A
    | _ => None
    end.

  Definition term_from_gen_tree : gen_tree data -> option term.
  Proof.
    refine (let fix java t := match t with | GenLeaf _ => None | GenNode tag children => _ end in java).
    refine (match tag, children with
      | 0, [src] => src ← varSym_from src; mret (fwd src)
      | 1, [P1; P2; x; A] =>
        x ← var_from x;
        A ← type_from A;
        P1 ← java P1;
        P2 ← java P2;
        mret (cut P1 P2 x A)
      | 2, _ => mret send_1
      | 3, [x; P] => x ← var_from x; P ← java P; mret (recv_1 x P)
      | 4, [y; P] => y ← var_from y; P ← java P; mret (recv_lolli y P)
      | 5, [x; y; P] =>
        x ← varSym_from x;
        y ← varSym_from y;
        P ← java P;
        mret (send_lolli x y P)
      | 6, [y; P] => y ← varSym_from y; P ← java P; mret (send_tensor y P)
      | 7, [x; y; P] =>
        x ← varSym_from x;
        y ← var_from y;
        P ← java P;
        mret (recv_tensor x y P)
      | 8, [P1; P2] => P1 ← java P1; P2 ← java P2; mret (recv_with P1 P2)
      | 9, [x; sel; P] =>
        x ← varSym_from x;
        sel ← bool_from sel;
        P ← java P;
        mret (send_with x sel P)
      | 10, [sel; P] =>
        sel ← bool_from sel;
        P ← java P;
        mret (send_plus sel P)
      | 11, [x; P1; P2] =>
        x ← varSym_from x;
        P1 ← java P1;
        P2 ← java P2;
        mret (recv_plus x P1 P2)
      | _, _ => None end).
  Defined.

  Global Instance term_countable : Countable term.
  Proof.
    refine (inj_countable term_to_gentree term_from_gen_tree _).
    intros t. induction t.
    all: simpl; try rewrite IHt; try rewrite IHt1, IHt2; try done.
  Defined.
End term_countable.

Instance flipbit_type_eq_dec : EqDecision flipbit_type.
Proof. solve_decision. Defined. 

Instance flipbit_countable : Countable flipbit_type.
Proof. eapply (inj_countable' (λ x, match x with
  | TToRecv  => 0
  | TRecved1 => 1
  | TRecved2 => 2
  | TSentBit => 3
  end) (λ x, match x with
  | 0 => TToRecv
  | 1 => TRecved1
  | 2 => TRecved2
  | _ => TSentBit
  end)); by intros [].
Defined.
