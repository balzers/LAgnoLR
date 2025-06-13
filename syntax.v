From Coq Require Import String.
From stdpp Require Import base tactics gmap gmultiset option.
From ST Require Import stdsharp.

Inductive type :=
| T1 | TTensor (A B : type) | TLolli (A B : type)
| TWith (A B : type) | TPlus (A B : type).

Notation "A ⊗ B" := (TTensor A B) (at level 80).
Notation "A ⊸ B" := (TLolli A B) (at level 80, right associativity).
Notation "A ⊕ B" := (TPlus A B) (at level 85).
(* A & B is renamed to A ⊛ B because neither & nor [with] seem to work *)
Notation "A ⊛ B" := (TWith A B) (at level 82).

Definition sym := nat.
Definition var := string.

(* ! or ? *)
Inductive direction := Send | Recv.

Definition direction_dual (d : direction) : direction := match d with
| Send => Recv | Recv => Send end.

Inductive payload :=
| Payload_sym (name : sym)
| Payload_choice (b : bool)
| Payload_terminate.

Definition π1 := Payload_choice true.
Definition π2 := Payload_choice false.

Inductive Action :=
| Action_silent : Action
| Action_comm : sym -> direction -> payload -> Action.

Notation "a ! b" := (Action_comm a Send b) (at level 50).
Notation "a ? b" := (Action_comm a Recv b) (at level 50).

Definition Action_dual (a : Action) : Action.
  destruct a.
  - apply Action_silent.
  - apply Action_comm. 2: by apply direction_dual. all: done.
Defined.

Inductive AtomicObj (NObj : Type) :=
| AtomicObj_proc (a : sym) (P : NObj)
| AtomicObj_fwd  (a : sym) (b : sym).

Notation "proc[ a ] P" := (AtomicObj_proc _ a P) (at level 50).
Notation "fwd[ a ] b"  := (AtomicObj_fwd _ a b) (at level 50).  

(* Identifier of a language -- so I have countable languages *)
Inductive LangName :=
| LangName_session_type
| LangName_flip_bit.

Inductive varOrSym := Var (v : var) | Sym (s : sym).

Inductive term :=
| fwd (src : varOrSym)
| cut (P1 P2 : term) (x : var) (A : type) (* x : A *)
| send_1
| recv_1 (x : var) (P : term)
| recv_lolli (y : var) (P : term)
| send_lolli (x y : varOrSym) (P : term)
| send_tensor (y : varOrSym) (P : term)
| recv_tensor (x : varOrSym) (y : var) (P : term)
| recv_with (P1 P2 : term)
| send_with (x : varOrSym) (sel : bool) (P : term)
| send_plus (sel : bool) (P : term)
| recv_plus (x : varOrSym) (P1 P2 : term).

Definition sourceCtx := gmap var type.
Definition substObj := gmap var sym.

Inductive typed_term : sourceCtx -> term -> type -> Prop :=
| Typed_fwd x A : typed_term {[x := A]} (fwd (Var x)) A
| Typed_cut Γ1 Γ2 P1 P2 x A B :
  Γ1 ##ₘ Γ2 -> x ∉ Γ2 ->
  typed_term Γ1 P1 A ->
  typed_term (<[x := A]> Γ2) P2 B ->
  typed_term (Γ1 ∪ Γ2) (cut P1 P2 x A) B
| Typed_send_1 : typed_term ∅ send_1 T1
| Typed_recv_1 Γ x P A :
  x ∉ Γ -> typed_term Γ P A ->
  typed_term (<[x := T1]> Γ) (recv_1 x P) A
| Typed_recv_lolli Γ y P A B :
  y ∉ Γ -> typed_term (<[y := A]> Γ) P B ->
  typed_term Γ (recv_lolli y P) (A ⊸ B)
| Typed_send_lolli Γ x y P A B C:
  x ∉ Γ -> y ∉ Γ -> x ≠ y -> typed_term (<[x := B]> Γ) P C ->
  typed_term (<[x := A ⊸ B]> (<[y := A]> Γ)) (send_lolli (Var x) (Var y) P) C
| Typed_send_tensor Γ y P A B :
  y ∉ Γ -> typed_term Γ P B ->
  typed_term (<[y := A]> Γ) (send_tensor (Var y) P) (A ⊗ B)
| Typed_recv_tensor Γ x y P A B C :
  x ∉ Γ -> y ∉ Γ -> x ≠ y -> typed_term (<[y := A]> (<[x := B]> Γ)) P C ->
  typed_term (<[x := A ⊗ B]> Γ) (recv_tensor (Var x) y P) C
| Typed_recv_with Γ P1 P2 A B :
  typed_term Γ P1 A -> typed_term Γ P2 B ->
  typed_term Γ (recv_with P1 P2) (A ⊛ B)
| Typed_send_with Γ x (sel : bool) P A B C:
  x ∉ Γ -> typed_term (<[x := if sel then A else B]> Γ) P C ->
  typed_term (<[x := A ⊛ B]> Γ) (send_with (Var x) sel P) C
| Typed_send_plus Γ (sel : bool) P A B :
  typed_term Γ P (if sel then A else B) ->
  typed_term Γ (send_plus sel P) (A ⊕ B)
| Typed_recv_plus Γ x P1 P2 A B C :
  x ∉ Γ -> typed_term (<[x := A]> Γ) P1 C -> typed_term (<[x := B]> Γ) P2 C ->
  typed_term (<[x := A ⊕ B]> Γ) (recv_plus (Var x) P1 P2) C.

Inductive flipbit_type :=
| TToRecv | TRecved1 | TRecved2 | TSentBit.
