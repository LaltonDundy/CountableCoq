Inductive Nec_Nat : Type :=
| Unit : Nec_Nat
| More : Nec_Nat -> Nec_Nat
.

Fixpoint Nec_Nat_g (a : nat) : Nec_Nat :=
match a with
| 0   => Unit
| S n => More (Nec_Nat_g n)
end .

Definition Pos_Nat := option Nec_Nat.

(*
Fixpoint Pos_Nat_f (a : Pos_Nat) : nat :=
match a with
| None          => 0
| Some x        => 1 + (Nec_Nat_f x)
end.
*)

Fixpoint Pos_Nat_g (a : nat) : Pos_Nat :=
match a with
| 0     => None
| S n   => Some (Nec_Nat_g n)
end.

Inductive Nec_Int : Type :=
| Pos : Nec_Nat -> Nec_Int
| Neg : Nec_Nat -> Nec_Int
.

Definition Pos_Int := option Nec_Int.

Definition Iso (A : Type) (B : Type) (f : A -> B) (g : B -> A) : Prop :=
    forall x : A         ,
    forall y : B         ,
    (f (g y) = y) /\ (g (f x) = x).

Definition compose { A : Type } { B : Type } { C : Type }
(f : B -> C)
(g : A -> B)
 :=  fun x => f ( g x ).

Theorem compose_assoc : 
  forall A B C D: Type,
  forall f  : A -> B,
  forall g  : B -> C,
  forall z  : C -> D,
  compose (compose z g) f = compose z ( compose g f ).
Proof.
  intros.
  unfold compose.
  auto.
Qed.

Definition reverse_app { A B : Type } (a : A) (f : A -> B) := f a.

Theorem point_free : 
  forall A B : Type,
  forall x : A,
  forall f : A -> B,
  ((fun y => f y) = f).
Proof.
  intros.
  auto.
Qed.

Lemma Iso_eq : 
  forall A B : Type,
  forall f : A -> B,
  forall g : B -> A,
  forall x y : A,
  (Iso A B f g) -> (f x = f y) -> (x = y).
Proof.
  intros.
  evar ( z : B).
  destruct H with (x := x) (y := z).
  rewrite <- H2.
  rewrite  H0.
  destruct H with (x:=y) (y:=z).
  auto.
  Unshelve.
  auto.
Qed.


Theorem Iso_Commute  :
  forall A B : Type  ,
  forall f : A -> B,
  forall g : B -> A,
  Iso A B f g -> Iso B A g f.
Proof.
  intros.
  constructor.
  destruct H with (x := y) (y := x).
  auto.
  destruct H with (x := y) (y := x).
  auto.
Qed.

Theorem Iso_Compose : 
forall A B C : Type  ,
forall f  : A -> B,
forall g  : B -> A,
forall f' : B -> C,
forall g' : C -> B,
 Iso A B f  g ->
 Iso B C f' g'->
 Iso A C (compose f' f) (compose g g').
Proof using All.
intros.
constructor.

destruct H with (x := x) (y := f x).
destruct H0 with (x := f x) (y := y).
unfold compose.
transitivity (f' (g' y)).
rewrite (Iso_eq) with (B:=C) (f:=f') (g:=g') (x:=f x) (y:= f x).

(*

Class Countable (A : Type) := {
  next     : A -> A     ;
  to_nat   : A -> nat   ;
  from_nat : nat -> A   ;
  iso_nat  : Iso A nat to_nat from_nat;
  eq_next  : forall  x : A, 
             to_nat (next x) = 1 + (to_nat x)
              /\
             forall  n : nat, 
             from_nat (S n) = next (from_nat n)
}.

Instance Nec_Nat_Count : Countable Nec_Nat := {
next   := More ;
to_nat := (fun a => match a with
| Unit   => 0
| More x => 1 + (to_nat x)
end);
from_nat := (fun a => 
match a with
| 0   => Unit
| S n => More (from_nat n)
end)
}.
*)

(*
Module Type Countable.
  Parameter A : Type.
  Parameter Next : A -> A.
  Axiom iso_nat : Iso A nat.    
End Countable.

Module Nec_Nat_Count <: Countable.
  Definition A    := Nec_Nat.
  Definition Next := More.
  Lemma iso_nat : Iso Nec_Nat nat.
  Proof.
    intros a.
    intros n.
    refine (ex_intro _ Nec_Nat_f _).
    refine (ex_intro _ Nec_Nat_g _).
    split.
    elim n.
    elim a.
    simpl ; auto.
    intros.
    rewrite H ; auto.
    intros.
    simpl ; auto.
    elim a.
    simpl ; auto.
    intros.
    simpl.
    rewrite H ; auto.
  Qed.

Module Pos_Nat_Count <: Countable.
Definition A := Pos_Nat.
Definition Next := (fun x => match x with
    | None   => Some Unit
    | Some x => Some (More x)
    end ).
Lemma iso_nat : Iso Pos_Nat nat.
 Proof.
 cut (Nec_Nat -> nat).
*)


