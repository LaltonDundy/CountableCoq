Require Import Utils.

(*
  This file is a fun study of both ways in which we are able to program 
  and also how we describe numbers (and more generally, things that are countable) 
  on a more fundamental level.

  The first idea presented is that of inhabitance vs voidence as integral parts to how we think about numbers.
  That is to say, for all numbers, there either is some units, or there is None. 
  We can now make two sets for every representation of numbers: ones that contain zero or not (or also defined as inhabited or voided).

  One can make the the connection to Modal Logic where as types that are always inhabited are Neccessarily so 
  and types that are not always inhabited are only possibly so. We will use this terminology to describe our types.


  First let's describe our inhabited (non-zero) Natural numbers as 'Necessarily Naturals'.
 *)

Inductive Nec_Nat : Type :=
    | Unit : Nec_Nat
    | More : Nec_Nat -> Nec_Nat
.

(* 
    How using this definition, we can easily construct the complete Natural numbers as 'Possibly Naturals'.
*)

Definition Pos_Nat := option Nec_Nat.

(* 
    On Countable numbers.
    In order to prove that something is countable, we must be able to step through each element one by one.
    Also, we must prove that the thing is isomorphic to the Natural Numbers. 

    Here is our definition of Isomorphism, some following proofs and helpers definitons.
*)


Fixpoint Nec_Nat_g (a : nat) : Nec_Nat :=
match a with
| 0   => Unit
| S n => More (Nec_Nat_g n)
end .


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


