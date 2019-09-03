Require Import Coq.Setoids.Setoid.

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
rewrite <- H3 at 2.
rewrite <- H3 at 1.

rewrite H3.
auto.
