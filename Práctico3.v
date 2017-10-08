Definition o_forall : forall A B C : Set, (A -> B) -> (B -> C) -> A -> C := fun A B C f g (a:A) => (g (f a)).

Section Ejercicio4.
Variable A: Set.

Definition id : A -> A := fun a => a.

Infix "O" := (o_forall A A A) (at level 80, right associativity).

Theorem e4a : forall x:A, (id O id) x = id x.
Proof.
intro.
unfold id.
unfold o_forall.
reflexivity.
Qed.

Theorem e4b : forall x:A, (id O id) x = id x.
Proof.
intro.
cbv delta.
simpl.
reflexivity.
Qed.

Theorem e4c : forall x:A, (id O id) x = id x.
Proof.
intro.
compute.
reflexivity.
Qed.

End Ejercicio4.


Section Ejercicio5.

(* 5.1 *)
Definition opI (A : Set) (x : A) := x.

Definition opK (A : Set) (B : Set) (x : A) (y : B) := x.

Definition opS (A : Set) (B : Set) (C : Set) (f : A -> (B -> C)) (g : A -> B) (x : A) := (f x) (g x).

(* 5.2 *)
Lemma e52 : forall A B : Set, opS A (B -> A) A (opK A (B -> A)) (opK A B) = opI A.
Proof.
cbv delta beta.
reflexivity.
Qed.

End Ejercicio5.


Section Ejercicio10.

Parameter Array : Set -> nat -> Set.
Parameter emptyA : forall X : Set, Array X 0.
Parameter addA : forall (X : Set) (n : nat), X -> Array X n -> Array X (S n).

Parameter Matrix : Set -> nat -> Set.
Parameter emptyM : forall X : Set, Matrix X 0.
Parameter addM : forall (X : Set) (n : nat), Matrix X n -> Array X (S n) -> Matrix X (S n).

Definition A1 := addA nat 0 1 (emptyA nat). (* arreglo de un elemento *)
Definition A1bis := addA nat 0 2 (emptyA nat). (* arreglo de un elemento *)
Definition A1bisbis := addA nat 0 3 (emptyA nat). (* arreglo de un elemento *)
Definition A2 := addA nat 1 2 A1bis. (* arreglo de dos elementos *)
Definition A2bis := addA nat 1 3 A1bisbis. (* arreglo de dos elementos *)
Definition A3 := addA nat 2 3 A2bis. (* arreglo de tres elementos *)
Check A3.

Definition M1 := addM nat 0 (emptyM nat) A1. (* matriz de dos columnas *)
Definition M2 := addM nat 1 M1 A2. (* matriz de dos columnas *)
Definition M3 := addM nat 2 M2 A3. (* matriz de tres columnas *)

Check M3.

End Ejercicio10.


Section Ejercicio11.

Parameter ABNat : forall n : nat, Set.
Parameter emptyAB : ABNat 0.
Parameter addAB : forall n : nat, nat -> ABNat n -> ABNat n -> ABNat (S n).

Definition AB1 := addAB 0 7 emptyAB emptyAB. (* \\u00e1rbol de altura 1 *)
Definition AB2 := addAB 1 3 AB1 AB1.

Check AB2.

Parameter ABNat_forall : forall (n : nat) (s : Set), Set.
Parameter emptyAB_forall : forall (s : Set), ABNat_forall 0 s.
Parameter addAB_forall : forall (s : Set) (n : nat), s -> ABNat_forall n s -> ABNat_forall n s -> ABNat_forall (S n) s.

End Ejercicio11.


Section Ejercicio15.

Variable U : Set.
Variable e : U.
Variable A B : U -> Prop.
Variable P : Prop.
Variable R : U -> U -> Prop.

Lemma Ej315_1 : (forall x : U, A x -> B x) -> (forall x : U, A x) -> forall x : U, B x.
Proof.
  intros for1 for2 x; exact (for1 x (for2 x)).
Qed.

Lemma Ej315_2 : forall x : U, A x -> ~ (forall x : U, ~ A x).
Proof.
  unfold not; intros x ax all; exact (all x ax).
Qed.

Lemma Ej315_3 : (forall x : U, P -> A x) -> P -> forall x : U, A x.
Proof.
  exact (fun all p x => all x p).
Qed.

Lemma Ej315_4 : (forall x y : U, R x y) -> forall x : U, R x x.
Proof.
  exact (fun all x => all x x).
Qed.

Lemma Ej315_5 : (forall x y: U, R x y -> R y x) -> forall z : U, R e z -> R z e.
Proof.
  exact (fun all z rez => all e z rez).
Qed.

End Ejercicio15.