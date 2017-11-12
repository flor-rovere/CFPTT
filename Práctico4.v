Section Ejercicio1.
(*1*)
Inductive list (A : Set) : Set :=
                 nil : list A
               | cons : A -> list A -> list A.

Inductive bintree (A : Set) : Set :=
                    empty : bintree A
                  | add : A -> bintree A -> bintree A -> bintree A.

(*6*)
Inductive mirrorBin (A : Set) : bintree A -> Set :=
                      mirrorBinEmpty : mirrorBin A (empty A)
                    | mirrorBinAdd : forall (tB tC : bintree A) (b : A), mirrorBin A tB -> mirrorBin A tC -> mirrorBin A (add A b tB tC).
End Ejercicio1.


Section Ejercicio3.
(*1*)
Fixpoint sum (x y : nat) {struct y} : nat :=
  match y with
    0 => x
  | S n => S (sum x n)
  end.
End Ejercicio3.


Section Ejercicio4.
(*2*)
Fixpoint append (A : Set) (l1 l2: list A) {struct l1} : list A :=
  match l1 with
    nil _ => l2
  | cons _ x xs => cons A x (append A xs l2)
  end.

(*4*)
Fixpoint filter (A : Set) (f : A -> bool) (l : list A) : list A :=
  match l with
    nil _ => l
  | cons _ x xs => if (f x)
                   then cons A x (filter A f xs)
                   else filter A f xs
  end.

(*5*)
Fixpoint map (A B : Set) (f : A -> B) (l : list A) : list B :=
  match l with
    nil _ => nil B
  | cons _ x xs => cons B (f x) (map A B f xs)
  end.
End Ejercicio4.

Section Ejercicio5.
(*1*)
Fixpoint inverse (A : Set) (b : bintree A) : bintree A :=
  match b with
    empty _ => empty A
  | add _ x l r => add A x (inverse A r) (inverse A l)
  end.
End Ejercicio5.


Section Ejercicio9.
(*1*)
Theorem sum0 : forall n : nat, sum n 0 = n /\  sum 0 n =n.
Proof.
intro n.
split.
- reflexivity.
- induction n.
  * reflexivity.
  * simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

(*2*)
Theorem sumS : forall n m : nat, sum n (S m) = sum (S n) m.
Proof.
intros n m.
simpl.
induction m.
- reflexivity.
- simpl.
  rewrite -> IHm.
  reflexivity.
Qed.

(*3*)
Theorem sumAsoc : forall n m p : nat, sum n (sum m p) = sum (sum n m) p.
Proof.
intros n m p.
induction p.
- reflexivity.
- simpl.
  rewrite -> IHp.
  reflexivity.
Qed.

(*4*)
Theorem sumConm : forall n m : nat, sum n m = sum m n.
Proof.
intros n m.
induction m.
- simpl.
  symmetry.
  apply (sum0 n).
- rewrite <- (sumS m n).
  simpl.
  rewrite -> IHm.
  reflexivity.
Qed.
End Ejercicio9.


Section Ejercicio12.
(*1*)
Theorem L7 : forall (A B : Set) (l m : list A) (f : A -> B),
              map A B f (append A l m) = append B (map A B f l) (map A B f m).
Proof.
intros A B l m f.
elim l.
- reflexivity.
- intros a l1 hip.
  simpl.
  rewrite -> hip.
  reflexivity.
Qed.

(*2*)
Theorem L8 : forall (A : Set) (l m : list A) (P : A -> bool),
              filter A P (append A l m) = append A (filter A P l) (filter A P m).
Proof.
intros A l m P.
elim l.
- reflexivity.
- intros a l1 hip.
  simpl.
  rewrite -> hip.
  case (P a); reflexivity.
Qed.

(*3*)
Theorem L9 : forall (A : Set) (l : list A) (P : A -> bool),
              filter A P (filter A P l) = filter A P l.
Proof.
intros A l P.
elim l.
- reflexivity.
- intros a l1 hip.
  simpl.
  case (P a) eqn : hip2.
  * simpl.
    rewrite -> hip2.
    rewrite -> hip.
    reflexivity.
  * rewrite -> hip.
    reflexivity.
Qed.

(*4*)
Theorem L10 : forall (A : Set) (l m n : list A),
              append A l (append A m n) = append A (append A l m) n.
Proof.
intros A l m n.
induction l.
- reflexivity.
- simpl.
  rewrite -> IHl.
  reflexivity.
Qed.
End Ejercicio12.


Section Ejercicio14.
Theorem propinverse : forall (A : Set) (b : bintree A), mirrorBin A (inverse A b).
Proof.
intros A b.
induction b.
- simpl.
  constructor.
- constructor; assumption.
Qed.

End Ejercicio14.


Section Ejercicio17.
(*1*)
Inductive posfijo (A : Set) : list A -> list A -> Prop :=
                    emptyPos : forall (l : list A), posfijo A l l
                  | addPos : forall (l1 l2 : list A) (a : A), posfijo A l1 l2 -> posfijo A l1 (cons A a l2).

(*2*)
Theorem L11 : forall (A : Set) (l1 l2 l3 : list A),
              l2 = append A l3 l1 -> posfijo A l1 l2.
Proof.
intros A l1 l2 l3 hip.
rewrite -> hip; clear hip.
induction l3.
- simpl.
  constructor.
- simpl.
  constructor.
  assumption.
Qed.

Theorem L12 : forall (A : Set) (l1 l2 : list A),
              posfijo A l1 l2 -> exists l3:list A, l2 = append A l3 l1.
Proof.
intros A l1 l2 hip.
induction hip.
- exists (nil A).
  reflexivity.
- elim IHhip.
  intros x hip2.
  rewrite -> hip2.
  exists (cons A a x).
  reflexivity.
Qed.

(*3*)
Theorem L13 : forall (A : Set) (l1 l2 : list A),
              posfijo A l2 (append A l1 l2).
Proof.
intros A l1 l2.
induction l1.
- simpl.
  constructor.
- simpl.
  constructor.
  assumption.
Qed.

Lemma L14a : forall (A : Set) (l1 l2 : list A),
             append A l1 l2 = (nil A) -> l1 = nil A /\ l2 = nil A.
Proof.
intros A l1 l2 hip.
induction l1.
- split.
  * reflexivity.
  * assumption.
- simpl in hip.
  discriminate.
Qed.

Axiom L14b : forall (A : Set) (l1 l2 : list A),
             l2 = append A l1 l2 -> l1 = nil A.

Theorem L14 : forall (A : Set) (l1 l2 : list A),
              posfijo A l1 l2 /\ posfijo A l2 l1 -> l1 = l2.
Proof.
intros A l1 l2 hip.
elim hip; intros h1 h2; clear hip.
apply L12 in h1; apply L12 in h2.
elim h1; intros x h3; clear h1.
elim h2; intros y h4; clear h2.
rewrite h3 in h4.
rewrite L10 in h4.
apply L14b in h4.
apply L14a in h4.
elim h4; intros xnil ynil; clear h4.
rewrite -> ynil in h3.
rewrite -> h3.
reflexivity.
Qed.

Theorem L15 : forall (A : Set) (l1 l2 l3 : list A),
              posfijo A l1 l2 /\ posfijo A l2 l3 -> posfijo A l1 l3.
Proof.
intros A l1 l2 l3 hip.
elim hip; intros h1 h2; clear hip.
induction h2.
- assumption.
- constructor.
  apply IHh2.
  assumption.
Qed.

(*4*)
Fixpoint ultimo (A : Set) (l : list A) {struct l} : list A :=
  match l with
    nil _ => nil A
  | cons _ x (nil _) => cons A x (nil A)
  | cons _ x xs => ultimo A xs
  end.

(*5*)
Theorem L16 : forall (A : Set) (l : list A),
              posfijo A (ultimo A l) l.
Proof.
intros A l.
induction l.
- simpl.
  constructor.
- induction l.
  * constructor.
  * constructor.
    assumption.
Qed.

End Ejercicio17.


Section Ejercicio20.
(*1*)
Inductive ACom (A : Set) : nat -> Set :=
                 nodeACom : A -> ACom A 0
               | addACom : forall (n : nat), A -> ACom A n -> ACom A n -> ACom A (S n).

(*2*)
Fixpoint h (A : Set) (n : nat) (t : ACom A n) {struct t} :=
  match t with
    nodeACom _ _ => 1
  | addACom _ n a l r => h A n l + h A n r
  end.

(*3*)
Parameter pot : nat -> nat -> nat.
Axiom pot0 : forall n : nat, pot (S n) 0 = 1.
Axiom potS : forall m : nat, pot 2 (S m) = (pot 2 m) + (pot 2 m).

Theorem L80 : forall (A : Set) (n : nat) (t : ACom A n),
              h A n t = pot 2 n.
Proof.
intros A n t.
induction t.
- simpl.
  rewrite -> (pot0 1).
  reflexivity.
- simpl.
  rewrite -> (potS n).
  rewrite -> IHt1.
  rewrite -> IHt2.
  reflexivity.
Qed.
End Ejercicio20.