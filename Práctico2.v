Section Ejercicio3.

Variable U   : Set.
Variable A B : U -> Prop.
Variable P Q : Prop.
Variable R S : U -> U -> Prop.

Definition H1 := forall x:U, (R x x).
Definition H2 := forall x y z:U, (R x y) /\ (R x z) -> (R y z).

Lemma reflexivity: H1 -> forall x:U, R x x.
Proof.
intros all x.
apply (all x).
Qed.

Lemma symmetry: H1 /\ H2 -> forall x y:U, (R x y -> R y x).
Proof.
intros all x y rxy.
elim all;intros all1 all2; clear all.
apply (all2 x y x).
split.
- assumption.
- apply (all1 x).
Qed.

Lemma transitivity: H1 /\ H2 -> forall x y z:U, (R x y /\ R y z -> R x z).
Proof.
intros all x y z rxyryz.
elim all;intros all1 all2.
elim rxyryz; intros rxy ryz; clear rxyryz.
apply (all2 y x z).
split.
- apply (symmetry all x y).
  assumption.
- assumption.
Qed.

Theorem e231: H1 /\ H2 ->  forall x y z:U, (R x x) /\ (R x y -> R y x) /\ (R x y /\ R y z -> R x z).
Proof.
intros all x y z.
elim all; intros all1 all2.
split.
- apply (reflexivity all1 x).
- split.
  + apply (symmetry all x y).
  + apply (transitivity all x y z).
Qed.

Definition Irreflexiva := forall x:U, ~(R x x).
Definition Asimetrica := forall x y:U, (R x y) -> ~(R y x).

Lemma e232 : Asimetrica -> Irreflexiva.
Proof.
intros all x rxx.
apply (all x x rxx rxx).
Qed.

End Ejercicio3.

Section Ejercicio7.

Variable U   : Set.
Variable A B : U -> Prop.

Theorem e71: (forall x:U, ((A x) /\ (B x)))
                       -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
intros all.
split; intro x; apply (all x).
Qed.

Theorem e72: (exists x:U, (A x \/ B x))->(exists x:U, A x )\/(exists x:U, B x).
Proof.
intro ex.
elim ex; intros x ab; clear ex.
elim ab; intro abx; [left | right]; exists x; assumption.
Qed.

Theorem e73: (forall x:U, A x) \/ (forall y:U, B y) -> forall z:U, A z \/ B z.
Proof.
intros allab z.
elim allab; intro all; [left | right]; exact (all z).
Qed.

End Ejercicio7.

Section Ejercicio9.
Require Import Classical.
Variables U : Set.
Variables A : U -> Prop.

Lemma not_ex_not_forall: (~exists x :U, ~A x) -> (forall x:U, A x).
Proof.
intros nex x.
elim (classic (A x)).
- intros ax; assumption.
- intro nax.
  unfold not in *.
  assert (hip:False).
  + apply (nex).
    exists x.
    assumption.
  + elim hip.
Qed.

Lemma not_forall_ex_not: (~forall x :U, A x) -> (exists x:U,  ~A x).
Proof.
intros nall.
elim (classic (exists x:U, ~A x)).
- intro ex; assumption.
- intro nex.
  elim nall.
  apply (not_ex_not_forall).
  assumption.
Qed.

End Ejercicio9.

Section Ejercicio10.

Variable nat : Set.
Variable  O  : nat.
Variable  S  : nat -> nat.

Axiom disc   : forall n:nat, ~O=(S n).
Axiom inj    : forall n m:nat, (S n)=(S m) -> n=m.
Axiom allNat : forall n: nat, n = O \/ exists m: nat, S m = n.

Variable sum prod : nat->nat->nat.

Axiom sum0   : forall n :nat, (sum n O)=n.
Axiom sumS   : forall n m :nat, (sum n (S m))=(S (sum n m)).
Axiom prod0  : forall n :nat, (prod n O)=O.
Axiom prodS  : forall n m :nat, (prod n (S m))=(sum n (prod n m)).

Lemma L10_1: (sum (S O) (S O)) = (S (S O)).
Proof.
rewrite sumS; rewrite sum0.
reflexivity.
Qed.

Lemma L10_2: forall n :nat, ~(O=n /\ (exists m :nat, n = (S m))).
Proof.
intros n oex.
elim oex; intros o ex; clear oex.
elim ex; intros m nsx; clear ex.
apply (disc m).
transitivity n.
- assumption.
- assumption.
Qed.

Lemma prod_neutro: forall n :nat, (prod n (S O)) = n.
Proof.
intro n.
rewrite prodS; rewrite prod0.
rewrite sum0.
reflexivity.
Qed.

Lemma diff: forall n:nat, ~(S (S n))=(S O).
Proof.
intros n sss.
apply (disc n).
symmetry.
apply (inj (S n) O).
assumption.
Qed.

Lemma L10_3: forall n: nat, exists m: nat, prod n (S m) = sum n n.
Proof.
intro n.
exists (S O).
rewrite prodS; rewrite prodS; rewrite prod0.
rewrite sum0.
reflexivity.
Qed.

Lemma L10_4: forall m n: nat, n <> O -> sum m n <> O.
Proof.
intros m n nn0 s.
apply nn0.
elim (allNat n).
- intro; assumption.
- intro ex; elim ex; intros x sxn; clear ex.
  symmetry in sxn.
  rewrite sxn in s.
  rewrite sumS in s.
  absurd (S (sum m x) = O ).
  + intro ssum0.
    apply (disc (sum m x)).
    symmetry.
    assumption.
  + assumption.
Qed.

Lemma L10_5: forall m n: nat, sum m n = O -> m = O /\ n = O.
Proof.
intros m n s.
split.
- elim (allNat m).
  + intro; assumption.
  + intro ex; elim ex; intros x sxm; clear ex.
    elim (allNat n).
    * intro n0.
      rewrite n0 in s.
      rewrite sum0 in s.
      assumption.
    * { intro ex2; elim ex2; intros x2 sx2n; clear ex2.
        symmetry in sx2n.
        rewrite sx2n in s.
        rewrite sumS in s.
        absurd (S (sum m x2) = O).
        - intro ssmx2.
          apply (disc (sum m x2)).
          symmetry.
          assumption.
        - assumption.
      }
- elim (allNat n).
  + intro; assumption.
  + intro ex; elim ex; intros x sxn; clear ex.
    symmetry in sxn.
    rewrite sxn in s.
    rewrite sumS in s.
    absurd (S (sum m x) = O ).
    * intro ssum0.
      apply (disc (sum m x)).
      symmetry.
      assumption.
    * assumption.
Qed.

End Ejercicio10.