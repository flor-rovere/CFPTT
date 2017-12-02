Section Ejercicio3.

Definition Value := bool.

Inductive BoolExpr : Set :=
    bbool : bool -> BoolExpr
  | band : BoolExpr -> BoolExpr -> BoolExpr
  | bnot : BoolExpr -> BoolExpr.


Inductive BEval : BoolExpr -> Value -> Prop :=
   ebool : forall b : bool, BEval (bbool b) (b : Value)
 | eandl : forall e1 e2 : BoolExpr, BEval e1 false -> BEval (band e1 e2) false
 | eandr : forall e1 e2 : BoolExpr, BEval e2 false -> BEval (band e1 e2) false
 | eandrl : forall e1 e2 : BoolExpr, BEval e1 true -> BEval e2 true -> BEval (band e1 e2) true
 | enott : forall e : BoolExpr, BEval e true -> BEval (bnot e) false
 | enotf : forall e : BoolExpr, BEval e false -> BEval (bnot e) true.

Fixpoint beval1 (e : BoolExpr) : Value :=
  match e with
    bbool b => b
  | band e1 e2 => match beval1 e1, beval1 e2 with
                    true, true => true
                  | _, _ => false
                  end
  | bnot e1 => if beval1 e1
              then false
              else true
  end.

Fixpoint beval2 (e : BoolExpr) : Value :=
  match e with
    bbool b => b
  | band e1 e2 => match beval2 e1 with
                    false => false
                  | _ => beval2 e2
                  end
  | bnot e1 => if beval2 e1
              then false
              else true
  end.

(*1*)
Lemma beval1C : forall e : BoolExpr, {b : Value | BEval e b}.
Proof.
intro.
exists (beval1 e).
induction e.
- constructor.
- simpl.
  destruct (beval1 e1).
  destruct (beval1 e2).
  + constructor; assumption.
  + apply eandr; assumption.
  + constructor; assumption.
- simpl.
  destruct (beval1 e); constructor; assumption.
Qed.

Lemma beval2C : forall e : BoolExpr, {b : Value | BEval e b}.
Proof.
intro.
exists (beval2 e).
induction e.
- constructor.
- simpl.
  destruct (beval2 e1).
  destruct (beval2 e2).
  + constructor; assumption.
  + apply eandr; assumption.
  + constructor; assumption.
- simpl.
  destruct (beval2 e); constructor; assumption.
Qed.

(*2*)
Hint Constructors BEval.
Lemma beval1CBis : forall e : BoolExpr, {b : Value | BEval e b}.
Proof.
intro.
exists (beval1 e).
induction e.
- auto.
- simpl.
  destruct (beval1 e1); auto.
  destruct (beval1 e2); auto.
- simpl.
  destruct (beval1 e); auto.
Qed.

Lemma beval2CBis : forall e : BoolExpr, {b : Value | BEval e b}.
Proof.
intro.
exists (beval2 e).
induction e.
- auto.
- simpl.
  destruct (beval2 e1); auto.
  destruct (beval2 e2); auto.
- simpl.
  destruct (beval2 e); auto.
Qed.
End Ejercicio3.

Extraction Language Haskell.
Extraction "/Users/flor.rovere/Desktop/beval1CBis_function" beval1CBis.

Extraction Language Haskell.
Extraction "/Users/flor.rovere/Desktop/beval2CBis_function" beval2CBis.

Extract Inductive bool => "Bool" ["true" "false"].
Extraction Language Haskell.
Extraction "/Users/flor.rovere/Desktop/beval1CBis_function2" beval1CBis.

Extraction Language Haskell.
Extraction "/Users/flor.rovere/Desktop/beval2CBis_function2" beval2CBis.

Section Ejercicio5.
(*1*)
Inductive Le : nat -> nat -> Prop :=
    Le0 : forall n, Le 0 n
  | LeS : forall n m, Le n m -> Le (S n) (S m).

Inductive Gt : nat -> nat -> Prop :=
    Gt0 : forall n, Gt (S n) 0
  | GtS : forall n m, Gt n m -> Gt (S n) (S m).

Hint Constructors Le.
Hint Constructors Gt.

(*2*)
Function leBool (n m : nat) : bool :=
  match n, m with
    0, _ => true
  | S n1, 0 => false
  | S n1, S m1 => leBool n1 m1
  end.

Lemma Le_Gt_dec : forall n m : nat, {(Le n m)} + {(Gt n m)}.
Proof.
intros.
functional induction (leBool n m).
- left; auto.
- right; auto.
- elim IHb; intros; [left | right]; auto.
Qed.

(*3*)
Require Import Omega.
Lemma le_gt_dec : forall n m : nat, {(le n m)} + {(gt n m)}.
Proof.
intros.
functional induction (leBool n m).
- left; omega.
- right; omega.
- elim IHb; intros; [left | right]; omega.
Qed.
End Ejercicio5.

Section Ejercicio6.
Require Import Omega.
Require Import DecBool.
Require Import Compare_dec.
Require Import Plus.
Require Import Mult.

Definition spec_res_nat_div_mod (a b : nat) (qr : nat * nat) :=
  match qr with
    (q, r) => (a = b * q + r) /\ r < b
  end.

Definition nat_div_mod :
  forall a b : nat, not (b = 0) -> {qr : nat * nat | spec_res_nat_div_mod a b qr}.
Proof.
intros a b hip.
unfold spec_res_nat_div_mod.
induction a.
- exists (0,0).
  omega.
- elim IHa; intros.
  destruct x.
  case (lt_dec n0 (b-1)); intros.
  + exists (n, n0+1).
    omega.
  + exists (n + 1, 0).
    split.
    * { elim p; intros.
        assert (n0 = b-1).
        - omega.
        - rewrite -> H1 in H.
          rewrite H.
          rewrite -> mult_plus_distr_l.
          omega.
      }
    * omega.
Qed.
End Ejercicio6.

Section Ejercicio7.
Inductive tree (A : Set) : Set :=
    leaf : tree A
  | node : A -> tree A -> tree A -> tree A.

Inductive tree_sub (A : Set) (t : tree A) : tree A -> Prop :=
    tree_sub1 : forall (t1 : tree A) (x : A), tree_sub A t (node A x t t1)
  | tree_sub2 : forall (t1 : tree A) (x : A), tree_sub A t (node A x t1 t).

Theorem well_founded_tree_sub : forall A : Set, well_founded (tree_sub A).
Proof.
intro.
unfold well_founded; intro t.
induction t; apply Acc_intro; intros; inversion H; auto.
Qed.
End Ejercicio7.

Section Ejercicio8.
(*1*)
Function size (b : BoolExpr) : nat :=
  match b with
    bbool _ => 0
  | band l r => 1 + (size l) + (size r)
  | bnot b => 1 + (size b)
  end.

Definition elt (e1 e2 : BoolExpr) := size e1 < size e2.

(*2*)
Require Import Wf_nat.
Require Import Inverse_Image.

Theorem well_founded_elr : well_founded elt.
Proof.
apply (wf_inverse_image BoolExpr nat lt size).
apply lt_wf.
Qed.
End Ejercicio8.