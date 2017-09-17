(* Practica 1 *)

Section P1.
Variables A B C:Prop.

(* Ej 5.1 *)
Theorem e51: (A->B)-> ~B-> ~A.
Proof.
intros f nb.
unfold not in *.
intro a.
exact (nb (f a)).
Qed.

(* Ej 5.2 *)
Theorem e52: ~(A/\~A).
Proof.
unfold not in *.
intro af.
elim af.
intros a f.
exact (f a).
Qed.

(* Ej 5.3 *)
Theorem e53: (A->B)-> ~(A/\~B).
Proof.
unfold not in *.
intros f ag.
elim ag.
intros a g.
exact (g (f a)).
Qed.

(* Ej 5.4 *)
Theorem e54: (A/\B)->~(A->~B).
Proof.
unfold not in *.
intros ab f.
elim ab.
intros a b.
exact (f a b).
Qed.

(* Ej 5.5 *)
Theorem e55: (~A /\ ~~A) -> False.
Proof.
unfold not in *.
intro fg.
elim fg.
intros f g.
exact (g f).
Qed.

(* Ej 6.1 *)
Theorem e61: (A\/B) -> ~(~A/\~B).
Proof.
unfold not in *.
intros ab fg.
elim fg.
intros f g.
elim ab.
- exact f.
- exact g.
Qed.

(* Ej 6.2 *)
Theorem e62: A\/B <-> B\/A.
Proof.
unfold iff.
split.
- intro ab.
  elim ab.
  + intro a.
    right.
    assumption.
  + intro b.
    left.
    assumption.
- intro ba.
  elim ba.
  + intro b.
    right.
    assumption.
  + intro a.
    left.
    assumption.
Qed.

(* Ej 6.3 *)
Theorem e63: A\/B -> ((A->B)->B).
Proof.
intros ab f.
elim ab.
- intro a.
  exact (f a).
- intro b.
  assumption.
Qed.

End P1.

Section Logica_Clasica.
Variables A B C: Prop.

Require Import Classical.
Check classic.

(* Ej 8.1 *)
Theorem e81: forall A:Prop, ~~A->A.
Proof.
intro D.
intro nnd.
elim (classic D).
- intro d.
  assumption.
- intro nd.
  absurd (~D).
  + assumption.
  + assumption.
Qed.

(* Ej 8.2 *)
Theorem e82: forall A B:Prop, (A->B)\/(B ->A).
Proof.
intros D E.
elim (classic D).
- intro d.
  right.
  intro e.
  assumption.
- intro nd.
  left.
  intro d.
  absurd D.
  + assumption.
  + assumption.
Qed.

(* Ej 8.3 *)
Theorem e83: forall A B:Prop, ~(A/\B)-> ~A \/ ~B.
Proof.
intros D E.
intro nde.
elim (classic D).
unfold not in *.
- intro d.
  right.
  intro e.
  apply nde.
  split.
  + assumption.
  + assumption.
- intro nd.
  left.
  assumption.
Qed.

End Logica_Clasica.


Section Traducciones.

(* Ej 9 *)
(* Definiciones *)
Variable NM RED CONS UTIL : Prop.

Hypothesis H1 : ~NM \/ ~RED.
Hypothesis H2 : CONS \/ ~UTIL.

Theorem ej9 : NM /\ UTIL -> CONS /\ ~RED.
Proof.
intro nmut.
split.
- elim H2.
  + intro c.
    assumption.
  + intro nu.
    elim nmut.
    intros nm ut.
    absurd UTIL.
    * assumption.
    * assumption.
- elim H1.
  + intro nnm.
    elim nmut.
    intros nm ut.
    absurd NM.
    * assumption.
    * assumption.
  + intro r.
    assumption.
Qed.

(* Ej 12 *)
(* Definiciones *)
Variable PF:Prop. (* el paciente tiene fiebre *)
Variable PA:Prop. (* el paciente tiene piel amarillenta *)
Variable PH:Prop. (* el paciente tiene hepatitis *)
Variable PR:Prop. (* el paciente tiene rubeola *)

Hypothesis Regla1: PF \/ PA -> PH \/ PR.
Hypothesis Regla2: ~PR \/ PF.
Hypothesis Regla3: PH /\ ~PR -> PA.


Theorem ej12: (~PA /\ PF) -> PR.
Proof.
intro npapf.
elim npapf.
intros npa pf.
cut (PH \/ PR).
- intro phpr.
  elim phpr.
  + intro ph.
    elim (classic PR).
    * intro pr.
      assumption.
    * { intro npr.
        cut PA.
        - intro pa.
          absurd PA.
          + assumption.
          + assumption.
        - apply Regla3.
          split.
          + assumption.
          + assumption.
      }
  + intro pr.
    assumption.
- apply Regla1.
  left.
  assumption.
Qed.

End Traducciones.