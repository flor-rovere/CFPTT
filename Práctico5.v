Section Ejercicio5.
(*1*)
Definition Var := nat.

Inductive BoolExpr :=
    BEVar : Var -> BoolExpr
  | BEBool : bool -> BoolExpr
  | BAnd : BoolExpr -> BoolExpr -> BoolExpr
  | BNot : BoolExpr -> BoolExpr.

(*2*)
Definition Valor := bool.

Definition Memoria := Var -> Valor.

Definition lookup (mem : Memoria) (v : Var) : Valor := mem v.

Inductive BEval : BoolExpr -> Memoria -> Valor -> Prop :=
   evar : forall (v : Var) (m : Memoria), BEval (BEVar v) m (lookup m v)
 | eboolt : forall (m : Memoria), BEval (BEBool true) m true
 | eboolf : forall (m : Memoria), BEval (BEBool false) m false
 | eandl : forall (e1 e2 : BoolExpr) (m : Memoria), BEval e1 m false -> BEval (BAnd e1 e2) m false
 | eandr : forall (e1 e2 : BoolExpr) (m : Memoria), BEval e2 m false -> BEval (BAnd e1 e2) m false
 | eandrl : forall (e1 e2 : BoolExpr) (m : Memoria), BEval e1 m true -> BEval e2 m true -> BEval (BAnd e1 e2) m true
 | enott : forall (e : BoolExpr) (m : Memoria), BEval e m true -> BEval (BNot e) m false
 | enotf : forall (e : BoolExpr) (m : Memoria), BEval e m false -> BEval (BNot e) m true.

(*3*)
Theorem a5 : forall (m : Memoria), ~BEval (BEBool true) m false.
Proof.
intros m hip.
inversion hip.
Qed.

Theorem b5 : forall (e1 e2 : BoolExpr) (m : Memoria) (w : Valor), BEval e1 m true -> BEval e2 m w -> BEval (BAnd e1 e2) m w.
Proof.
intros e1 e2 m w h1 h2.
induction w; constructor; assumption.
Qed.

Theorem c5 : forall (e : BoolExpr) (m : Memoria) (w1 w2 : Valor), BEval e m w1 -> BEval e m w2 -> w1 = w2.
Proof.
intros e m w1 w2 h1 h2.
induction e.
- inversion_clear h1; inversion_clear h2; reflexivity.
- destruct b; inversion_clear h1; inversion_clear h2; reflexivity.
- inversion h1.
  inversion h2; auto.
  + rewrite -> H2.
    rewrite -> H8.
    apply IHe1; [rewrite <- H2| rewrite <- H8]; assumption.
  + rewrite -> H2.
    apply IHe2; [rewrite <- H2| inversion h2]; assumption.
  + inversion h2; auto.
    * rewrite -> H3, H8.
      apply IHe1; [rewrite <- H3| rewrite <- H8]; assumption.
    * rewrite -> H3, H8.
      apply IHe2; [rewrite <- H3| rewrite <- H8]; assumption.
- inversion h1.
  inversion h2; auto.
  + rewrite -> H2, H6.
    apply IHe; [rewrite <- H2| rewrite <- H6]; assumption.
  + inversion h2; auto.
    * rewrite -> H2, H6.
      apply IHe; [rewrite <- H2| rewrite <- H6]; assumption.
Qed.

(*4*)
Fixpoint beval (m : Memoria) (e : BoolExpr) {struct e} : Valor :=
  match e with
    BEVar v => lookup m v
  | BEBool b => b
  | BAnd e1 e2 => if beval m e1
                  then beval m e2
                  else false
  | BNot e => if beval m e
              then false
              else true
  end.

(*5*)
Theorem e5 : forall (e : BoolExpr) (m : Memoria), BEval e m (beval m e).
Proof.
intros e m.
induction e.
- constructor.
- simpl.
  destruct b;constructor.
- simpl.
  destruct (beval m e1).
  + destruct (beval m e2); constructor; assumption.
  + constructor; assumption.
- simpl.
  destruct (beval m e); constructor; assumption.
Qed.
End Ejercicio5.

Section Ejercicio6y7.
(*6.1*)
Inductive Instr :=
    Skip : Instr
  | IVar : Var -> BoolExpr -> Instr
  | IIf : BoolExpr -> Instr -> Instr -> Instr
  | IWhile : BoolExpr -> Instr -> Instr
  | Repeat : nat  -> Instr -> Instr
  | IBegin : LInstr -> Instr
with LInstr :=
  | LIEmpty : LInstr
  | LICons : Instr -> LInstr -> LInstr.

(*6.2*)
Notation "v 'Is' e" := (IVar v e) (at level 60).
Notation "'If' e 'Then' i1 'Else' i2" := (IIf e i1 i2) (at level 60).
Notation "'While' e 'Do' i" := (IWhile e i) (at level 60).
Notation "'Begin' li 'End'" := (IBegin li) (at level 60).

Notation "[]" := LIEmpty.
Infix ";" := LICons (at level 80, right associativity).

Definition PP (v1 v2: Var) :=
  Begin
    (v1 Is (BEBool true);
    (v2 Is (BNot (BEVar v1));
    []))
  End.

Definition swap (v1 v2 aux : Var) :=
  Begin
    (aux Is (BEVar v1);
    (v1 Is (BEVar v2);
    (v2 Is (BEVar aux);
    [])))
  End.

(*6.3*)
Require Import Coq.Arith.EqNat.

Definition update (mem : Memoria) (var : Var) (val : Valor) :=
  fun var2 => if beq_nat var var2
              then val
              else mem var2.

Check (update: Memoria -> Var -> Valor -> Memoria).

(*6.4*)
Theorem a6 : forall (var : Var) (val : Valor) (mem : Memoria), lookup (update mem var val) var = val.
Proof.
intros var val mem.
unfold lookup.
unfold update.
rewrite <- beq_nat_refl.
reflexivity.
Qed.

(*6.5*)
Theorem b6 : forall (var1 var2 : Var) (val : Valor) (mem : Memoria), var1 <> var2 -> lookup (update mem var1 val) var2 = lookup mem var2.
Proof.
intros var1 var2 val mem hip.
unfold lookup.
unfold update.
rewrite <- beq_nat_false_iff in hip.
rewrite -> hip.
reflexivity.
Qed.

(*7.1*)
Inductive Execute : Instr -> Memoria -> Memoria -> Prop :=
    xAss : forall (e : BoolExpr) (mem : Memoria) (var : Var) (val : Valor), BEval e mem val -> Execute (var Is e) mem (update mem var val)
  | xSkip : forall (mem : Memoria), Execute (Skip) mem mem
  | xIFthen : forall (e : BoolExpr) (mem1 mem2 : Memoria) (i1 i2 : Instr), BEval e mem1 true -> Execute i1 mem1 mem2 -> Execute (If e Then i1 Else i2) mem1 mem2
  | xIFelse : forall (e : BoolExpr) (mem1 mem2 : Memoria) (i1 i2 : Instr), BEval e mem1 false -> Execute i2 mem1 mem2 -> Execute (If e Then i1 Else i2) mem1 mem2
  | xWhileTrue : forall (e : BoolExpr) (mem1 mem2 mem3 : Memoria) (i : Instr), BEval e mem1 true -> Execute i mem1 mem2 -> Execute (While e Do i) mem2 mem3 -> Execute (While e Do i) mem1 mem3
  | xWhileFalse : forall (e : BoolExpr) (mem : Memoria) (i : Instr), BEval e mem false -> Execute (While e Do i) mem mem
  | xRepeat0 : forall (i : Instr) (mem : Memoria), Execute (Repeat 0 i) mem mem
  | xRepeatS : forall (i : Instr) (mem1 mem2 mem3 : Memoria) (n : nat), Execute i mem1 mem2 -> Execute (Repeat n i) mem2 mem3 -> Execute (Repeat (S n) i) mem1 mem3
  | xBeginEnd : forall (li : LInstr) (mem1 mem2 : Memoria), ExecuteList li mem1 mem2 -> Execute (Begin li End) mem1 mem2
with ExecuteList : LInstr -> Memoria -> Memoria -> Prop :=
    xEmptyBlock : forall (mem : Memoria), ExecuteList [] mem mem
  | xNext : forall (i : Instr) (li : LInstr) (mem1 mem2 mem3 : Memoria), Execute i mem1 mem2 -> ExecuteList li mem2 mem3 -> ExecuteList (i ; li) mem1 mem3.

(*7.2*)
Theorem a7 : forall (i1 i2 : Instr) (mem1 mem2 : Memoria), Execute (If (BNot (BEBool false)) Then i1 Else i2) mem1 mem2 -> Execute (If (BEBool false) Then i2 Else i1) mem1 mem2.
Proof.
intros i1 i2 mem1 mem2 hip.
apply xIFelse.
- constructor.
- inversion hip.
  + assumption.
  + inversion H4.
    inversion H7.
Qed.

(*7.3*)
Theorem b7 : forall (i1 i2 : Instr) (mem1 mem2 : Memoria) (b : bool), Execute (If (BNot (BEBool b)) Then i1 Else i2) mem1 mem2 -> Execute (If (BEBool b) Then i2 Else i1) mem1 mem2.
Proof.
intros i1 i2 mem1 mem2 b hip.
destruct b.
- constructor.
  + constructor.
  + inversion hip.
    * inversion H4.
      inversion H7.
    * assumption.
- exact (a7 i1 i2 mem1 mem2 hip).
Qed.

(*7.4*)
Theorem c7 : forall (i : Instr) (mem1 mem2 : Memoria), Execute (While (BEBool false) Do i) mem1 mem2 -> mem1 = mem2.
Proof.
intros i mem1 mem2 hip.
inversion hip.
- inversion H1.
- reflexivity.
Qed.

(*7.5*)
Theorem d7 : forall (i : Instr) (b : bool) (mem1 mem2 : Memoria), Execute (Begin (If (BEBool b) Then i Else Skip);(While (BEBool b) Do i;[]) End) mem1 mem2 -> Execute (While (BEBool b) Do i) mem1 mem2.
Proof.
intros i b mem1 mem2 hip.
inversion_clear hip.
inversion_clear H.
inversion_clear H1.
inversion H2.
inversion_clear H0.
- rewrite -> H4 in H.
  exact (xWhileTrue (BEBool b) mem1 mem3 mem2 i H1 H5 H).
- inversion H5.
  rewrite -> H4 in H.
  assumption.
Qed.

(*7.6*)
Theorem e7 : forall (i : Instr) (n : nat) (mem1 mem2 : Memoria), Execute (Begin i;Repeat n i; [] End) mem1 mem2 -> Execute (Repeat (S n) i) mem1 mem2.
Proof.
intros i n mem1 mem2 hip.
inversion_clear hip.
inversion_clear H.
inversion_clear H1.
apply (xRepeatS i mem1 mem3 mem2 n).
- assumption.
- inversion H2.
  rewrite -> H4 in H.
  assumption.
Qed.

(*7.7*)
Theorem f7 : forall (n1 n2 : nat) (i : Instr) (mem1 mem2 mem3 : Memoria), Execute (Repeat n1 i) mem1 mem2 -> Execute (Repeat n2 i) mem2 mem3 -> Execute (Repeat (n1+n2) i) mem1 mem3.
Proof.
induction n1; intros n2 i mem1 mem2 mem3 hip1 hip2.
inversion hip1.
- rewrite -> (plus_O_n n2).
  assumption.
- inversion hip2.
  + rewrite <- (plus_n_O (S n1)).
    rewrite <- H3.
    assumption.
  + inversion hip1.
    simpl.
    apply (xRepeatS i mem1 mem7 mem3 (n1 + S n) H7).
    rewrite <- H in hip2.
    exact (IHn1 (S n) i mem7 mem2 mem3 H10 hip2).
Qed.

(*7.8*)
Theorem g7 : forall (mem1 mem2 : Memoria) (var1 var2 : Var), var2 <> var1 -> Execute (PP var1 var2) mem1 mem2 -> BEval (BEVar var1) mem2 true /\ BEval (BEVar var2) mem2 false.
Proof.
intros mem1 mem2 var1 var2 hip1 hip2.
inversion_clear hip2.
inversion_clear H.
inversion H1.
inversion H0.
inversion H6.
rewrite <- H14.
inversion H11.
rewrite <- H10 in H3.
inversion H3.
inversion H20.
split.
- rewrite <- H16.
  rewrite <- (a6 var1 true mem1) at 2.
  rewrite <- (b6 var2 var1 false (update mem1 var1 true) hip1).
  constructor.
- rewrite <- (a6 var2 false (update mem1 var1 val)) at 2.
  constructor.
- rewrite <- H16 in H22.
  inversion H22.
  unfold lookup in H28.
  unfold update in H28.
  rewrite <- beq_nat_refl in H28.
  discriminate.
Qed.
End Ejercicio6y7.