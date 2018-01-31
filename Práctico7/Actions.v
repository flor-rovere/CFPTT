(*******************************************************************
 * Florencia Rovere
 ******************************************************************)

Load State.

Section Actions.

Inductive Action :=
   read : vadd -> Action
 | write : vadd -> value -> Action
 | chmod : Action.

(* Actions Semantics. *)

Definition va_mapped_to_ma (s: state) (vad: vadd) (mad: madd) : Prop :=
  exists (o : os) (patoma : padd -> option madd) (mad' : madd) (pg : page) (vatoma : vadd -> option madd),
    oss s (active_os s) = Some o
    /\ hypervisor s (active_os s) = Some patoma
    /\ patoma (curr_page o) = Some mad'
    /\ memory s mad' = Some pg
    /\ PT vatoma = page_content pg
    /\ vatoma vad = Some mad.

Definition Pre_Read (s : state) (vad : vadd) :=
  os_accesible ctx vad = true
  /\ aos_activity s = running
  /\ (exists (mad : madd) (pg : page),
        va_mapped_to_ma s vad mad
        /\ memory s mad = Some pg
        /\ is_RW (page_content pg)).

Definition Pre_Write (s : state) (vad : vadd) (val : value) := Pre_Read s vad.

Definition Pre_Chmod (s : state) :=
  aos_activity s = waiting
  /\ exists (o : os),
       oss s (active_os s) = Some o
       /\ hcall o = None.

Definition Pre (s : state) (a : Action) : Prop :=
  match a with
    read vad => Pre_Read s vad
  | write vad val => Pre_Write s vad val
  | chmod =>Pre_Chmod s
  end.

Definition Post_Read (s : state) (vad : vadd) (s' : state) := s' = s.

Definition aux (mem : system_memory) (mad : madd) (pg : page) :=
  fun (mad': madd) => if (madd_eq mad mad') then Some pg else mem mad.

Definition Post_Write (s : state) (vad : vadd) (val : value) (s' : state) :=
  exists (mad : madd),
    va_mapped_to_ma s vad mad
    /\ memory s' = aux (memory s) mad (Page (RW (Some val)) (Os (active_os s)))
    /\ active_os s' = active_os s
    /\ aos_exec_mode s' = aos_exec_mode s
    /\ aos_activity s' = aos_activity s
    /\ oss s' = oss s
    /\ hypervisor s' = hypervisor s
    /\ (forall mad' : madd,
          mad' <> mad
          /\ memory s mad' = memory s' mad').

Definition Post_Chmod (s s' : state) :=
  (trusted_os ctx (active_os s) = true
   /\ aos_exec_mode s = usr
   /\ aos_exec_mode s' = svc
   /\ aos_activity s = waiting
   /\ aos_activity s' = running
   /\ active_os s' = active_os s
   /\ oss s' = oss s
   /\ hypervisor s' = hypervisor s
   /\ memory s' = memory s)
  \/ (trusted_os ctx (active_os s) = false
      /\ aos_exec_mode s = svc
      /\ aos_exec_mode s' = usr
      /\ aos_activity s = waiting
      /\ aos_activity s' = running
      /\ active_os s' = active_os s
      /\ oss s' = oss s
      /\ hypervisor s' = hypervisor s
      /\ memory s' = memory s).

Definition Post (s : state) (a : Action) (s' : state) : Prop :=
  match a with
    read vad => Post_Read s vad s'
  | write vad val => Post_Write s vad val s'
  | chmod => Post_Chmod s s'
  end.

(* One-step execution. *)

Inductive one_step_execution : state -> Action -> state -> Prop :=
  ose : forall (s s' : state) (a : Action),
          valid_state s -> Pre s a -> Post s a s' -> one_step_execution s a s'.


(* Invariance of valid state. *)
Ltac manys :=
  repeat match goal with
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : exists x, _ |- _ ] => elim H; intros; clear H
  end.

Lemma preserves_valid_states : forall (s s': state) (a : Action),
  one_step_execution s a s'
  -> valid_state_iii s'.
Proof.
intros.
inversion_clear H.
inversion_clear H0.
unfold valid_state_iii.
intro.
destruct a.
- inversion H2.
  apply H.
  rewrite -> H4 in H0.
  assumption.
- inversion H2.
  manys.
  rewrite H7.
  apply H.
  rewrite <- H6.
  rewrite <- H8.
  assumption.
- inversion H2 ; manys.
  + assumption.
  + elim H0 ; intros.
    * manys.
      rewrite -> H9 in H14.
      rewrite H14 in H4.
      discriminate.
    * rewrite -> H14 in H8.
      discriminate.
Qed.

(* Read isolation. *)

Lemma read_isolation : forall (s s' : state) (vad : vadd),
  one_step_execution s (read vad) s'
  -> exists mad : madd,
       va_mapped_to_ma s vad mad
       /\ exists pg : page,
            memory s mad = Some pg
            /\ page_owned_by pg = Os (active_os s).
Proof.
intros.
inversion_clear H.
inversion_clear H1.
manys.
elim H3.
intros.
manys.
exists x.
split.
- assumption.
- exists x0.
  split.
  + assumption.
  + inversion_clear H0.
    inversion_clear H3.
    manys.
    elim H3 with (pg := x0) (patoma := x7) (pad := curr_page x6) (mad := x8).
    intros.
    manys.
    assumption.
Qed.
End Actions.