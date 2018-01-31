(*******************************************************************
 * Florencia Rovere
 ******************************************************************)

Section State.

(* Identifiers for OSs and Hypercalls. *)

Parameter os_ident : Set.
Parameter os_ident_eq : forall oi1 oi2 : os_ident, {oi1 = oi2} + {oi1 <> oi2}.

Parameter Hyperv_call: Set.

(* Memory and addresses. *)

(* Virtual addresses. *)

Parameter vadd: Set.
Parameter vadd_eq : forall va1 va2 : vadd, {va1 = va2} + {va1 <> va2}.

(* Machine adresses. *)

Parameter madd :  Set.
Parameter madd_eq : forall ma1 ma2 : madd, {ma1 = ma2} + {ma1 <> ma2}.

(* Physical adresses. *)

Parameter padd: Set.
Parameter padd_eq : forall pa1 pa2 : padd, {pa1 = pa2} + {pa1 <> pa2}.

(* Memory values. *)

Parameter value: Set.
Parameter value_eq:forall val1 val2 : value, {val1 = val2} + {val1 <> val2}.

(* Environment. *)

Record context : Set :=
  Context
    { (* A virtual adress is accessible, i.e. it is not reserved
         for the Hypervisor. *)
      ctxt_vadd_accessible: vadd -> bool;
      (* guest OSs  (Trusted/Untrusted) *)
      ctxt_oss : os_ident -> bool
    }.

(* Operating systems. *)

Record os : Set :=
  OS
    { (* Current page table. *)
      curr_page : padd;
      (* Information on whether it has a hypercall pending to be resolved. *)
      hcall : option Hyperv_call
    }.

Definition oss_map := os_ident -> option os.

(* Execution mode. *)

Inductive exec_mode := usr | svc.

Inductive os_activity := running | waiting.

(* Memory mappings. *)

Definition hypervisor_map := os_ident -> option (padd -> option madd).

Inductive content :=
   RW (v : option value)
 | PT (va_to_ma : vadd -> option madd)
 | Other.

Definition is_RW (c : content) := exists v : option value, c = RW v.

Inductive page_owner :=
   Hyp
 | Os (osi : os_ident)
 | No_Owner.

Record page : Set :=
  Page
    { page_content : content;
      page_owned_by : page_owner
    }.

Definition system_memory := madd -> option page.

(* States. *)

Record state : Set :=
  State
    {
      (* Active operating system. *)
      active_os : os_ident;
      (* Execution mode. *)
      aos_exec_mode : exec_mode;
      (* Processor mode. *)
      aos_activity : os_activity;
      (* Information of the guest OSs of the platform. *)
      oss : oss_map;
      (* Mapping from physical to machine addresses. *)
      hypervisor : hypervisor_map;
      (* Mapping that associates a page to a machine adress. *)
      memory : system_memory
    }.

(* Valid states. *)

Parameter ctx : context.

Definition os_accesible := ctxt_vadd_accessible.
Definition trusted_os := ctxt_oss.

Definition valid_state_iii (s : state) :=
  (trusted_os ctx (active_os s) = true /\ aos_activity s = running)
  \/ (aos_activity s = waiting)
  -> aos_exec_mode s = svc.

Definition valid_state_v (s : state) :=
  forall (pad : padd) (patoma : padd -> option madd) (mad : madd) (pg : page),
    hypervisor s (active_os s) = Some patoma
    /\ patoma pad = Some mad
    /\ memory s mad = Some pg
    /\ page_owned_by pg = Os (active_os s)
    /\ (forall pa pa' : padd,
          patoma pa = patoma pa' -> pa = pa').

Definition valid_state_vi (s : state) :=
  forall (vad : vadd) (vatoma : vadd -> option madd) (pg : page) (mad : madd),
    vatoma vad = Some mad
    /\ memory s mad = Some pg
    /\ page_content pg = PT vatoma
    /\ (os_accesible ctx vad = true
        -> page_owned_by pg = Os (active_os s))
    /\ (os_accesible ctx vad = false
        -> page_owned_by pg = Hyp).

Definition valid_state (s : state) :=
  valid_state_iii s
  /\ valid_state_v s
  /\ valid_state_vi s.

End State.