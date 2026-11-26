(** * Ticks in contracts

    [Ticks.v] adds a counter to a function.  This file says how a VST
    contract speaks of that counter, and how a contract for a function
    without the counter becomes one for the function with it.

    - [ticks gv t]: the counter holds [t].
    - [with_ticks]: the form with ticks of a contract.
    - [spend_tick]: the proof step for one tick.

    The form with ticks is made from the contract's own precondition and
    postcondition, so the two forms cannot drift apart: they differ in the
    counter and in nothing else. *)

Require Import VST.floyd.proofauto.
From fvzlib.proofs.lib Require Import Ticks.

(** The counter is a global variable of type [unsigned long], owned
    whole.  It holds [t]. *)
Definition ticks {cs : compspecs} (gv : globals) (t : Z) : mpred :=
  data_at Ews tulong (Vlong (Int64.repr t)) (gv _fvz_ticks).

(** ** The form with ticks of a contract

    Take a contract with parameters of type [A], precondition [P], and
    postcondition [Q], and a cost [cost w] for each choice [w] of the
    parameters.  The form with ticks has the same parameters and two more:
    the global variables [gv] and the number [t] that the counter holds.

    - Before the call, everything [P] asks, and beside it a counter that
      holds [t], where [t] is at least the cost.
    - After the call, everything [Q] promises, and beside it the counter,
      holding [t] less the ticks used, which are at most the cost.

    So the cost is an upper bound, and the caller gets back what it did
    not use. *)
Definition with_ticks {cs : compspecs} (sig : compcert_rmaps.typesig)
    (cc : calling_convention) (A : Type) (cost : A -> Z)
    (P : A -> argsEnviron -> mpred) (Q : A -> environ -> mpred) : funspec :=
  NDmk_funspec sig cc (A * globals * Z)
    (fun '(w, gv, t) gargs =>
       !! (cost w <= t <= Int64.max_unsigned) &&
       (P w gargs * GLOBALSx [gv] (SEPx [ticks gv t]) gargs)%logic)
    (fun '(w, gv, t) rho =>
       EX used : Z,
       !! (0 <= used <= cost w) && (Q w rho * ticks gv (t - used))%logic).

(** [plain] and [ticked] are the two forms of one contract: the first is
    made of [P] and [Q] alone, and the second is [with_ticks] of the same
    [P] and [Q]. *)
Definition two_forms {cs : compspecs} (sig : compcert_rmaps.typesig)
    (cc : calling_convention) (A : Type) (cost : A -> Z)
    (plain ticked : funspec) : Prop :=
  exists (P : A -> argsEnviron -> mpred) (Q : A -> environ -> mpred),
    plain = NDmk_funspec sig cc A P Q /\
    ticked = with_ticks sig cc A cost P Q.

(** ** One tick in a proof

    Step through one tick when the counter is known to be positive.  The
    branch that jumps to the missing label is closed by contradiction. *)
Ltac spend_tick :=
  forward;
  forward_if True;
  [ exfalso;
    match goal with
    | H : Int64.repr _ = Int64.zero |- _ =>
        change Int64.zero with (Int64.repr 0) in H;
        apply repr_inj_unsigned64 in H; rep_lia
    end
  | forward; entailer!
  | forward ].
