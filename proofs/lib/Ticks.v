(** * Tick instrumentation

    A transformation on Clight functions that adds a counter.  One tick is
    spent on entry to the function and one at the start of every loop
    iteration.  A tick tests the counter, and if it is zero jumps to a label
    that does not exist, which is a stuck state in Clight.  Otherwise it
    decrements the counter.

    VST can prove a goto only when it is unreachable.  So a VST proof about
    an instrumented function shows that the counter never runs out.

    This file contains the transformation only.  It began in the contract
    transfer spike.  What a VST proof about the instrumented code implies
    for the original is discussed in [spikes/transfer/Transfer.v], and the
    two theorems that question needs are stated in
    [spikes/transfer/TickStatements.v]. *)

From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs.
From Stdlib Require Import List String.
Import ListNotations.
Import Clightdefs.ClightNotations.
Local Open Scope string_scope.
Local Open Scope clight_scope.

(** The counter, a global of type [unsigned long]. *)
Definition _fvz_ticks : ident := $"fvz_ticks".

(** A temporary that holds the counter's value while it is tested. *)
Definition _fvz_t : ident := $"fvz_t".

(** A label that no function defines.  Jumping to it is stuck. *)
Definition _fvz_exhausted : ident := $"fvz_exhausted".

(** Spend one tick:
<<
      fvz_t = fvz_ticks;
      if (fvz_t == 0) goto fvz_exhausted;
      fvz_ticks = fvz_t - 1;
>>
    The load and the store are separate statements, as VST requires. *)
Definition tick : statement :=
  Ssequence
    (Sset _fvz_t (Evar _fvz_ticks tulong))
    (Ssequence
      (Sifthenelse
         (Ebinop Oeq (Etempvar _fvz_t tulong)
                 (Econst_long (Int64.repr 0) tulong) tint)
         (Sgoto _fvz_exhausted)
         Sskip)
      (Sassign (Evar _fvz_ticks tulong)
         (Ebinop Osub (Etempvar _fvz_t tulong)
                 (Econst_long (Int64.repr 1) tulong) tulong))).

(** Put a tick at the start of every loop iteration. *)
Fixpoint add_ticks (s : statement) : statement :=
  match s with
  | Ssequence a b => Ssequence (add_ticks a) (add_ticks b)
  | Sifthenelse e a b => Sifthenelse e (add_ticks a) (add_ticks b)
  | Sloop a b => Sloop (Ssequence tick (add_ticks a)) (add_ticks b)
  | Sswitch e cases => Sswitch e (add_ticks_cases cases)
  | Slabel l a => Slabel l (add_ticks a)
  | _ => s
  end
with add_ticks_cases (cases : labeled_statements) : labeled_statements :=
  match cases with
  | LSnil => LSnil
  | LScons c s rest => LScons c (add_ticks s) (add_ticks_cases rest)
  end.

(** Instrument a function: a tick on entry, a tick per loop iteration, and
    the extra temporary. *)
Definition instrument_function (f : function) : function :=
  {| fn_return := fn_return f; fn_callconv := fn_callconv f;
     fn_params := fn_params f; fn_vars := fn_vars f;
     fn_temps := (_fvz_t, tulong) :: fn_temps f;
     fn_body := Ssequence tick (add_ticks (fn_body f)) |}.

(** Does [s] have the shape of [tick]?  It is enough to look at the
    temporary it assigns, since no other statement assigns [_fvz_t]. *)
Definition is_tick (s : statement) : bool :=
  match s with
  | Ssequence (Sset t _) _ => Pos.eqb t _fvz_t
  | _ => false
  end.

(** Removing the ticks again. *)
Fixpoint erase_ticks (s : statement) : statement :=
  match s with
  | Ssequence a b =>
      if is_tick a then erase_ticks b
      else Ssequence (erase_ticks a) (erase_ticks b)
  | Sifthenelse e a b => Sifthenelse e (erase_ticks a) (erase_ticks b)
  | Sloop a b => Sloop (erase_ticks a) (erase_ticks b)
  | Slabel l a => Slabel l (erase_ticks a)
  | _ => s
  end.

(** Erasing the ticks of an instrumented statement gives back the original
    statement, provided the original does not itself use the temporary. *)
