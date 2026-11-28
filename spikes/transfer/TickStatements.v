(** * The two theorems about tick instrumentation, stated

    [proofs/lib/Ticks.v] adds a counter to a function.  A VST proof about the
    instrumented function shows that the counter never runs out.  Two
    theorems are needed to turn that into a statement about the original
    program.  This file states both, in terms of CompCert's semantics of
    Clight.  It contains definitions only, and assumes nothing.

    - [bounded_ticks_bound_steps]: an execution of an instrumented program
      that spends few ticks takes few steps.  Proven in [TickBound.v].
    - [erasure_preserves_behavior]: if the instrumented program never goes
      wrong, the original program behaves as the instrumented one does.
      Not proven.  Its status is in ledger entry T0002.

    Each statement is a definition of type [Prop], not an axiom, so that
    stating it adds nothing to what the project assumes. *)

From compcert Require Import Coqlib Integers AST Ctypes Cop Values Memory
  Events Globalenvs Smallstep Behaviors Clight Clightdefs.
From Stdlib Require Import List.
From fvzlib.proofs.lib Require Import Ticks Executions.
Import ListNotations.
Local Open Scope nat_scope.

(** ** The three parts of a tick

    [tick] is: load the counter, test it, store it decremented.  The store
    is the step that spends the tick. *)

Definition tick_load : statement :=
  Sset _fvz_t (Evar _fvz_ticks tulong).

Definition tick_test : statement :=
  Sifthenelse
    (Ebinop Oeq (Etempvar _fvz_t tulong)
            (Econst_long (Int64.repr 0) tulong) tint)
    (Sgoto _fvz_exhausted)
    Sskip.

Definition tick_spend : statement :=
  Sassign (Evar _fvz_ticks tulong)
    (Ebinop Osub (Etempvar _fvz_t tulong)
            (Econst_long (Int64.repr 1) tulong) tulong).

Lemma tick_parts :
  tick = Ssequence tick_load (Ssequence tick_test tick_spend).
Proof. reflexivity. Qed.

(** ** What an instrumented function looks like

    [ticked s]: every loop in [s] starts each iteration with a tick, the
    only jump is the one a tick makes when the counter is zero, and no
    statement carries the label that jump names.  So that jump has nowhere
    to go, and is stuck. *)
Fixpoint ticked (s : statement) : Prop :=
  match s with
  | Ssequence a b => ticked a /\ ticked b
  | Sifthenelse _ a b => ticked a /\ ticked b
  | Sloop a b =>
      match a with
      | Ssequence t a' => t = tick /\ ticked a'
      | _ => False
      end /\ ticked b
  | Sswitch _ cases => ticked_cases cases
  | Slabel l a => l <> _fvz_exhausted /\ ticked a
  | Sgoto l => l = _fvz_exhausted
  | _ => True
  end
with ticked_cases (cases : labeled_statements) : Prop :=
  match cases with
  | LSnil => True
  | LScons _ s rest => ticked s /\ ticked_cases rest
  end.

(** A function that spends a tick on entry and whose body is [ticked]. *)
Definition instrumented (f : function) : Prop :=
  exists body, fn_body f = Ssequence tick body /\ ticked body.

(** ** The size of a statement

    A count of the steps a statement can take before it finishes, enters a
    loop body, or calls a function.  The constant in the first theorem is
    the largest size of a function body. *)
Fixpoint size (s : statement) : nat :=
  match s with
  | Sskip | Sbreak | Scontinue => 1
  | Sassign _ _ | Sset _ _ | Sbuiltin _ _ _ _ | Sreturn _ | Sgoto _ => 2
  | Scall _ _ _ => 6
  | Ssequence a b => size a + size b + 2
  | Sifthenelse _ a b => size a + size b + 1
  | Sloop a b => size a + size b + 6
  | Sswitch _ cases => size_cases cases + 2
  | Slabel _ a => size a + 1
  end
with size_cases (cases : labeled_statements) : nat :=
  match cases with
  | LSnil => 1
  | LScons _ s rest => size s + size_cases rest + 2
  end.

(** ** Counting steps and ticks *)

Section EXECUTIONS.

Variable ge : genv.

(** How a function is entered.  CompCert has two rules, [function_entry1]
    and [function_entry2].  The first theorem holds for any. *)
Variable entry : function -> list val -> mem -> env -> temp_env -> mem -> Prop.

(** A state about to spend a tick. *)
Definition spending (s : state) : Prop :=
  exists f k e le m, s = State f tick_spend k e le m.

(** [run s n c s']: there are [n] steps from [s] to [s'], and [c] of them
    spend a tick. *)
Inductive run : state -> nat -> nat -> state -> Prop :=
| run_stop s :
    run s 0 0 s
| run_spend s t s1 n c s' :
    spending s -> step ge entry s t s1 -> run s1 n c s' ->
    run s (S n) (S c) s'
| run_other s t s1 n c s' :
    ~ spending s -> step ge entry s t s1 -> run s1 n c s' ->
    run s (S n) c s'.

End EXECUTIONS.

(** ** The first theorem: bounded ticks bound the steps

    Take a program in which every function is instrumented and has a body
    of size at most [K].  Start any of its functions with an empty
    continuation, as the program's entry point is started.  If the
    execution has spent [c] ticks so far, it has taken at most
    [K * (c + 1) + 2] steps.

    A step is a step of CompCert's semantics of Clight.  A call to an
    external function is one step, whatever that function does.

    So an execution that cannot spend more than [c] ticks cannot run for
    more than that many steps: it has stopped, by returning or by getting
    stuck.  The statement does not say which.

    It counts ticks spent, not the value of the counter.  It therefore
    also covers a client that sets the counter again between calls. *)
Definition bounded_ticks_bound_steps : Prop :=
  forall (ge : genv) entry (K : nat),
    (forall b f, Genv.find_funct_ptr ge b = Some (Internal f) ->
                 instrumented f /\ size (fn_body f) <= K) ->
    forall b fd args m s n c,
      Genv.find_funct_ptr ge b = Some fd ->
      run ge entry (Callstate fd args Kstop m) n c s ->
      n <= K * (c + 1) + 2.

(** ** Instrumenting a whole program

    Every function defined in the program is instrumented, and the counter
    is added as a global variable holding [budget]. *)

Definition instrument_fundef (fd : Clight.fundef) : Clight.fundef :=
  match fd with
  | Internal f => Internal (instrument_function f)
  | External _ _ _ _ => fd
  end.

Definition instrument_globdef (gd : globdef Clight.fundef type)
  : globdef Clight.fundef type :=
  match gd with
  | Gfun fd => Gfun (instrument_fundef fd)
  | Gvar v => Gvar v
  end.

Definition counter (budget : int64) : globvar type :=
  {| gvar_info := tulong;
     gvar_init := [Init_int64 budget];
     gvar_readonly := false;
     gvar_volatile := false |}.

Definition instrument_program (budget : int64) (p : Clight.program)
  : Clight.program :=
  {| prog_defs :=
       (_fvz_ticks, Gvar (counter budget))
       :: map (fun d => (fst d, instrument_globdef (snd d))) (prog_defs p);
     prog_public := prog_public p;
     prog_main := prog_main p;
     prog_types := prog_types p;
     prog_comp_env := prog_comp_env p;
     prog_comp_env_eq := prog_comp_env_eq p |}.

(** ** The names the instrumentation adds must be new

    [expr_uses id a] and [stmt_uses id s]: the name [id] occurs in the
    expression or statement, as a variable, a temporary, or a label. *)
Fixpoint expr_uses (id : ident) (a : expr) : bool :=
  match a with
  | Evar x _ | Etempvar x _ => Pos.eqb x id
  | Ederef a1 _ | Eaddrof a1 _ | Eunop _ a1 _ | Ecast a1 _
  | Efield a1 _ _ => expr_uses id a1
  | Ebinop _ a1 a2 _ => expr_uses id a1 || expr_uses id a2
  | _ => false
  end.

Definition opt_is (id : ident) (x : option ident) : bool :=
  match x with Some y => Pos.eqb y id | None => false end.

Fixpoint stmt_uses (id : ident) (s : statement) : bool :=
  match s with
  | Sskip | Sbreak | Scontinue | Sreturn None => false
  | Sassign a1 a2 => expr_uses id a1 || expr_uses id a2
  | Sset x a => Pos.eqb x id || expr_uses id a
  | Scall x a args =>
      opt_is id x || expr_uses id a || existsb (expr_uses id) args
  | Sbuiltin x _ _ args => opt_is id x || existsb (expr_uses id) args
  | Ssequence a b => stmt_uses id a || stmt_uses id b
  | Sifthenelse c a b => expr_uses id c || stmt_uses id a || stmt_uses id b
  | Sloop a b => stmt_uses id a || stmt_uses id b
  | Sreturn (Some a) => expr_uses id a
  | Sswitch a cases => expr_uses id a || cases_use id cases
  | Slabel l a => Pos.eqb l id || stmt_uses id a
  | Sgoto l => Pos.eqb l id
  end
with cases_use (id : ident) (cases : labeled_statements) : bool :=
  match cases with
  | LSnil => false
  | LScons _ s rest => stmt_uses id s || cases_use id rest
  end.

(** The function does not use the name at all. *)
Definition new_in_function (id : ident) (f : function) : Prop :=
  ~ In id (var_names (fn_params f)) /\
  ~ In id (var_names (fn_vars f)) /\
  ~ In id (var_names (fn_temps f)) /\
  stmt_uses id (fn_body f) = false.

(** The program does not use the three names the instrumentation adds. *)
Definition names_are_new (p : Clight.program) : Prop :=
  ~ In _fvz_ticks (map fst (prog_defs p)) /\
  forall id f, In (id, Gfun (Internal f)) (prog_defs p) ->
    new_in_function _fvz_ticks f /\
    new_in_function _fvz_t f /\
    new_in_function _fvz_exhausted f.

(** ** The second theorem: erasing the ticks preserves behavior

    A behavior, in CompCert's sense, is what can be observed of a whole
    execution: its trace of input and output events, and whether it
    terminates, with which value, or runs forever, or goes wrong.

    Take a program that does not use the three names, and instrument it
    with any budget.  If the instrumented program never goes wrong, then
    every behavior of the original program is a behavior of the
    instrumented one.  In particular the original never goes wrong
    either.

    The semantics is the one VST's soundness theorem speaks of, in which
    parameters are temporaries.

    This is the direction a transfer needs.  VST shows that the
    instrumented program never goes wrong, and this statement then carries
    what is known of its behaviors over to the program without ticks.

    Not covered: a program where a client sets the counter again between
    calls.  That assignment is instrumentation too, and
    [instrument_program] does not add it. *)
Definition erasure_preserves_behavior : Prop :=
  forall (budget : int64) (p : Clight.program),
    names_are_new p ->
    never_goes_wrong (instrument_program budget p) ->
    forall beh,
      program_behaves (Clight.semantics2 p) beh ->
      program_behaves (Clight.semantics2 (instrument_program budget p)) beh.
