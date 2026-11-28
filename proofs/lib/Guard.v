(** * Guards for the open items of the census

    The census lists arithmetic whose result the C standard does not fix
    for some operand values.  For an open item, something has to show that
    those values do not arise.  This transformation makes that a proof
    obligation.

    Before each statement that contains an open item, it inserts a test for
    the bad operand values.  If the test succeeds, the program jumps to a
    label that does not exist, which is a stuck state in Clight.  VST can
    prove a goto only when it is unreachable.  So a VST proof about the
    guarded function shows that the bad values never arise.

    Guards are implemented for signed division and remainder and for right
    shifts of signed values.  For the other two kinds the transformation
    refuses, returning [None], so an open item is never silently skipped.

    This file contains the transformation only.  What a proof about the
    guarded program says of the program without the guards is proven in
    [GuardSound.v]. *)

From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs.
From Stdlib Require Import List String.
From fvzlib.proofs.lib Require Import Census.
Import ListNotations.
Import Clightdefs.ClightNotations.

(** A label that no function defines.  Jumping to it is stuck. *)
Local Open Scope string_scope.
Local Open Scope clight_scope.
Definition _fvz_undefined : ident := $"fvz_undefined".
Local Close Scope clight_scope.
Local Close Scope string_scope.

(** A test that [a] is negative, unless [a] can never be. *)
Definition negative (a : expr) : list expr :=
  if never_negative a then []
  else [Ebinop Olt a (Econst_int (Int.repr 0) tint) tint].

(** The tests for the operand values that make an item's result undefined
    or implementation-defined.  [None] means no guard is implemented. *)
Definition violations (i : item) : option (list expr) :=
  match item_status i with
  | Open =>
      match item_kind i, item_expr i with
      | SignedDivision, Ebinop _ a b _ => Some (negative a ++ negative b)
      | SignedShiftRight, Ebinop _ a _ _ => Some (negative a)
      | _, _ => None
      end
  | _ => Some []
  end.

Fixpoint all_violations (items : list item) : option (list expr) :=
  match items with
  | [] => Some []
  | i :: rest =>
      match violations i, all_violations rest with
      | Some a, Some b => Some (a ++ b)
      | _, _ => None
      end
  end.

Definition guard (c : expr) : statement :=
  Sifthenelse c (Sgoto _fvz_undefined) Sskip.

Definition bind {A B} (x : option A) (f : A -> option B) : option B :=
  match x with Some a => f a | None => None end.

(** The transformation is in two steps.  The first decides what to test:
    it inspects types and constants.  The second inserts the tests: it
    looks only at the shape of the statements.  Keeping them apart lets the
    second step be computed without unfolding names, so that the result
    stays readable.

    A guard point is a place where tests may be inserted: in front of a
    simple statement, or in front of a conditional or switch for the
    expression it tests.  Both steps visit the guard points in the same
    order. *)

(** Step one: the tests for each guard point, in order. *)
Fixpoint plan_stmt (ret : type) (s : statement) : option (list (list expr)) :=
  match s with
  | Sassign _ _ | Sset _ _ | Scall _ _ _ | Sbuiltin _ _ _ _ | Sreturn _ =>
      bind (all_violations (scan_stmt ret s)) (fun c => Some [c])
  | Ssequence a b =>
      bind (plan_stmt ret a) (fun pa =>
      bind (plan_stmt ret b) (fun pb => Some (pa ++ pb)))
  | Sifthenelse c a b =>
      bind (all_violations (scan_expr c)) (fun pc =>
      bind (plan_stmt ret a) (fun pa =>
      bind (plan_stmt ret b) (fun pb => Some (pc :: pa ++ pb))))
  | Sloop a b =>
      bind (plan_stmt ret a) (fun pa =>
      bind (plan_stmt ret b) (fun pb => Some (pa ++ pb)))
  | Sswitch e cases =>
      bind (all_violations (scan_expr e)) (fun pe =>
      bind (plan_cases ret cases) (fun pc => Some (pe :: pc)))
  | Slabel _ a => plan_stmt ret a
  | _ => Some []
  end
with plan_cases (ret : type) (cases : labeled_statements)
  : option (list (list expr)) :=
  match cases with
  | LSnil => Some []
  | LScons _ s rest =>
      bind (plan_stmt ret s) (fun ps =>
      bind (plan_cases ret rest) (fun pr => Some (ps ++ pr)))
  end.

(** Put the tests [conds] in front of [s]. *)
Definition prefix (conds : list expr) (s : statement) : statement :=
  fold_right (fun c rest => Ssequence (guard c) rest) s conds.

(** Step two: insert the planned tests.  Returns the new statement and the
    part of the plan not yet used. *)
Fixpoint apply_stmt (s : statement) (plan : list (list expr))
  : statement * list (list expr) :=
  match s with
  | Sassign _ _ | Sset _ _ | Scall _ _ _ | Sbuiltin _ _ _ _ | Sreturn _ =>
      match plan with
      | c :: rest => (prefix c s, rest)
      | [] => (s, [])
      end
  | Ssequence a b =>
      let (a', p1) := apply_stmt a plan in
      let (b', p2) := apply_stmt b p1 in
      (Ssequence a' b', p2)
  | Sifthenelse c a b =>
      match plan with
      | pc :: rest =>
          let (a', p1) := apply_stmt a rest in
          let (b', p2) := apply_stmt b p1 in
          (prefix pc (Sifthenelse c a' b'), p2)
      | [] => (s, [])
      end
  | Sloop a b =>
      let (a', p1) := apply_stmt a plan in
      let (b', p2) := apply_stmt b p1 in
      (Sloop a' b', p2)
  | Sswitch e cases =>
      match plan with
      | pe :: rest =>
          let (cases', p1) := apply_cases cases rest in
          (prefix pe (Sswitch e cases'), p1)
      | [] => (s, [])
      end
  | Slabel l a =>
      let (a', p1) := apply_stmt a plan in (Slabel l a', p1)
  | _ => (s, plan)
  end
with apply_cases (cases : labeled_statements) (plan : list (list expr))
  : labeled_statements * list (list expr) :=
  match cases with
  | LSnil => (LSnil, plan)
  | LScons c s rest =>
      let (s', p1) := apply_stmt s plan in
      let (rest', p2) := apply_cases rest p1 in
      (LScons c s' rest', p2)
  end.

Definition with_body (f : function) (body : statement) : function :=
  {| fn_return := fn_return f; fn_callconv := fn_callconv f;
     fn_params := fn_params f; fn_vars := fn_vars f;
     fn_temps := fn_temps f; fn_body := body |}.

Definition guard_plan (f : function) : option (list (list expr)) :=
  plan_stmt (fn_return f) (fn_body f).

Definition apply_plan (f : function) (plan : list (list expr)) : function :=
  with_body f (fst (apply_stmt (fn_body f) plan)).

Definition guard_function (f : function) : option function :=
  bind (guard_plan f) (fun plan => Some (apply_plan f plan)).

(** ** Removing the guards again *)

Definition is_guard (s : statement) : bool :=
  match s with
  | Sifthenelse _ (Sgoto l) Sskip => Pos.eqb l _fvz_undefined
  | _ => false
  end.

Fixpoint erase_guards (s : statement) : statement :=
  match s with
  | Ssequence a b =>
      if is_guard a then erase_guards b
      else Ssequence (erase_guards a) (erase_guards b)
  | Sifthenelse c a b => Sifthenelse c (erase_guards a) (erase_guards b)
  | Sloop a b => Sloop (erase_guards a) (erase_guards b)
  | Sswitch e cases => Sswitch e (erase_guards_cases cases)
  | Slabel l a => Slabel l (erase_guards a)
  | _ => s
  end
with erase_guards_cases (cases : labeled_statements) : labeled_statements :=
  match cases with
  | LSnil => LSnil
  | LScons c s rest => LScons c (erase_guards s) (erase_guards_cases rest)
  end.
