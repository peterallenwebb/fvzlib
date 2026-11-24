(** * Spike: removing forward gotos to a cleanup label

    A transformation on Clight statements, for functions of this shape:

<<
      ... code containing "goto L" ...
    L:
      ... cleanup code that always returns ...
>>

    Each [goto L] is replaced by a copy of the cleanup code.  The label is
    then dropped, since nothing jumps to it any more.

    This file contains the transformation and the side conditions under
    which it is meant to be used.  It contains no proof that the
    transformation preserves behavior.  That is the subject of
    [Transfer.v]. *)

From compcert Require Import Coqlib AST Ctypes Clight.
From Stdlib Require Import List.
Import ListNotations.

(** Replace every [goto L] in [s] by [tail]. *)
Fixpoint subst_goto (L : label) (tail : statement) (s : statement) : statement :=
  match s with
  | Sgoto l => if Pos.eqb l L then tail else s
  | Ssequence a b => Ssequence (subst_goto L tail a) (subst_goto L tail b)
  | Sifthenelse e a b => Sifthenelse e (subst_goto L tail a) (subst_goto L tail b)
  | Sloop a b => Sloop (subst_goto L tail a) (subst_goto L tail b)
  | Sswitch e cases => Sswitch e (subst_goto_cases L tail cases)
  | Slabel l a => Slabel l (subst_goto L tail a)
  | _ => s
  end
with subst_goto_cases (L : label) (tail : statement) (cases : labeled_statements)
  : labeled_statements :=
  match cases with
  | LSnil => LSnil
  | LScons c s rest => LScons c (subst_goto L tail s) (subst_goto_cases L tail rest)
  end.

(** The code from label [L] to the end of the function, when [L] labels a
    statement on the top-level sequence of the body.  In Clight a label is
    attached to one statement, and the statements after it follow in the
    enclosing sequence, so the cleanup code is the labeled statement
    together with everything after it. *)
Fixpoint find_tail (L : label) (s : statement) : option statement :=
  match s with
  | Slabel l t => if Pos.eqb l L then Some t else None
  | Ssequence (Slabel l t) rest =>
      if Pos.eqb l L then Some (Ssequence t rest) else find_tail L rest
  | Ssequence _ rest => find_tail L rest
  | _ => None
  end.

(** Remove the label itself from the top-level sequence. *)
Fixpoint drop_label (L : label) (s : statement) : statement :=
  match s with
  | Slabel l t => if Pos.eqb l L then t else s
  | Ssequence (Slabel l t) rest =>
      if Pos.eqb l L then Ssequence t rest
      else Ssequence (Slabel l t) (drop_label L rest)
  | Ssequence a rest => Ssequence a (drop_label L rest)
  | _ => s
  end.

(** ** Side conditions *)

(** [s] contains no jump, label, break, or continue. *)
Fixpoint straight (s : statement) : bool :=
  match s with
  | Sgoto _ | Slabel _ _ | Sbreak | Scontinue => false
  | Ssequence a b => straight a && straight b
  | Sifthenelse _ a b => straight a && straight b
  | Sloop a b => straight a && straight b
  | Sswitch _ cases => straight_cases cases
  | _ => true
  end
with straight_cases (cases : labeled_statements) : bool :=
  match cases with
  | LSnil => true
  | LScons _ s rest => straight s && straight_cases rest
  end.

(** Every path through [s] ends in a return. *)
Fixpoint always_returns (s : statement) : bool :=
  match s with
  | Sreturn _ => true
  | Ssequence a b => always_returns a || always_returns b
  | Sifthenelse _ a b => always_returns a && always_returns b
  | _ => false
  end.

(** The cleanup code may be copied to a jump site only if it never falls
    off its end and has no control flow that depends on where it sits. *)
Definition tail_ok (tail : statement) : bool :=
  straight tail && always_returns tail.

(** ** The transformation *)

Definition elim_tail_goto (L : label) (body : statement) : option statement :=
  match find_tail L body with
  | Some tail =>
      if tail_ok tail
      then Some (drop_label L (subst_goto L tail body))
      else None
  | None => None
  end.

(** [s] contains no goto at all. *)
Fixpoint goto_free (s : statement) : bool :=
  match s with
  | Sgoto _ => false
  | Ssequence a b => goto_free a && goto_free b
  | Sifthenelse _ a b => goto_free a && goto_free b
  | Sloop a b => goto_free a && goto_free b
  | Sswitch _ cases => goto_free_cases cases
  | Slabel _ a => goto_free a
  | _ => true
  end
with goto_free_cases (cases : labeled_statements) : bool :=
  match cases with
  | LSnil => true
  | LScons _ s rest => goto_free s && goto_free_cases rest
  end.

Definition transform_function (L : label) (f : function) : option function :=
  match elim_tail_goto L (fn_body f) with
  | Some body =>
      Some {| fn_return := fn_return f; fn_callconv := fn_callconv f;
              fn_params := fn_params f; fn_vars := fn_vars f;
              fn_temps := fn_temps f; fn_body := body |}
  | None => None
  end.
