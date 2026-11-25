(** * A census of arithmetic that VST does not check

    VST checks many things the C standard leaves undefined, but not all.
    This file lists, for a Clight function, every construct of four kinds
    whose result the C standard leaves undefined or implementation-defined
    for some operand values, and which VST accepts without question:

    - a left shift of a signed value: undefined if the value is negative or
      the result does not fit;
    - a right shift of a signed value: implementation-defined if the value
      is negative;
    - a division or remainder of signed values: implementation-defined in
      the 1990 standard if either operand is negative;
    - a conversion into a signed integer type that cannot hold every value
      of the source type: implementation-defined if the value does not fit.

    Each item is given a status.  An item is closed by its constants when
    its operands are constants for which the result is defined.  It is
    closed by its types when the types of its operands rule out the bad
    values.  Otherwise it is open, and something else has to show that the
    bad values do not arise.

    This is plain computation over the syntax tree.  It proves nothing by
    itself.  Its value is that the list is complete for these four kinds,
    by construction, and that it is recomputed whenever the source changes. *)

From compcert Require Import Coqlib Integers AST Ctypes Cop Clight.
From Stdlib Require Import List ZArith Bool.
Import ListNotations.
Local Open Scope Z_scope.

Inductive kind : Type :=
| SignedShiftLeft | SignedShiftRight | SignedDivision | IntoSigned.

Inductive status : Type := Open | ByConstants | ByTypes.

Record item : Type :=
  mk_item { item_kind : kind; item_status : status; item_expr : expr }.

(** ** Integer types *)

(** The width in bits and the signedness of an integer type. *)
Definition int_shape (t : type) : option (Z * bool) :=
  match t with
  | Tint IBool _ _ => Some (1, false)
  | Tint I8 Signed _ => Some (8, true)
  | Tint I8 Unsigned _ => Some (8, false)
  | Tint I16 Signed _ => Some (16, true)
  | Tint I16 Unsigned _ => Some (16, false)
  | Tint I32 Signed _ => Some (32, true)
  | Tint I32 Unsigned _ => Some (32, false)
  | Tlong Signed _ => Some (64, true)
  | Tlong Unsigned _ => Some (64, false)
  | _ => None
  end.

(** Every value of the first shape is a value of the second. *)
Definition fits (src dst : Z * bool) : bool :=
  match src, dst with
  | (s, true), (d, true) => s <=? d
  | (s, false), (d, true) => s <? d
  | (s, false), (d, false) => s <=? d
  | (_, true), (_, false) => false
  end.

(** A conversion from [src] to [dst] lands in a signed type that cannot
    hold every value of [src]. *)
Definition lossy_into_signed (src dst : type) : bool :=
  match int_shape src, int_shape dst with
  | Some s, Some (d, true) => negb (fits s (d, true))
  | _, _ => false
  end.

(** No value of this type is negative. *)
Definition unsigned_type (t : type) : bool :=
  match int_shape t with Some (_, false) => true | _ => false end.

(** ** Constants *)

Definition const_value (e : expr) : option Z :=
  match e with
  | Econst_int n (Tint _ Unsigned _) => Some (Int.unsigned n)
  | Econst_int n _ => Some (Int.signed n)
  | Econst_long n (Tlong Unsigned _) => Some (Int64.unsigned n)
  | Econst_long n _ => Some (Int64.signed n)
  | _ => None
  end.

Definition is_const (e : expr) : bool :=
  match const_value e with Some _ => true | None => false end.

(** The expression is never negative: its type is unsigned, or it is a
    non-negative constant. *)
Definition never_negative (e : expr) : bool :=
  unsigned_type (typeof e) ||
  match const_value e with Some v => 0 <=? v | None => false end.

(** ** Status of each kind of item *)

Definition from (both_const ok : bool) : status :=
  if ok then (if both_const then ByConstants else ByTypes) else Open.

Definition division_status (a b : expr) : status :=
  from (is_const a && is_const b) (never_negative a && never_negative b).

Definition shift_right_status (a : expr) : status :=
  from (is_const a) (never_negative a).

(** A left shift is defined when the value is non-negative and the result
    fits in the signed result type of [bits] bits. *)
Definition shift_left_status (bits : Z) (a b : expr) : status :=
  match const_value a, const_value b with
  | Some va, Some vb =>
      if (0 <=? va) && (0 <=? vb) && (va * 2 ^ vb <? 2 ^ (bits - 1))
      then ByConstants else Open
  | None, Some vb =>
      match int_shape (typeof a) with
      | Some (w, false) =>
          if (0 <=? vb) && (w + vb <=? bits - 1) then ByTypes else Open
      | _ => Open
      end
  | _, _ => Open
  end.

Definition conversion_status (a : expr) (dst : type) : status :=
  match const_value a, int_shape dst with
  | Some v, Some (d, true) =>
      if (- 2 ^ (d - 1) <=? v) && (v <? 2 ^ (d - 1)) then ByConstants else Open
  | _, _ => Open
  end.

(** ** Scanning *)

Definition shift_item (left : bool) (e a b : expr) : list item :=
  let mk bits :=
    if left
    then [mk_item SignedShiftLeft (shift_left_status bits a b) e]
    else [mk_item SignedShiftRight (shift_right_status a) e] in
  match classify_shift (typeof a) (typeof b) with
  | shift_case_ii Signed | shift_case_il Signed => mk 32
  | shift_case_ll Signed | shift_case_li Signed => mk 64
  | _ => []
  end.

Definition division_item (e a b : expr) : list item :=
  match classify_binarith (typeof a) (typeof b) with
  | bin_case_i Signed | bin_case_l Signed =>
      [mk_item SignedDivision (division_status a b) e]
  | _ => []
  end.

(** An implicit or explicit conversion of [a] to type [dst]. *)
Definition conversion_item (a : expr) (dst : type) : list item :=
  if lossy_into_signed (typeof a) dst
  then [mk_item IntoSigned (conversion_status a dst) (Ecast a dst)]
  else [].

(** The conversions of both operands to the common type of an arithmetic
    operation, when that type is signed. *)
Definition operand_conversions (a b : expr) : list item :=
  match classify_binarith (typeof a) (typeof b) with
  | bin_case_i Signed =>
      conversion_item a (Tint I32 Signed noattr) ++
      conversion_item b (Tint I32 Signed noattr)
  | bin_case_l Signed =>
      conversion_item a (Tlong Signed noattr) ++
      conversion_item b (Tlong Signed noattr)
  | _ => []
  end.

Definition is_arith (op : binary_operation) : bool :=
  match op with
  | Oadd | Osub | Omul | Odiv | Omod | Oand | Oor | Oxor
  | Oeq | One | Olt | Ogt | Ole | Oge => true
  | _ => false
  end.

Fixpoint scan_expr (e : expr) : list item :=
  match e with
  | Ebinop op a b _ =>
      scan_expr a ++ scan_expr b ++
      (if is_arith op then operand_conversions a b else []) ++
      match op with
      | Oshl => shift_item true e a b
      | Oshr => shift_item false e a b
      | Odiv | Omod => division_item e a b
      | _ => []
      end
  | Ecast a ty => scan_expr a ++ conversion_item a ty
  | Eunop _ a _ => scan_expr a
  | Ederef a _ => scan_expr a
  | Eaddrof a _ => scan_expr a
  | Efield a _ _ => scan_expr a
  | _ => []
  end.

Definition scan_exprs (es : list expr) : list item := flat_map scan_expr es.

(** The conversions of call arguments to the parameter types. *)
Fixpoint argument_conversions (args : list expr) (params : list type) : list item :=
  match args, params with
  | a :: args', p :: params' =>
      conversion_item a p ++ argument_conversions args' params'
  | _, _ => []
  end.

Definition parameter_types (f : expr) : list type :=
  match typeof f with
  | Tfunction params _ _ => params
  | Tpointer (Tfunction params _ _) _ => params
  | _ => []
  end.

(** [ret] is the return type of the enclosing function. *)
Fixpoint scan_stmt (ret : type) (s : statement) : list item :=
  match s with
  | Sassign a b => scan_expr a ++ scan_expr b ++ conversion_item b (typeof a)
  | Sset _ e => scan_expr e
  | Scall _ f args =>
      scan_expr f ++ scan_exprs args ++
      argument_conversions args (parameter_types f)
  | Sbuiltin _ _ _ args => scan_exprs args
  | Ssequence a b => scan_stmt ret a ++ scan_stmt ret b
  | Sifthenelse c a b => scan_expr c ++ scan_stmt ret a ++ scan_stmt ret b
  | Sloop a b => scan_stmt ret a ++ scan_stmt ret b
  | Sreturn (Some e) => scan_expr e ++ conversion_item e ret
  | Sswitch e cases => scan_expr e ++ scan_cases ret cases
  | Slabel _ a => scan_stmt ret a
  | _ => []
  end
with scan_cases (ret : type) (cases : labeled_statements) : list item :=
  match cases with
  | LSnil => []
  | LScons _ s rest => scan_stmt ret s ++ scan_cases ret rest
  end.

(** Every item in a function. *)
Definition census (f : function) : list item :=
  scan_stmt (fn_return f) (fn_body f).

(** The kinds and statuses, without the expressions. *)
Definition summary (items : list item) : list (kind * status) :=
  map (fun i => (item_kind i, item_status i)) items.

Definition is_open (i : item) : bool :=
  match item_status i with Open => true | _ => false end.

Definition open_items (items : list item) : list item := filter is_open items.

Definition count (k : kind) (items : list item) : nat :=
  length (filter (fun i => match item_kind i, k with
                           | SignedShiftLeft, SignedShiftLeft
                           | SignedShiftRight, SignedShiftRight
                           | SignedDivision, SignedDivision
                           | IntoSigned, IntoSigned => true
                           | _, _ => false
                           end) items).
