(** Federer (1969), 3.4.1, p. 310: independent laws for the printed critical degree. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_critical_value_degree]: the exact printed expression
    s=nu+(m-nu)/k in 3.4.1, p. 310. This equation specifies the scalar;
    it does not assume a critical-image measure theorem or its optimality.
    The book's m>nu>=0 and k>=1 are retained by the public interface. *)
Record is_critical_value_degree (R:realType) (m nu k:nat) (s:R):Prop:={
  (** Source for [critical_value_degree_equation]: the actual real scalar
      nu+(m-nu)/k of 3.4.1, p. 310, with division in the scalar field. *)
  critical_value_degree_equation:s=nu%:R+(m%:R-nu%:R)/k%:R
}.
