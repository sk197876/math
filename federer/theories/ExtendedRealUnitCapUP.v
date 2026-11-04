(** Supporting finite metric representation for Federer (1969),
    3.2.46, p. 281. On a disconnected chart the original path
    infimum may be infinite. The cap min(1,rho) is a technical
    carrier for local metric arguments; it does not replace
    rho's defining infimum or assert that rho is globally finite. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_extended_real_unit_cap]: supporting scalar
    representation for the metric assertion of Federer 3.2.46,
    p. 281. These independent laws specify the finite cap before
    its private construction. Preservation of local distances and
    Hausdorff measures requires separate proved assertions. *)
Record is_extended_real_unit_cap (R : realType) (cap : \bar R -> R) : Prop := {
  (** Source for [unit_cap_finite]: min(1,r) on finite inputs;
      technical metric support for 3.2.46, p. 281, not a book definition. *)
  unit_cap_finite : forall r : R, cap r%:E = Order.min r 1;
  (** Source for [unit_cap_posinf]: positive infinity has capped
      value one; technical support for 3.2.46, p. 281. *)
  unit_cap_posinf : cap +oo%E = 1;
  (** Source for [unit_cap_neginf]: an irrelevant total value at
      negative infinity; actual path distances are nonnegative.
      Technical support for 3.2.46, p. 281. *)
  unit_cap_neginf : cap -oo%E = 0
}.
