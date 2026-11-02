(** Federer (1969), 3.2.16, p. 253,
    corrected by erratum p. 5, book line 29:
    the annular radii satisfy delta_(i+1)<delta_i/2.
    Specify this choice independently of a witness;
    P records the required small-ball property. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_shrinking_radius_selection]:
    positive good radii with the corrected
    strict half-radius decrease in Federer
    3.2.16, p. 253 line 29; erratum p. 5. *)
Record is_shrinking_radius_selection (R : realType)
    (P : nat -> R -> Prop) (rho : nat -> R) : Prop := {
  (** Source for [shrinking_radius_positive]: delta_i>0
      in Federer 3.2.16, p. 253. *)
  shrinking_radius_positive : forall n, 0<rho n;
  (** Source for [shrinking_radius_property]: the
      small-mass condition at the selected delta_i,
      Federer 3.2.16, p. 253. *)
  shrinking_radius_property : forall n, P n (rho n);
  (** Source for [shrinking_radius_half]: the correction
      delta_(i+1)<delta_i/2, erratum p. 5,
      book p. 253 line 29. *)
  shrinking_radius_half : forall n, rho n.+1<rho n/2
}.
