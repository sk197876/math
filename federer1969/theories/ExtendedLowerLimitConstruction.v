(** Private existence proof for the scalar lower limit used in Federer
    (1969), 2.4.6, p. 84. Source context and precise role:
    ExtendedLowerLimitUP.v. The existing sealed extended-real supremum
    supplies the witness. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBoundsUP ExtendedRealBounds ExtendedLowerLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_lower_limit_exists]: supporting
    existence of the scalar lower limit in Federer 2.4.6,
    p. 84, using completeness from 2.1.1, p. 51. *)
Theorem extended_lower_limit_exists (R : realType) (u : nat -> \bar R) :
  exists l, is_extended_lower_limit u l.
Proof.
exists (extended_real_sup (extended_eventual_lower_bounds u)); constructor.
- exact: extended_real_sup_upper.
- exact: extended_real_sup_least.
Qed.
