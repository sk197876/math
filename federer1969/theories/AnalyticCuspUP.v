(** Federer (1969), 3.4.11, p. 338:
    independent equation laws for the original plane cusp.
    Its tangent cone and nonanalyticity are conclusions
    to prove, not parts of this specification. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_analytic_cusp]: the printed set
    x_1^3=x_2^2 in the counterexample of 3.4.11,
    p. 338, specified only by its original equation. *)
Definition is_analytic_cusp (R:realType) (S:set (R_n R 2)):Prop:=
  forall v,S v <->(v ord0)^+3=(v ord_max)^+2.
