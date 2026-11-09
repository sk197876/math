(** Federer (1969), 3.3.20, pp. 306–309:
    exact scalar endpoints of the original critical children. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [four_adic_interval_scalar_endpoints]: the
    actual quarter-length endpoint children have integer
    lower addresses 4a and 4a+3. These four
    scalar equations support original interval membership
    in 3.3.20, pp. 306–309. All denominators
    are positive finite original scales. *)
Lemma four_adic_interval_scalar_endpoints (R:realType) (a r:R):0<r ->
  (4*a)/(4*r)=a/r /\
  (4*a+1)/(4*r)=a/r+((a+1)/r-a/r)/4 /\
  (4*a+3)/(4*r)=(a+1)/r-((a+1)/r-a/r)/4 /\
  (4*a+4)/(4*r)=(a+1)/r.
Proof.
move=>hr;have hNonzero:r!=0 by rewrite gt_eqF.
split;first by field;rewrite hNonzero.
split;first by field;rewrite hNonzero.
split;field;by rewrite hNonzero.
Qed.
