(** Federer (1969), 2.1.1, pp. 52–53, supporting
    the finite order squeeze for the original conical
    upper density in 3.3.19, p. 305. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [nonnegative_ereal_positive_lower_tests]: a
    nonnegative extended real above every positive real k<c
    is at least the positive real c. This supporting
    order fact retains infinity in the density conclusion
    of 3.3.19, p. 305. *)
Theorem nonnegative_ereal_positive_lower_tests (R:realType) (q: \bar R) (c:R):
  (0<=q)%E ->0<c ->(forall k:R,0<k ->k<c ->(k%:E<=q)%E) ->(c%:E<=q)%E.
Proof.
case:q=>[v| |] hNonnegative hc hTests;last 2 first.
- exact:leey.
- by rewrite leNgt ltNyr in hNonnegative.
rewrite lee_fin leNgt;apply/negP=>hv.
rewrite lee_fin in hNonnegative.
have hMid:0<(c+v)/2 by lra.
have hMidUpper:(c+v)/2<c by lra.
have hBound:= hTests _ hMid hMidUpper.
rewrite lee_fin in hBound;lra.
Qed.
