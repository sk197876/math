(** Federer (1969), 4.1.18, pp. 375–376:
    every original compact K in open U has a positive
    closed tube still contained in U. Reuse the actual
    compact neighbourhood theorem from 4.1.2, p. 348;
    no distance to an empty complement is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates SmoothCompactSet SmoothCompactInteriorThickening
  EuclideanClosedSupportTube VectorSetSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_compact_closed_tube_inside_exists]: the
    original compact-index union and both support-radius
    propositions use a positive tube inside U,
    Federer 4.1.18, pp. 375–376. Empty K and U remain allowed. *)
Theorem current_compact_closed_tube_inside_exists (R:realType) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U):
  exists delta:R,0<delta /\
    @euclidean_closed_support_tube R n (smooth_compact_carrier K) delta `<=` U.
Proof.
have[delta [hDelta [C [hKC hTube]]]]:=@smooth_compact_interior_thickening R
  (R_n R n) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU K.
exists delta;split;first exact:hDelta.
move=>x /vector_set_sum_membership [a [b [hA [hB hX]]]].
apply:(smooth_compact_in_domain C).
apply:(hTube x a hA).
change (inner_norm (@euclidean_inner_productP R n) (x-a)<=delta).
rewrite hX addrAC subrr add0r.
exact:hB.
Qed.
