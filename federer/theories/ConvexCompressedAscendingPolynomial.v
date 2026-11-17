(** Ascending anisotropic coefficients for the exact comparison
    in Federer (1969), 3.2.45, pp. 279–280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  EuclideanLinearMaps VectorSetSum EuclideanLebesgueDimensions EuclideanBallVolume IntegralGeometricGauge
  SteinerTubePolynomial ScalarComplementPolynomialComparison ConvexCompressedBallPolynomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_compressed_ball_ascending_polynomial]: supporting
    finite evaluation of the actual anisotropic tube
    coefficients in Federer 3.2.45, pp. 279–280.
    Reverse the indices in the already proved
    determinant-normalized Steiner polynomial. The radius-i
    coefficient is h^m times the original intrinsic
    volume of degree m+n-i of the inverse-stretched
    K, times alpha(i). No coefficient limit or
    order is introduced by this finite rearrangement. *)
Theorem convex_compressed_ball_ascending_polynomial (R : realType) m n
    (K : set (inner_metric_space (@euclidean_inner_productP R (m+n)))) (h r : R) :
  K !=set0 -> compact K -> is_inner_convex K -> 0<h -> 0<r ->
  @euclidean_lebesgue_measure R (m+n)
    (vector_set_sum K ((@euclidean_diagonal_map R (m+n) (fun j => if (j<m)%N then h else 1)) @`
      [set x | inner_norm (@euclidean_inner_productP R (m+n)) x<=r]))=
  (\sum_(i : 'I_(m+n).+1)
    (((h^+m)*fine (@integral_geometric_gauge R (m+n) (m+n-i) (leq_subr i (m+n)) 1
      ((@euclidean_diagonal_map R (m+n) (fun j => if (j<m)%N then h^-1 else 1)) @` K)))*
      euclidean_unit_ball_volume R i)*r^+i)%:E.
Proof.
move=> hNonempty hCompact hConvex hh hr.
rewrite (@convex_compressed_ball_volume_polynomial R m n K h r hNonempty hCompact hConvex hh hr).
congr (_%:E); under eq_bigr do rewrite mulrA.
rewrite finite_reverse_power_sum; apply: eq_bigr=> i _.
have hIndex : ((m+n)-rev_ord i)%N= i.
  change (((m+n)-((m+n).+1-i.+1))%N= i); rewrite subSS subKn //.
  by have := ltn_ord i; rewrite ltnS.
rewrite hIndex.
by rewrite (bool_irrelevance (steiner_dimension_guard (rev_ord i)) (leq_subr i (m+n))).
Qed.
