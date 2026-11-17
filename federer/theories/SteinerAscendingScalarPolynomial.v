(** Original Steiner coefficients in ascending radius order
    for Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  IntegralGeometricGauge EuclideanBallVolume SteinerTubePolynomial SteinerTubeScalarPolynomial
  ScalarComplementPolynomialComparison FinitePowerPadding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_tube_polynomial_ascending_scalar_value]: supporting
    finite interpolation of the original Steiner polynomial
    in Federer 3.2.45, p. 279, from 3.2.35,
    p. 271. Reverse the original finite ordinal
    indices; each radius-degree i coefficient remains
    the actual intrinsic volume of degree n-i times
    alpha(i). Existing finiteness justifies every scalar
    representative. No coefficient is redefined. *)
Lemma steiner_tube_polynomial_ascending_scalar_value (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (r : R) :
  S !=set0 -> is_inner_convex S -> metric_set_bounded S ->
  steiner_tube_polynomial S r=
    (\sum_(i : 'I_n.+1)
      (fine (@integral_geometric_gauge R n (n-i) (leq_subr i n) 1 S)*
        euclidean_unit_ball_volume R i)*r^+i)%:E.
Proof.
move=> hNonempty hConvex hBound.
rewrite (@steiner_tube_polynomial_scalar_value R n S r hNonempty hConvex hBound); congr (_%:E).
under eq_bigr do rewrite mulrA.
rewrite finite_reverse_power_sum; apply: eq_bigr=> i _.
have hIndex : (n-rev_ord i)%N= i.
  change ((n-(n.+1-i.+1))%N= i); rewrite subSS subKn //.
  by have := ltn_ord i; rewrite ltnS.
rewrite hIndex.
by rewrite (bool_irrelevance (steiner_dimension_guard (rev_ord i)) (leq_subr i n)).
Qed.

(** Source for [steiner_tube_polynomial_padded_scalar_value]: supporting
    recovery of the actual section coefficients with the
    ambient finite evaluation map in Federer 3.2.45,
    p. 279. The ascending section polynomial is
    padded by zero above its original dimension q.
    Its other coefficients are unchanged. Empty
    coordinate blocks and equality of dimensions remain. *)
Theorem steiner_tube_polynomial_padded_scalar_value (R : realType) q N (hQN : (q<=N)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R q))) (r : R) :
  S !=set0 -> is_inner_convex S -> metric_set_bounded S ->
  steiner_tube_polynomial S r=
    (\sum_(i : 'I_N.+1)
      (if (i<=q)%N then fine (@integral_geometric_gauge R q (q-i) (leq_subr i q) 1 S)*
        euclidean_unit_ball_volume R i else 0)*r^+i)%:E.
Proof.
move=> hNonempty hConvex hBound.
rewrite (@steiner_tube_polynomial_ascending_scalar_value R q S r hNonempty hConvex hBound).
congr (_%:E).
exact: (@finite_ascending_power_padding R q N hQN
  (fun j : nat => fine (@integral_geometric_gauge R q (q-j) (leq_subr j q) 1 S)*
    euclidean_unit_ball_volume R j) r).
Qed.
