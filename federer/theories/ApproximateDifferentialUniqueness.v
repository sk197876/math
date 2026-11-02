(** Federer (1969), 3.1.2, p. 212: uniqueness of the linear approximate
    differential. The argument uses the printed small-ball measure
    obstruction, followed by boundedness and homogeneity of the difference. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric InnerNorm InnerNormInequalities RealNormUP
  HilbertFormCompactness NormFiniteLinearBound NormDifferentialUP NormLinearDenseProbes NormApproximationDifference
  MetricClosedBalls EuclideanDensityGoodPoint ApproximateDifferentialUP
  ApproximateDifferentialRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [approximate_differential_unique]: Federer 3.1.2, p. 212:
    the candidate linear map L is unique. The proof keeps the original
    base point, tests the sphere of half the containing radius and uses
    the same smaller-ball volume argument. No completeness or separability
    of the target is required. *)
Theorem approximate_differential_unique (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) (a : R_n R n) (L M : Hom (R_n R n) Y) :
  has_approximate_differential NY A f a L ->
  has_approximate_differential NY A f a M -> L=M.
Proof.
move=> hL hM.
pose NX := inner_norm (@euclidean_inner_productP R n).
have hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
have hbounded := @norm_finite_linear_bounded R (R_n R n) Y NX NY hNX hNY
  n (@coordinate_basis R n) (@coordinate_basisP R n) (L-M).
have hz : L-M=0.
  apply: (@norm_linear_dense_probes_zero R (R_n R n) Y NX NY hNX hNY (L-M) hbounded).
  move=> e he hehalf.
  have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
  have hEL := @approximate_remainder_exceptional_density R n Y NY hNY A f a L (e/2) hL he2.
  have hEM := @approximate_remainder_exceptional_density R n Y NY hNY A f a M (e/2) hM he2.
  have [d [hd hgood]] := euclidean_zero_density_good_point hEL hEM he.
  pose r := d/2.
  have hr : 0<r by rewrite /r divr_gt0 // ltr0n.
  have hrd : r<d by rewrite /r; lra.
  exists r; split=> // u hu.
  pose b : inner_metric_space (@euclidean_inner_productP R n) := a+u.
  have hb : mdist (a : inner_metric_space (@euclidean_inner_productP R n)) b=r/2.
    rewrite inner_metric_distanceE /b opprD addrA subrr add0r inner_normN.
    exact hu.
  have hsub : metric_closed_ball b (e*r) `<=`
      metric_closed_ball (a : inner_metric_space (@euclidean_inner_productP R n)) r.
    move=> x hx; have ht := metric_triangle
      (a : inner_metric_space (@euclidean_inner_productP R n)) b x.
    have hbnd := le_trans ht (lerD (lexx _) hx).
    rewrite hb in hbnd; change (is_true (mdist
      (a : inner_metric_space (@euclidean_inner_productP R n)) x<=r)); nra.
  have [v [hv [hvL hvM]]] := hgood r b hr hrd hsub.
  have hgL : approximate_remainder_good_points NY A f a L (e/2) v := contrapT hvL.
  have hgM : approximate_remainder_good_points NY A f a M (e/2) v := contrapT hvM.
  exists (v-a); split.
  - have hid : u-(v-a)=(a+u)-v by rewrite opprB addrA (addrC u a).
    rewrite /NX hid; change (is_true (mdist b v<=e*r)); exact hv.
  - have hvnorm : NX (v-a)<=r.
      have hh := hsub v hv.
      move: hh; rewrite /metric_closed_ball /= inner_metric_distanceE.
      by rewrite -opprB inner_normN.
    apply: le_trans (linear_difference_remainder_bound hNY hgL.2.2 hgM.2.2) _.
    change (is_true (e*NX (v-a)<=e*r)); nra.
by apply/eqP; rewrite -subr_eq0; apply/eqP.
Qed.
