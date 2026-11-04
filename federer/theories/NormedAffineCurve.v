(** Federer (1969), 3.2.46, p. 281: straight segments
    supply the local upper distance bound. The following
    actual derivative and Lipschitz computations support that
    comparison using only norm and vector-space laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import RealNormUP NormedCurveDerivativeUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  RealMetricBackground LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [affine_curve_increment]: supporting exact
    increment of the straight segment in Federer 3.2.46,
    p. 281; this is a vector-space identity. *)
Lemma affine_curve_increment (R : fieldType) (E : lmodType R)
    (x w : E) (t u : R) :
  (x+t*:w)-(x+u*:w) = (t-u)*:w.
Proof.
rewrite opprD addrACA subrr add0r -scalerBl; by [].
Qed.

(** Source for [affine_normed_curve_derivative]: the actual
    velocity of the straight segment is w at every parameter,
    supporting the local comparison in Federer 3.2.46, p. 281.
    It also covers w=0 and the zero vector space. *)
Lemma affine_normed_curve_derivative (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (x w : E) (t : R) :
  has_normed_curve_derivative N (fun s=>x+s*:w) t w.
Proof.
move=> e he; exists 1; split; first exact: ltr01.
move=> h /andP [hh hSmall].
have hne : h != 0 by rewrite -normr_gt0.
rewrite affine_curve_increment addrAC subrr add0r scalerA mulVf // scale1r subrr.
by rewrite (real_seminorm_zero hN.1).
Qed.

(** Source for [euclidean_affine_curve_lipschitz]: a straight
    Euclidean segment is globally Lipschitz with bound |w|,
    supporting its admissibility in Federer 3.2.46, p. 281.
    Zero bound is retained. *)
Lemma euclidean_affine_curve_lipschitz (R : realType) n (x w : R_n R n) :
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
    setT (fun t=>x+t*:w) (inner_norm (@euclidean_inner_productP R n) w).
Proof.
split; first exact: inner_norm_nonnegative.
move=> t u _ _; rewrite inner_metric_distanceE affine_curve_increment inner_normZ
  real_line_metric_distanceE mulrC; exact: lexx.
Qed.
