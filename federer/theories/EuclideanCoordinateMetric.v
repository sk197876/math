(** Euclidean coordinate lines for Federer (1969), 2.5.10, p. 101, using the
    actual dot-product metric of 1.7.1, p. 28. These are geometric
    prerequisites, not statements of the measure example. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  CoordinateProjection InnerNorm InnerNormInequalities InnerMetric RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_coordinate_unit_norm]: the
    standard basis is orthonormal for the displayed dot product
    in Federer 1.7.1, p. 28; supporting the
    coordinate lines of 2.5.10, p. 101. *)
Lemma euclidean_coordinate_unit_norm (R : realType) n (i : 'I_n) :
  inner_norm (@euclidean_inner_productP R n) (@coordinate_basis R n i)= 1.
Proof.
apply: inner_norm_value; first exact: ler01.
by rewrite expr1n euclidean_inner_basis /coordinate_basis ffunE eqxx.
Qed.

(** Source for [euclidean_coordinate_norm_bound]: Cauchy's
    inequality in Federer 1.7.1, p. 28, applied
    to a standard unit vector. This bounds the projection
    used in 2.5.10, p. 101. *)
Lemma euclidean_coordinate_norm_bound (R : realType) n (i : 'I_n) (x : R_n R n) :
  `|x i|<=inner_norm (@euclidean_inner_productP R n) x.
Proof.
have h := inner_cauchy (@euclidean_inner_productP R n) x (@coordinate_basis R n i).
by rewrite euclidean_inner_basis euclidean_coordinate_unit_norm mulr1 in h.
Qed.

(** Source for [euclidean_coordinate_nonexpanding]: the
    coordinate projection in Federer 2.5.10, p. 101,
    has Lipschitz constant at most one by 1.7.1,
    p. 28. This holds in every finite dimension. *)
Lemma euclidean_coordinate_nonexpanding (R : realType) n (i : 'I_n)
    (x y : inner_metric_space (@euclidean_inner_productP R n)) :
  @mdist R [the metricType R of real_line_metric R] (x i) (y i)<=mdist x y.
Proof.
rewrite real_line_metric_distanceE inner_metric_distanceE.
have h := euclidean_coordinate_norm_bound i (x-y).
by rewrite !ffunE in h.
Qed.

(** Source for [euclidean_coordinate_line]: a coordinate
    line through v, supporting the horizontal and vertical
    tests in Federer 2.5.10, p. 101. The
    vector and metric are those of 1.7.1, p. 28. *)
Definition euclidean_coordinate_line (R : realType) n (i : 'I_n)
    (v : inner_metric_space (@euclidean_inner_productP R n)) (t : real_line_metric R) :
    inner_metric_space (@euclidean_inner_productP R n) := v+t*:(@coordinate_basis R n i).

(** Source for [euclidean_coordinate_line_distance]: coordinate
    line parametrisations preserve real distance, supporting
    Federer 2.5.10, p. 101, from the norm
    laws of 1.7.1, p. 28. *)
Lemma euclidean_coordinate_line_distance (R : realType) n (i : 'I_n)
    (v : inner_metric_space (@euclidean_inner_productP R n)) (s t : real_line_metric R) :
  mdist (euclidean_coordinate_line i v s) (euclidean_coordinate_line i v t)=mdist s t.
Proof.
rewrite inner_metric_distanceE /euclidean_coordinate_line opprD addrACA subrr add0r.
by rewrite -scalerBl inner_normZ euclidean_coordinate_unit_norm mulr1 real_line_metric_distanceE.
Qed.

(** Source for [euclidean_coordinate_retraction]: the
    coordinate inverse on a line, supporting the line tests
    of Federer 2.5.10, p. 101; its affine
    formula uses the Euclidean model of 1.7.1, p. 28. *)
Definition euclidean_coordinate_retraction (R : realType) n (i : 'I_n)
    (v x : inner_metric_space (@euclidean_inner_productP R n)) : real_line_metric R := x i-v i.

(** Source for [euclidean_coordinate_line_retraction]: the
    coordinate inverse cancels the line parametrisation in
    Federer 2.5.10, p. 101, supporting Hausdorff
    length invariance by the image estimate of 2.10.11,
    p. 176. *)
Lemma euclidean_coordinate_line_retraction (R : realType) n (i : 'I_n)
    (v : inner_metric_space (@euclidean_inner_productP R n)) :
  cancel (euclidean_coordinate_line i v) (euclidean_coordinate_retraction i v).
Proof.
move=> t; rewrite /euclidean_coordinate_retraction /euclidean_coordinate_line /coordinate_basis !ffunE eqxx /=.
change (v i+(t*1)-v i=t).
by rewrite mulr1 addrAC subrr add0r.
Qed.

(** Source for [euclidean_coordinate_retraction_nonexpanding]:
    the inverse on a coordinate line extends to a nonexpanding
    map of the ambient Euclidean space, supporting Federer
    2.5.10, p. 101; Cauchy's inequality is
    Federer 1.7.1, p. 28. *)
Lemma euclidean_coordinate_retraction_nonexpanding (R : realType) n (i : 'I_n)
    (v x y : inner_metric_space (@euclidean_inner_productP R n)) :
  mdist (euclidean_coordinate_retraction i v x) (euclidean_coordinate_retraction i v y)<=mdist x y.
Proof.
rewrite real_line_metric_distanceE /euclidean_coordinate_retraction opprB addrA subrK.
exact (@euclidean_coordinate_nonexpanding R n i x y).
Qed.
