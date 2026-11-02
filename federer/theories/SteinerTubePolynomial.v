(** Federer (1969), 3.2.35, p. 271:
    the exact finite tube-volume polynomial, with
    the existing intrinsic-volume gauges and the
    explicit zeroth-degree convention. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  IntegralGeometricGauge ConvexIntrinsicVolumeIntegrals ZeroDegreeIntegralGauge EuclideanBallVolume
  MetricSetDistanceUP EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [steiner_dimension_guard]: supporting
    the finite m=0,...,n range in the
    first display of Federer 3.2.35, p. 271.
    Each index has the existing projection
    dimension guard, with no extra hypothesis. *)
Lemma steiner_dimension_guard n (i:'I_n.+1):(i<=n)%N.
Proof. by have:=ltn_ord i; rewrite ltnS. Qed.

(** Source for [steiner_tube_polynomial]: direct
    finite expression on the right of Steiner's
    formula, Federer 3.2.35, p. 271.
    The existing exponent-one gauge gives zeta^m;
    its independently proved zeroth-degree value
    on nonempty sets is one. Actual alpha
    coefficients and natural radius powers remain. *)
Definition steiner_tube_polynomial (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R) : \bar R :=
  \sum_(i:'I_n.+1) (@integral_geometric_gauge R n i (steiner_dimension_guard i) 1 S)*
    (euclidean_unit_ball_volume R (n-i)*r^+(n-i))%R%:E.

(** Source for [is_steiner_tube_volume]: independent
    statement of the first assertion of Federer
    3.2.35, p. 271, before its dimension
    induction proof. The polynomial uses the
    original S, and d remains the original
    distance specified separately by its laws. *)
Definition is_steiner_tube_volume (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (d:R_n R n->R) : Prop :=
  forall r:R,(0<r)%R ->euclidean_lebesgue_measure n [set x|(d x<r)%R]=steiner_tube_polynomial S r.

(** Source for [steiner_tube_polynomial_nonnegative]:
    supporting the nonnegative integral exchanges
    in Federer 3.2.35, p. 272. Every
    original intrinsic volume is proved nonnegative,
    and actual alpha and nonnegative radius
    powers keep every finite term nonnegative. *)
Lemma steiner_tube_polynomial_nonnegative (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->(0<=r)%R ->
  0<=steiner_tube_polynomial S r.
Proof.
move=>hNonempty hS hBound hr; rewrite /steiner_tube_polynomial.
apply:sume_ge0=>i _; apply:mule_ge0.
- exact:(@convex_intrinsic_volume_nonnegative_finite R n i (steiner_dimension_guard i) 1 S
    hNonempty hS hBound (lexx 1)).1.
- rewrite lee_fin; apply:mulr_ge0; first exact:ltW (euclidean_unit_ball_volumeE R (n-i)).2.
  exact:exprn_ge0.
Qed.

(** Source for [steiner_tube_polynomial_zero_dimension]:
    the empty-product starting case of the
    dimension induction for Federer 3.2.35,
    pp. 271--272. This explicit n=0
    extension has one term, equal to one;
    the printed positive-dimensional formula follows
    from the same induction. *)
Lemma steiner_tube_polynomial_zero_dimension (R:realType)
    (S:set (inner_metric_space (@euclidean_inner_productP R 0))) (r:R):
  S!=set0 ->steiner_tube_polynomial S r= 1.
Proof.
move=>hNonempty.
rewrite /steiner_tube_polynomial big_ord_recr big_ord0 /= ?add0e ?add0r
  (@zero_degree_integral_geometric_gauge R 0 _ S hNonempty) euclidean_unit_ball_volume0 expr0 mulr1.
exact:mul1e.
Qed.
