(** Federer (1969), 3.2.36, p. 272:
    the already proved actual Steiner polynomial
    has finite scalar coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  SteinerTubePolynomial ConvexIntrinsicVolumeIntegrals IntegralGeometricGauge EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [steiner_tube_polynomial_scalar_value]:
    supporting actual scalar polynomial estimates
    in the continuity deduction of Federer
    3.2.36, p. 272. Each actual original
    intrinsic volume is first proved finite;
    only then is its finite part used.
    The equality retains all natural ambient
    dimensions and arbitrary real radius values. *)
Lemma steiner_tube_polynomial_scalar_value (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->
  steiner_tube_polynomial S r=
    (\sum_(i:'I_n.+1) fine (@integral_geometric_gauge R n i (steiner_dimension_guard i) 1 S)*
      (euclidean_unit_ball_volume R (n-i)*r^+(n-i)))%R%:E.
Proof.
move=>hNonempty hS hBound; rewrite /steiner_tube_polynomial -sumEFin.
apply:eq_bigr=>i _.
have [hNonnegative hFinite]:=@convex_intrinsic_volume_nonnegative_finite R n i
  (steiner_dimension_guard i) 1 S hNonempty hS hBound (lexx 1).
have hFinNum: @integral_geometric_gauge R n i (steiner_dimension_guard i) 1 S \is a fin_num.
  by rewrite (ge0_fin_numE hNonnegative).
by rewrite [RHS]EFinM (fineK hFinNum).
Qed.

(** Source for [steiner_tube_scalar_coefficient_nonnegative]:
    supporting the nonnegative coefficient estimate
    used in Federer 3.2.36, p. 272.
    The actual normalized intrinsic volume and
    alpha coefficient are nonnegative, including
    degree zero and lower-dimensional convex sets. *)
Lemma steiner_tube_scalar_coefficient_nonnegative (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (i:'I_n.+1):
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->
  (0<=fine (@integral_geometric_gauge R n i (steiner_dimension_guard i) 1 S)*
    euclidean_unit_ball_volume R (n-i))%R.
Proof.
move=>hNonempty hS hBound.
have [hNonnegative hFinite]:=@convex_intrinsic_volume_nonnegative_finite R n i
  (steiner_dimension_guard i) 1 S hNonempty hS hBound (lexx 1).
have hFinNum: @integral_geometric_gauge R n i (steiner_dimension_guard i) 1 S \is a fin_num.
  by rewrite (ge0_fin_numE hNonnegative).
apply:mulr_ge0; last exact:ltW (euclidean_unit_ball_volumeE R (n-i)).2.
by move:hNonnegative; rewrite -(fineK hFinNum) lee_fin.
Qed.
