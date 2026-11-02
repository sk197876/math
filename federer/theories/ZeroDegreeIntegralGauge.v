(** Federer (1969), 3.2.35, p. 271:
    the zeroth intrinsic volume of every
    nonempty source is one. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanLebesgueDimensions PointMassMeasure
  ProjectedVolumeMeasurability ProjectionBetaZeroDegree IntegralGeometricGauge OrthogonalProjectionProbability
  NonnegativeExtendedProbabilityConstant ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_degree_projected_volume]: every
    actual projection of a nonempty source to
    the sole zero-dimensional point has unit
    volume, supporting zeta^0 in Federer
    3.2.35, p. 271. No measurability,
    boundedness or convexity is required. *)
Lemma zero_degree_projected_volume (R:realType) n
    (p:orthogonal_projection_metric_space R n 0)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  S!=set0 ->projected_volume_function S p= 1%E.
Proof.
move=>[a ha].
have hImage:euclidean_projection_linear p @` S=setT.
  apply/seteqP; split=>x hx; first exact Logic.I.
  exists a=>//; by rewrite (coordinate_zero (euclidean_projection_linear p a)) (coordinate_zero x).
rewrite /projected_volume_function hImage /euclidean_lebesgue_measure.
exact:(@point_mass_in R [the choiceType of inner_metric_space (@euclidean_inner_productP R 0)] 0 setT I).
Qed.

(** Source for [zero_degree_integral_geometric_gauge]:
    the exact zeta^0(S)=1 convention of Federer
    3.2.35, p. 271, agrees with the
    existing gauge at degree zero. Actual
    projected-volume constancy and the proved
    beta normalization discharge its full laws. *)
Theorem zero_degree_integral_geometric_gauge (R:realType) n (h0n:(0<=n)%N)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  S!=set0 ->@integral_geometric_gauge R n 0 h0n 1 S= 1%E.
Proof.
move=>hNonempty.
have hFunction:projected_volume_function (m:=0) S=
    (fun _:orthogonal_projection_metric_space R n 0=>(1%E:extended_real_line R)).
  apply:funext=>p; exact:zero_degree_projected_volume hNonempty.
rewrite /integral_geometric_gauge (@projection_beta_zero_degree R n h0n 1 (lexx 1)) invr1 mul1e hFunction.
exact:(@probability_nonnegative_extended_constant_norm R _ _ (@theta_star_is_measure R n 0 h0n)
  1 1 (@theta_star_total R n 0 h0n) (@lee01 R) (lexx _)).
Qed.
