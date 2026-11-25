(** Federer (1969), 3.2.17, p. 254:
    the ordinary tangent of the image is
    exactly the range of the injective
    differential. Apply the already proved tangent
    embedding theorem of 3.1.21 to the
    actual restricted inverse. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric RealNormUP NormMetric HilbertFormCompactness
  NormDifferentialUP EuclideanLebesgueDimensions PartialFunctionUP MeasureSetDensity CenteredBallRelations
  MetricBiLipschitzUP EuclideanFullDensityTangent EuclideanInjectiveRetraction
  NormLinearLeftInverseBound FiniteNormLinearRangeClosed TangentConeUP
  TangentEmbeddingUP TangentEmbeddingImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_bilipschitz_ordinary_tangent_plane]:
    Tan(psi(K),psi(a)) equals im Dpsi(a),
    Federer 3.2.17, p. 254. Source
    full density supplies every tangent direction;
    the finite injective differential has closed
    range and a bounded inverse on that range. *)
Theorem euclidean_bilipschitz_ordinary_tangent_plane (R : realType) m n
    (K : set (R_n R m)) (psi : R_n R m -> R_n R n) (lambda : R) a
    (L : Hom (R_n R m) (R_n R n)) :
  @is_metric_bilipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) K psi lambda ->
  0<lambda -> K a -> injective L ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT psi a L ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) (~` K)) a 0%E ->
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) (psi @` K) (psi a)=range L.
Proof.
move=> hB hLam ha hi hPsi hFull.
pose X := R_n R m; pose Y := R_n R n.
pose NX := inner_norm (@euclidean_inner_productP R m).
pose NY := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY := inner_norm_real_norm (@euclidean_inner_productP R n).
have [P [hP hPL]] := euclidean_injective_bounded_left_inverse hi.
have hLower := @norm_linear_left_inverse_lower_bound R X Y NX NY hNY L P hP hPL.
have hClosed := @finite_norm_linear_range_closed R X Y NY hNY n
  (@coordinate_basis R n) (@coordinate_basisP R n) L.
have hInv : norm_inverse_continuous_on_set NX NY K psi a.
  move=> e he; exists (e/lambda); split; first by rewrite divr_gt0.
  move=> x hx hsmall.
  have hh := hB.2 x a hx ha.
  change (is_true (NX (x-a)<=lambda*NY (psi x-psi a))) in hh.
  apply: (le_lt_trans hh _); move: hsmall; by rewrite ltr_pdivlMr // mulrC.
have hTan := @norm_tangent_embedding_image R X Y NX NY hNX hNY setT K psi a L
  hPsi hLower hClosed hInv.
have hSource := euclidean_full_density_tangent hFull.
rewrite hSource in hTan; exact: esym hTan.
Qed.
