(** Federer (1969), 3.2.46, p. 281: any two original
    interval-only admissible curves with a common endpoint
    yield an admissible concatenation with exactly the sum
    of their lengths. Extensions serve only as existence proofs. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RealMetricBackground LipschitzUP LipschitzIntervalRetraction
  StieltjesSubstitution MetricCurveConcatenation RiemannianTensorUP RiemannianCurveCost
  RiemannianCurveRetraction RiemannianCurveConcatenation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_admissible_curves_concatenation]:
    the actual path construction proving the triangle assertion
    in Federer 3.2.46, p. 281. No regularity outside either
    original interval or independent length-additivity premise
    is required. Degenerate intervals are retained. *)
Theorem riemannian_admissible_curves_concatenation (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x y z
    (C D : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b c d :
  is_riemannian_admissible_curve A x y C a b ->
  is_riemannian_admissible_curve A y z D c d ->
  exists E u v, is_riemannian_admissible_curve A x z E u v /\
    riemannian_curve_cost g E u v =
      (riemannian_curve_cost g C a b + riemannian_curve_cost g D c d)%E.
Proof.
move=> hC hD.
pose C0 := fun t : real_line_metric R=>C (segment_retraction a b t).
pose D0 := fun t : real_line_metric R=>D (segment_retraction c d t).
have [L [hL hCB]] := hC.2.1.
have [M [hM hDB]] := hD.2.1.
have hC0 := @metric_curve_retraction_lipschitz R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] C a b L hC.1 hCB.
have hD0 := @metric_curve_retraction_lipschitz R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] D c d M hD.1 hDB.
have hCA : forall t, A (C0 t) := metric_curve_retraction_image hC.1 hC.2.2.1.
have hDA : forall t, A (D0 t) := metric_curve_retraction_image hD.1 hD.2.2.1.
have hCAd := riemannian_retracted_curve_admissible hC.
have hDAd := riemannian_retracted_curve_admissible hD.
have hCStart : C0 a = x := hCAd.2.2.2.1.
have hCEnd : C0 b = y := hCAd.2.2.2.2.
have hDStart : D0 c = y := hDAd.2.2.2.1.
have hDEnd : D0 d = z := hDAd.2.2.2.2.
have hJoin : C0 b = D0 c by rewrite hCEnd hDStart.
have [hAd hCost] := @riemannian_global_curves_concatenation R n A g hg C0 D0
  a b c d L M hC0 hD0 hCA hDA hC.1 hD.1 hJoin.
change (is_riemannian_admissible_curve A (C0 a) (D0 d)
  (metric_curve_concatenation C0 D0 b c) a (b+d-c)) in hAd.
rewrite hCStart hDEnd in hAd.
have hCCost : riemannian_curve_cost g C0 a b = riemannian_curve_cost g C a b.
  exact: esym (riemannian_retracted_curve_cost hg hC).
have hDCost : riemannian_curve_cost g D0 c d = riemannian_curve_cost g D c d.
  exact: esym (riemannian_retracted_curve_cost hg hD).
change (riemannian_curve_cost g (metric_curve_concatenation C0 D0 b c) a (b+d-c) =
  (riemannian_curve_cost g C0 a b + riemannian_curve_cost g D0 c d)%E) in hCost.
rewrite hCCost hDCost in hCost.
exists (metric_curve_concatenation C0 D0 b c),a,(b+d-c); exact: conj hAd hCost.
Qed.
