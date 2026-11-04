(** Federer (1969), 3.2.46, p. 281: the constant
    extension of an interval-only Lipschitz curve is a
    legitimate representative of the same path and length.
    The retraction is used only through its proved laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RealMetricBackground LipschitzUP LipschitzBasic
  LipschitzIntervalRetraction LipschitzCurveAbsoluteContinuity
  StieltjesSubstitution RiemannianTensorUP RiemannianCurveCost
  RiemannianCurveIntervalCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_retracted_curve_admissible]: the
    constant extension has the same interval endpoints and lies
    in A, supporting actual curve manipulation in Federer
    3.2.46, p. 281. The original global values are not used. *)
Lemma riemannian_retracted_curve_admissible (R : realType) n A x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b :
  is_riemannian_admissible_curve A x y C a b ->
  is_riemannian_admissible_curve A x y (fun t=>C (segment_retraction a b t)) a b.
Proof.
move=> [hab [[L [hL hBound]] [hImage [hStart hEnd]]]].
have hGlobal := @metric_curve_retraction_lipschitz R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] C a b L hab hBound.
split; first exact hab; split.
- exists L; split; first exact hL; split; first exact hGlobal.1.
  by move=> t u ht hu; exact: hGlobal.2 t u Logic.I Logic.I.
- split.
  + move=> t ht; exact: metric_curve_retraction_image hab hImage t.
  + have hAtA : a <= a <= b by rewrite lexx hab.
    have hAtB : a <= b <= b by rewrite hab lexx.
    split; by rewrite segment_retraction_id.
Qed.

(** Source for [riemannian_retracted_curve_cost]: the actual
    original interval length equals that of its constant
    extension, supporting Federer 3.2.46, p. 281. Endpoint
    derivatives are not imposed on either curve. *)
Lemma riemannian_retracted_curve_cost (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b :
  is_riemannian_admissible_curve A x y C a b ->
  riemannian_curve_cost g C a b =
    riemannian_curve_cost g (fun t=>C (segment_retraction a b t)) a b.
Proof.
move=> hC.
have hD := riemannian_retracted_curve_admissible hC.
have [L [hL hBound]] := hC.2.1.
have hGlobal := @metric_curve_retraction_lipschitz R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] C a b L hC.1 hBound.
apply: (@riemannian_curve_interval_cost_agreement R n A g hg x y x y C
  (fun t=>C (segment_retraction a b t)) a b hC hD
  (metric_lipschitz_curve_locally_absolute_continuous hGlobal)).
by move=> t ht; exact: esym (metric_curve_retraction_agreement C ht).
Qed.
