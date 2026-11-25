(** Federer (1969), 3.2.46, p. 281: the actual constant curve has
    zero tensor-speed integral. This proves the diagonal distance law
    using the real derivative graph, rather than assuming a length axiom. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealMetricBackground ExtendedRealOrderTopology RiemannianTensorUP
  RiemannianCurveCost NormedCurveDerivativeUP PartialFunctionUP
  PartialZeroExtension MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUniqueness
  MeasureIntegralBounds MeasureConullZeroIntegral LebesgueScalarMeasure
  LipschitzUP LipschitzBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_constant_curve_speed_graph]: actual
    zero derivative and speed of a constant path, supporting the
    distance definition in Federer 3.2.46, p. 281. *)
Lemma riemannian_constant_curve_speed_graph (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x (hx : A x) t :
  partial_function_graph (riemannian_curve_speed g (fun _ => x)) t 0.
Proof.
exists 0%R; split.
- exact: (@constant_normed_curve_derivative R (R_n R n)
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) x t).
- rewrite (riemannian_tensor_speed_inner_norm hg hx) inner_norm0.
  by [].
Qed.

(** Source for [riemannian_constant_curve_cost]: a constant
    curve has length zero, supporting rho(x,x)=0 in Federer
    3.2.46, p. 281. Arbitrary interval endpoints are allowed. *)
Lemma riemannian_constant_curve_cost (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x (hx : A x) a b :
  riemannian_curve_cost g (fun _ => x) a b = 0.
Proof.
have hZero : measure_almost_everywhere (@lebesgue_scalar_measure R)
  [set t | partial_function_graph
    (partial_function_zero_extension (0 : extended_real_line R) `[a,b]
      (riemannian_curve_speed g (fun _ => x))) t 0].
  apply: (measure_almost_everywhere_mono (lebesgue_scalar_is_measure R) _
    (measure_almost_everywhere_true (lebesgue_scalar_is_measure R))).
  move=> t _; apply/partial_function_zero_extension_graph.
  case: (pselect ((`[a,b] : set (real_line_metric R)) t))=> ht.
  - left; split=> //; exact: (@riemannian_constant_curve_speed_graph R n A g hg x hx t).
  - by right; split.
have hi := measure_almost_zero_integral (lebesgue_scalar_is_measure R) hZero.
exact: measure_upper_integral_unique (measure_upper_integral_specification _ _) hi.2.1.
Qed.

(** Source for [riemannian_constant_curve_admissible]: the constant
    path on [0,1] is among the genuine Lipschitz curves in the
    definition of rho(x,x), Federer 3.2.46, p. 281. *)
Lemma riemannian_constant_curve_admissible (R : realType) n A x :
  A x -> @is_riemannian_admissible_curve R n A x x (fun _ => x) 0%R 1%R.
Proof.
move=> hx; split; first exact: ler01.
split; first exact: metric_lipschitz_of_bound
  (least_metric_lipschitz_bound (metric_lipschitz_constant_map _ _)).
by split; first move=> t _.
Qed.
