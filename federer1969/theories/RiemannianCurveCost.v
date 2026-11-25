(** Federer (1969), 3.2.46, printed p. 281: actual Lipschitz curves
    in A and their tensor-speed integrals. An undefined derivative is
    retained as a missing partial value. Existence of the derivative
    and integrability are later theorems, not definition hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness NormedCurveDerivativeUP
  RealMetricBackground ExtendedRealOrderTopology LipschitzUP
  PartialFunctionUP PartialZeroExtension MeasureUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralBounds MeasureSubsetIntegral
  MeasureStepNonnegative LebesgueScalarMeasure RiemannianTensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_riemannian_admissible_curve]: the curves in the
    infimum defining rho(x,y), Federer 3.2.46, p. 281. K is the
    actual compact interval [a,b]; no global Lipschitz extension is
    required, and degenerate compact intervals are allowed. *)
Definition is_riemannian_admissible_curve (R : realType) n
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (x y : inner_metric_space (@euclidean_inner_productP R n))
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) (a b : R) :=
  (a <= b)%R /\
  @is_metric_lipschitz R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
    `[a,b] C /\
  (forall t, (a <= t <= b)%R -> A (C t)) /\ C a = x /\ C b = y.

(** Source for [riemannian_curve_speed]: the partial actual
    derivative-speed graph in the defining integral, Federer
    3.2.46, p. 281. Derivative uniqueness proves that this is a
    function; a derivative field is not supplied as a premise. *)
Definition riemannian_curve_speed (R : realType) n
    (g : R_n R n -> R_n R n -> R_n R n -> R) (C : R -> R_n R n) :
    partial_function (real_line_metric R) (extended_real_line R).
Proof.
refine (@Build_partial_function _ _
  (fun t z => exists v, has_normed_curve_derivative
    (inner_norm (@euclidean_inner_productP R n)) C t v /\
      z = (riemannian_tensor_speed g (C t) v)%:E) _).
move=> t z w [v [hv ->]] [u [hu ->]].
have h : v = u := punctured_norm_limit_unique
  (inner_norm_real_norm (@euclidean_inner_productP R n)) hv hu.
by rewrite h.
Defined.

(** Source for [riemannian_curve_cost]: the defining curve integral
    in Federer 3.2.46, p. 281. The upper integral is a total order
    value; equality with the genuine integral is proved for the
    admissible Lipschitz curves. Existing integral seals are reused. *)
Definition riemannian_curve_cost (R : realType) n g
    (C : R -> R_n R n) (a b : R) :=
  measure_subset_upper_integral (@lebesgue_scalar_measure R)
    `[a,b] (riemannian_curve_speed g C).

(** Source for [riemannian_curve_cost_nonnegative]: positivity of
    the numbers whose infimum defines rho, Federer 3.2.46, p. 281.
    Every defined speed is nonnegative. This also covers a missing
    derivative domain, for which the upper integral is still ordered. *)
Lemma riemannian_curve_cost_nonnegative (R : realType) n g
    (C : R -> R_n R n) a b : 0 <= riemannian_curve_cost g C a b.
Proof.
apply: (measure_upper_integral_specification _ _).2=> z
  [u [[hu hUpper] hIntegral]].
apply: (measure_step_integral_nonnegative (lebesgue_scalar_is_measure R) _ hIntegral).
apply: (measure_almost_everywhere_mono (lebesgue_scalar_is_measure R) _ hUpper).
move=> t [r [s [hr [hs hsr]]]].
exists r; split=> //.
have hNonneg : 0 <= s.
  have [[_ [v [_ ->]]]|[_ ->]] :=
    (partial_function_zero_extension_graph _ _ _ t s).1 hs.
  - rewrite lee_fin; exact: riemannian_tensor_speed_nonnegative.
  - exact: lexx.
by have h := le_trans hNonneg hsr; rewrite lee_fin in h.
Qed.
