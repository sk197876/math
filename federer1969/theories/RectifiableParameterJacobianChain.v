(** Federer (1969), 3.2.20, p. 257: the complete
    first displayed Jacobian identity at Lebesgue almost every compact
    parameter point, for an auxiliary total representative of the
    exact intrinsic approximate-Jacobian graph. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction PartialFunctionExtensionUP MeasureUP MeasureBasic MeasureAlmostUP
  MeasureAlmostBasic MeasureRestriction HausdorffMeasure EuclideanLebesgueDimensions
  LipschitzUP RectifiableCompactChartsUP RectifiableCompactChartLaws
  RectifiableDifferentialChartUP RectifiableChartDensityDifferential EuclideanChartAlmostPullback
  MeasureApproximateJacobianUP MeasureApproximateJacobian MeasureApproximateJacobianChart
  EuclideanLinearJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_parameter_jacobian_chain]: the first
    display and its Lebesgue almost-everywhere qualifier in Federer
    3.2.20, p. 257. The representative J0 agrees only with
    actual intrinsic-Jacobian values; the proof assumes no values at
    undefined points, measurable derivative field or Jacobian chain rule. *)
Theorem rectifiable_parameter_jacobian_chain (R : realType) m n k
    (lambda : R) (W : set (R_n R n)) (K : set (R_n R m))
    (psi : R_n R m -> R_n R n) (F : R_n R n -> R_n R k) (J0 : R_n R n -> R) :
  1<lambda -> is_uniform_compact_rectifiable_chart lambda K psi ->
  psi @` K `<=` W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo)%E ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) setT F ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m m
      (partial_function_source_restrict W (partial_function_total F))) J0 ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) K [set a |
    exists (D : Hom (R_n R m) (R_n R n)) (H : Hom (R_n R m) (R_n R k)),
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R n)) setT psi a D /\
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R k)) setT (fun x=>F (psi x)) a H /\
      J0 (psi a)*euclidean_linear_jacobian m D=euclidean_linear_jacobian m H].
Proof.
move=> hLam hChart hEW hW hFin hF hJ0.
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @hausdorff_measure R Y m.
have hm := @hausdorff_measure_is_measure R Y m.
have hLocal := rectifiable_chart_density_differential hLam hChart hEW hW hFin hF.
have hPointAE : measure_almost_everywhere_on mu (psi @` K)
    [set w | is_rectifiable_differential_chart_point W K psi F w].
  apply: (measure_null_subset hm _ hLocal)=> w [hw hn].
  split; first exact hw; by move=> [_ hPoint]; exact: hn hPoint.
have hParam := euclidean_chart_almost_pullback (uniform_compact_chart_bilipschitz hChart) hPointAE.
apply: (measure_null_subset (euclidean_lebesgue_is_measure R m) _ hParam)=> a [ha hn].
split; first exact ha.
move=> hPoint; apply: hn.
have [b [D [H [j [hb [hVal [hInj [hD [hH [hJac hChain]]]]]]]]]] :=
  rectifiable_differential_chart_jacobian hPoint.
have hba : b=a := @uniform_compact_chart_injective R m n lambda K psi hChart b a hb ha hVal.
rewrite hba in hD hH hChain.
have hGraph := (@measure_approximate_jacobian_graph R n k (measure_restrict mu W) m m
  (partial_function_source_restrict W (partial_function_total F)) (psi a) j).2 hJac.
have hValue : J0 (psi a)=j := hJ0 (psi a) j hGraph.
exists D,H; split; first exact hD.
split; first exact hH.
by rewrite hValue.
Qed.
