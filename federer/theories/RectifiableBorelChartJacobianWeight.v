(** Federer (1969), 3.2.22, pp. 259–260:
    Borel chart-image weights approximate the intrinsic
    Jacobian from both sides with the printed lambda powers. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP NormDifferentialDirectional LipschitzUP LipschitzBasic NormMetricScaleContinuity
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction HausdorffMeasure EuclideanLebesgueDimensions
  RectifiableCompactChartsUP RectifiableChartInverseExtension RectifiableParameterJacobianBounds
  RectifiableParameterChartPoints MeasureApproximateJacobian EuclideanLinearJacobian BorelFunctionUP BorelFunctionBasic
  RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_borel_chart_jacobian_weight]:
    supporting measurable intrinsic densities in Federer
    3.2.22, pp. 259–260. A Borel scalar
    representative of J_q(F composed psi) is pulled
    through the same-bound global inverse of psi.
    Exact actual differential values and 3.2.19 give
    the two lambda^q bounds almost everywhere on psi(A).
    No measurability of the auxiliary intrinsic-Jacobian
    representative or preimage of a completed null set
    is assumed. *)
Theorem rectifiable_borel_chart_jacobian_weight (R:realType) m n k q
    (lambda:R) (W:set (R_n R n)) (K A:set (R_n R m))
    (psi:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R k))
    (J0:R_n R n->R)
    (J:inner_metric_space (@euclidean_inner_productP R m)->real_line_metric R):
  1<lambda ->is_uniform_compact_rectifiable_chart lambda K psi ->A `<=` K ->
  psi @` K `<=` W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo)%E ->
  is_metric_lipschitz setT F ->
  is_partial_function_total_extension
    (measure_approximate_jacobian (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W) m q
      (partial_function_source_restrict W (partial_function_total F))) J0 ->
  is_borel_function J ->(forall a,0<=J a) ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A [set a|
    exists H:Hom (R_n R m) (R_n R k),
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R k)) setT (fun x=>F (psi x)) a H /\
      J a=euclidean_linear_jacobian q H] ->
  exists h:inner_metric_space (@euclidean_inner_productP R n)->real_line_metric R,
    is_borel_function h /\ (forall w,0<=h w) /\
    measure_almost_everywhere_on (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) (psi @` A) [set w|
        (lambda^+q)^-1*J0 w<=h w /\ h w<=lambda^+q*J0 w].
Proof.
move=>hLambda hChart hAK hKW hW hFinite hF hJ0 hJB hJNonnegative hJActual.
have [G [hG hInverse]]:=uniform_compact_chart_inverse_global_extension hChart.
have hGLip:=metric_lipschitz_of_bound hG.
have hGCont:continuous (G:inner_metric_space (@euclidean_inner_productP R n)->
    inner_metric_space (@euclidean_inner_productP R m)).
  have [L [hL hB]]:=hGLip; apply:(metric_fixed_lipschitz_continuous (ltW hL))=>a b.
  exact:(hB.2 a b Logic.I Logic.I).
pose h:=fun w:inner_metric_space (@euclidean_inner_productP R n)=>(J (G w):real_line_metric R).
exists h; split; first exact:(borel_function_composition (continuous_borel_function hGCont) hJB).
split; first by move=>w; exact:(hJNonnegative (G w)).
have hBounds:=rectifiable_parameter_jacobian_bounds hLambda hChart hKW hW hFinite hF hJ0.
pose hm:=euclidean_lebesgue_is_measure R m.
have hBoth:=measure_almost_everywhere_and hm
  ((measure_almost_everywhere_on_implication _ _ _).1 hBounds)
  ((measure_almost_everywhere_on_implication _ _ _).1 hJActual).
have hParam:measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A
    [set a|(lambda^+q)^-1*J0 (psi a)<=h (psi a) /\ h (psi a)<=lambda^+q*J0 (psi a)].
  apply:(measure_almost_everywhere_on_implication _ _ _).2.
  apply:(measure_almost_everywhere_mono hm _ hBoth)=>a [hBoundA hActualA] ha.
  have hKa:=hAK a ha.
  have [D [H [hD [hH hSandwich]]]]:=hBoundA hKa.
  have [H0 [hH0 hValue]]:=hActualA ha.
  have hEq:H0=H:=@norm_differential_unique R (R_n R m) (R_n R k)
    (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R k))
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R k)) setT (fun x=>F (psi x)) a H0 H hH0 hH.
  change ((lambda^+q)^-1*J0 (psi a)<=J (G (psi a)) /\
    J (G (psi a))<=lambda^+q*J0 (psi a)).
  by rewrite (hInverse a hKa) hValue hEq.
exact:(euclidean_lipschitz_almost_pushforward
  (metric_lipschitz_of_bound (rectifiable_chart_global_bound hChart)) hParam).
Qed.
