(** Federer (1969), 3.2.22, pp. 258–260:
    the complete rectifiable coarea theorem, including
    all natural dimensions and exact original domains. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Export RectifiableCoareaUP RectifiableCoareaIntegrands
  RectifiablePartialCoareaImage RectifiablePartialCoareaFibres RectifiablePartialCoareaFormula.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric RealMetricBackground
  PartialFunctionUP PartialMetricLipschitz RectifiableSetUP HausdorffMeasure MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_22]: the complete theorem
    Federer 3.2.22, pp. 258–260. All three
    conclusions follow under the printed hypotheses.
    The proof retains the original partial map and
    weights, actual intrinsic Jacobian and actual fibre
    integral domains, finite-mass rectifiability, signed
    infinite integral values and every natural-dimension
    boundary. Apply erratum p. 5, book p. 258
    lines 20/22 and p. 259 lines 3/4: source R
    and target Q are both retained in the proof. *)
Theorem federer_3_2_22 (R:realType) m n mu v
    (W:set (R_n R n)) (Z:set (R_n R v))
    (f:partial_function (R_n R n) (R_n R v)):
  (mu<=m)%N ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  partial_function_domain f=W ->
  (exists L,@is_partial_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R v)) f L) ->
  partial_function_range f `<=` Z ->
  is_rectifiable_coarea m mu W Z f.
Proof.
move=>hDim hRectW hW hRectZ hZ hDomain hLip hRange; constructor.
- exact:(federer_3_2_22_1 hDim hRectW hW hRectZ hZ hDomain hLip hRange).
- exact:(federer_3_2_22_2 hDim hRectW hW hRectZ hZ hDomain hLip hRange).
- move=>g hGDomain hIntegral.
  exact:(federer_3_2_22_3 hDim hRectW hW hRectZ hZ hDomain hLip hRange hGDomain hIntegral).
Qed.
