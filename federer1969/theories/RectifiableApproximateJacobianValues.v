(** Federer (1969), 3.2.22, pp. 258–259:
    actual intrinsic Jacobian values exist almost everywhere
    in every exterior degree on the original rectifiable domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure
  RectifiableSetUP RectifiableDensityDifferentiability MeasureApproximateJacobianUP
  MeasureApproximateJacobianLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_approximate_jacobian_values_almost]:
    the use of 3.2.19 and the intrinsic norm
    definition from 3.2.20 in Federer 3.2.22,
    p. 259. Actual approximate differentiability supplies
    a finite nonnegative intrinsic q-Jacobian at almost
    every source point, even when q differs from m.
    No values are assigned to the public partial Jacobian
    at exceptional undefined points. *)
Theorem rectifiable_approximate_jacobian_values_almost (R:realType) m n k q
    (W:set (R_n R n)) (F:R_n R n->R_n R k):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) setT F ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W [set w|
      exists j:R,has_measure_approximate_jacobian
        (measure_restrict (@hausdorff_measure R
          (inner_metric_space (@euclidean_inner_productP R n)) m) W) m q
        (partial_function_source_restrict W (partial_function_total F)) w j].
Proof.
move=>hRect hW hF.
pose rho:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have hr:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have hAll:=rectifiable_density_and_differentiability_global hRect hW hF.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hr _
  ((measure_almost_everywhere_on_implication _ _ _).1 hAll))=>w hPoint hw.
have hApprox:=(hPoint hw).2.2.
exact:(@measure_approximate_jacobian_value_exists R n k (measure_restrict rho W) m q
  (partial_function_source_restrict W (partial_function_total F)) w
  (measure_restrict_is_measure hr W) hApprox).
Qed.
