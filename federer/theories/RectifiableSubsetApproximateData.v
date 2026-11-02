(** Federer (1969), 3.2.32, pp. 269–270: keep
    the approximate differential and Jacobian relative to the
    original W while applying 3.2.22 on smaller measurable
    source pieces. The omitted-density and cone equalities
    are proved before transferring the exact partial graphs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction LipschitzUP
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure RectifiableSetUP
  MeasureApproximateTangentUP MeasureApproximateDifferentialUP MeasureApproximateDifferentialUniqueness
  MeasureApproximateDifferentialSubset MeasureApproximateJacobianUP MeasureApproximateJacobian
  FiniteMeasurableTangentRestriction RectifiableApproximateJacobianValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section SubsetApproximateData.
Variable R:realType.
Variables m n v:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R n)).
Local Notation H:=(@hausdorff_measure R X m).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R v)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R v)).

(** Source for [rectifiable_subset_approximate_data_agreement]: supporting
    unchanged original approximate data in Federer 3.2.32,
    pp. 269–270. On each measurable S contained in W,
    the actual partial differential predicates and Jacobian
    graphs in every exterior degree agree almost everywhere.
    Neither a derivative field nor equality of source sets is
    assumed. The source measure retains its original degree m. *)
Theorem rectifiable_subset_approximate_data_agreement (W S:set X)
    (F:R_n R n->R_n R v) q:
  is_measure_m_rectifiable H m W ->measure_measurable H W ->
  measure_measurable H S ->S `<=` W ->
  @is_metric_lipschitz R X (inner_metric_space (@euclidean_inner_productP R v)) setT F ->
  measure_almost_everywhere_on H S [set a|
    (forall d:partial_function (R_n R n) (R_n R v),
      is_measure_approximate_differential NY hNX (measure_restrict H W) m
        (partial_function_source_restrict W (partial_function_total F)) a d <->
      is_measure_approximate_differential NY hNX (measure_restrict H S) m
        (partial_function_source_restrict S (partial_function_total F)) a d) /\
    (forall j,partial_function_graph (measure_approximate_jacobian (measure_restrict H W) m q
        (partial_function_source_restrict W (partial_function_total F))) a j <->
      partial_function_graph (measure_approximate_jacobian (measure_restrict H S) m q
        (partial_function_source_restrict S (partial_function_total F))) a j)].
Proof.
move=>hRect hW hS hSW hF.
have hH:=@hausdorff_measure_is_measure R X m.
have hHS:=measure_restrict_is_measure hH S.
have hCones:=@finite_measurable_subset_approximate_tangent_equal R m n W S hW hS hSW hRect.2.
have hValues:=@rectifiable_approximate_jacobian_values_almost R m n v q W F hRect hW hF.
have hAll:=measure_almost_everywhere_and hH
  ((measure_almost_everywhere_on_implication _ _ _).1 hCones)
  ((measure_almost_everywhere_on_implication _ _ _).1 hValues).
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hH _ hAll)=>a [hConea hValuea] ha.
have hCone:=hConea ha.
have [j0 [d0 [hD0 hNorm0]]]:=hValuea (hSW a ha).
have hD0S:=@measure_approximate_differential_subset_same_cone R (R_n R n) (R_n R v)
  NX NY hNX hNY H m S W F a d0 hH hSW hCone hD0.
have hD d:
    is_measure_approximate_differential NY hNX (measure_restrict H W) m
      (partial_function_source_restrict W (partial_function_total F)) a d <->
    is_measure_approximate_differential NY hNX (measure_restrict H S) m
      (partial_function_source_restrict S (partial_function_total F)) a d.
  split.
  - exact (@measure_approximate_differential_subset_same_cone R (R_n R n) (R_n R v)
      NX NY hNX hNY H m S W F a d hH hSW hCone).
  - move=>hdS.
    have hEqual:=measure_approximate_differential_unique hdS hD0S.
    by rewrite hEqual.
split; first exact hD.
move=>j; rewrite !measure_approximate_jacobian_graph.
split; move=>[d [hd hNorm]]; exists d; split=>//.
- exact ((hD d).1 hd).
- exact ((hD d).2 hd).
Qed.
End SubsetApproximateData.
