(** Federer (1969), 3.2.26(3), p. 262: on a
    Borel partition member S, the projection Jacobian is
    evaluated on the orientation originally chosen on W.
    Prove the tangent restriction rather than adding it
    as an assumption on the partition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerNorm InnerMetric HilbertFormCompactness ExteriorGrading AssociatedSubspace
  EuclideanProjectionSpace EuclideanProjectionMetric OrthogonalProjectionConstants
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  RectifiableOrientationUP RectifiableProjectionJacobian FiniteBorelTangentRestriction
  MeasureApproximateJacobian MeasureRestriction HausdorffMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic
  TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_orientation_subset_projection_jacobians]: the
    first displayed integral in 3.2.26(3), p. 262,
    on a Borel member of the chosen partition. The
    actual intrinsic approximate Jacobian on S agrees with
    the projection norm of T(w) on one conull source
    set, simultaneously for all projection parameters. *)
Theorem rectifiable_orientation_subset_projection_jacobians (R:realType) m n
    (W S:set (R_n R n))
    (T:partial_function (R_n R n) (exterior_power (R_n R n) m)):
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) W ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) S ->S `<=` W ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W < +oo ->
  is_rectifiable_measurable_orientation W T ->
  measure_almost_everywhere_on (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) S [set w|
    exists xi,partial_function_graph T w xi /\forall p:orthogonal_projection_metric_space R n m,
      partial_function_graph (measure_approximate_jacobian (measure_restrict
        (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) S) m m
        (partial_function_source_restrict S (partial_function_total (euclidean_projection_linear p))))
        w (projection_norm (euclidean_two_nonzero R) xi p)].
Proof.
move=>hW hS hSW hFinite hT.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
have hH:=@hausdorff_measure_is_measure R X m.
have hOrientation:=(measure_almost_everywhere_on_implication _ _ _).1
  (rectifiable_orientation_tangent hT).
have hTangent:=(measure_almost_everywhere_on_implication _ _ _).1
  (@finite_borel_subset_approximate_tangent_equal R m n W S hW hS hSW hFinite).
have hBoth:=measure_almost_everywhere_and hH hOrientation hTangent.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hH _ hBoth)=>w [hOW hTW] hw.
have [xi [hValue [hCone _]]]:=hOW (hSW w hw).
have hEqual:=hTW hw.
have [hSimple hUnit]:=rectifiable_orientation_unit_simple hT hValue.
exists xi; split; first exact hValue; move=>p.
apply:(@projection_jacobian_on_oriented_tangent R m n H S w xi p hH hSimple hUnit).
exact:(eq_trans hEqual hCone).
Qed.
