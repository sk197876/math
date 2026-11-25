(** Federer (1969), 4.1.26, p. 384:
    under the original connected-image hypotheses
    and injectivity of f on A, sign det Df
    is Lebesgue almost constant on the
    original positive-Jacobian part of A. Use
    3.2.3's positive-Jacobian null-preimage consequence;
    no null-set pullback over the whole source
    and no global inverse are asserted. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric InnerNorm InnerMetric HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct MetricDiameter LipschitzUP
  EuclideanLebesgueDimensions EuclideanHausdorffLebesgue HausdorffMeasure
  MeasureUP MeasureAlmostUP MeasureAlmostBasic BorelAreaSelection PositiveJacobianNullPreimage
  PartialFunctionUP LipschitzDegreeSealed LipschitzDeterminantSign
  LipschitzDegreeBoundaryImage LipschitzDegreeConnectedImage
  CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_degree_injective_sign_almost_constant]:
    the last assertion of 4.1.26, p. 384.
    All original source hypotheses are retained,
    including injectivity only on A and
    the explicit positive-Jacobian locus. *)
Theorem lipschitz_degree_injective_sign_almost_constant (R:realType)
    (h2:(1+1:R)!=0) m (f:R_n R m->R_n R m)
    (hLip:@is_metric_lipschitz R
      (inner_metric_space (@euclidean_inner_productP R m))
      (inner_metric_space (@euclidean_inner_productP R m)) setT f)
    (A:set (R_n R m))
    (hA:measure_measurable (@euclidean_lebesgue_measure R m) A)
    (hBound:@metric_set_bounded R
      (inner_metric_space (@euclidean_inner_productP R m)) A):
  @connected (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) A->
  (forall y,(f @` A) y->~(f @` lipschitz_degree_source_boundary A) y)->
  {in A &,injective f}->
  exists c:R,measure_almost_everywhere_on (@euclidean_lebesgue_measure R m)
    (A `&` positive_euclidean_jacobian_locus f)
    [set x|partial_function_graph (@lipschitz_determinant_sign R m f) x c].
Proof.
move=>hConnected hDisjoint hInjective.
have[c hConstant]:=@lipschitz_degree_connected_image_almost_constant
  R h2 m f hLip A hA hBound hConnected hDisjoint.
pose N:=(f @` A) `\` [set y|partial_function_graph (@LipschitzDegree.value R m f A) y c].
have hNull:(@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R m)) m) N=0%E.
  rewrite (@euclidean_hausdorff_spherical_lebesgue R m N).1;exact:hConstant.
have hPreimage:=@positive_jacobian_null_preimage R m m f N hLip hNull.
exists c;apply:(@measure_null_subset R (R_n R m)
  (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m)
  ((A `&` positive_euclidean_jacobian_locus f) `\`
    [set x|partial_function_graph (@lipschitz_determinant_sign R m f) x c])
  (positive_euclidean_jacobian_locus f `&` (f @^-1` N)) _ hPreimage).
move=>x [[hx hJacobian] hNot];split;first exact:hJacobian.
split.
- exists x;by [].
- move=>hDegree;apply:hNot.
  exact:(@lipschitz_degree_injective_fibre R m f A x c hInjective hx hDegree).
Qed.
