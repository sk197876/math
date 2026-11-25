(** Federer (1969), 3.2.27, pp. 262–263: the
    Euclidean norm of the coordinate multiplicity masses
    is at most Hausdorff mass, which is at most their
    sum. Retain an explicit Hausdorff-measurable source
    correction; the printed unrestricted upper bound is
    addressed by the separate two-sheet counterexample. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps InnerNorm InnerMetric
  InnerExterior InnerExteriorBasis InnerExteriorPositivity ExteriorGrading ExteriorNorm ExteriorIndices
  ExteriorMaps FiniteExteriorPowers OrthonormalFamilies CoordinateProjection EuclideanProjectionSpace EuclideanProjectionMetric
  OrthogonalProjectionConstants CoordinateExteriorProjectionNorm EuclideanLebesgueDimensions
  RectifiableSetUP RectifiableOrientationUP RectifiableOrientation RectifiableCoordinateMassUP
  InnerCoordinateUnitFieldIntegrals RectifiableOrientationProjectionIntegral
  MeasurableProjectionMultiplicityIntegral ProjectionMultiplicityIntegral MappingMultiplicity
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialFunctionExtensionality
  MeasureUP MeasureRestriction MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  HausdorffMeasure HilbertFormCompactness ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_coordinate_integrals_exist]: the
    complete vector integral argument in 3.2.27,
    p. 263. Apply 3.2.25 and absolute-coordinate
    replacement in the actual orthonormal exterior basis.
    Continuous dual evaluations, exact projection Jacobians
    and the area formula identify finite actual masses.
    Source measurability is retained as a local correction,
    not inferred from the definition of rectifiability. *)
Theorem rectifiable_coordinate_integrals_exist (R:realType) m n
    (hmn:(m<=n)%N) (W:set (R_n R n)):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  exists a:Lambda n m->R,is_rectifiable_coordinate_masses W a /\
    (Num.sqrt (\sum_lambda (a lambda)^+2))%:E<=
      @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W<=
      (\sum_lambda a lambda)%R%:E.
Proof.
move=>hRect hW.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
pose mu:=measure_restrict H W.
pose V:=exterior_power (R_n R n) m.
pose B:=@exterior_inner_form R (euclidean_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m.
pose hB:=@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m.
pose I:=Finite.clone (Lambda n m) _.
pose e:=@coordinate_e_lambda R n m.
have hStandard:orthonormal_family (@euclidean_inner_product R n) (@coordinate_basis R n).
  by move=>i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
have hOrthonormal:@orthonormal_family R V B I e.
  exact:(@exterior_orthonormal_family R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) n (@coordinate_basis R n) hStandard m).
have hBasis:=@coordinate_e_lambda_basis R (euclidean_two_nonzero R) n m.
have hH:=@hausdorff_measure_is_measure R X m.
have hMu:=measure_restrict_is_measure hH W.
have hFinite:mu setT < +oo by rewrite /mu /measure_restrict setIT; exact hRect.2.
have [T [hT hDomain]]:=@federer_3_2_25 R m n W hRect.
have hMeas:=rectifiable_orientation_measurable hT.
have hUnit w xi:partial_function_graph T w xi ->inner_norm hB xi= 1%R.
  move=>hValue; exact:(rectifiable_orientation_unit_simple hT hValue).2.
have [a [hCoordinates [hLower hUpper]]]:=@inner_unit_field_coordinate_integrals R (Choice.clone X _)
  V B hB I e mu T hOrthonormal hBasis hMu hFinite hMeas hUnit.
have hMasses:is_rectifiable_coordinate_masses W a.
  move=>lambda.
  have [p hP]:=@coordinate_projection_parameter_exists R n m lambda.
  have hArea:=@rectifiable_orientation_projection_integral R m n W T p hRect hW hT.
  have hNormFunction:(fun xi:V=>(projection_norm (euclidean_two_nonzero R) xi p)%:E:extended_real_line R)=
      (fun xi:V=>(`|B xi (e lambda)|)%:E:extended_real_line R).
    apply:funext=>xi; by rewrite (@coordinate_parameter_projection_norm R n m lambda p hP xi).
  rewrite hNormFunction in hArea.
  have hValue:(a lambda)%:E=projection_multiplicity_integral W p.
    exact:(measure_integral_unique (hCoordinates lambda) hArea).
  have hTarget:=@measurable_projection_multiplicity_integral R m n W p hW hRect.2.
  rewrite -hValue in hTarget.
  apply:(@measure_integral_graph_equivalent R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    (@euclidean_lebesgue_measure R m) _ _ _ _ hTarget)=>y z.
  change (@mapping_multiplicity R (Choice.clone X _)
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    (euclidean_projection_linear p) W y=z <->
    @mapping_multiplicity R (Choice.clone X _)
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    (@coordinate_projection R n m lambda) W y=z).
  have hMap:(euclidean_projection_linear p:R_n R n->R_n R m)=@coordinate_projection R n m lambda.
    exact:funext hP.
  by rewrite hMap.
exists a; split; first exact hMasses.
by rewrite /mu /measure_restrict setIT in hLower hUpper; split.
Qed.

(** Source for [federer_3_2_27]: coordinate projection bounds
    of 3.2.27, pp. 262–263, with the explicit
    local correction that W is Hausdorff measurable.
    The input a_lambda law is exactly the displayed
    definition in the book; existence is proved above.
    The separate counterexample explains why the source
    correction cannot simply be removed. *)
Theorem federer_3_2_27 (R:realType) m n (hmn:(m<=n)%N)
    (W:set (R_n R n)) (a:Lambda n m->R):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_rectifiable_coordinate_masses W a ->
  (Num.sqrt (\sum_lambda (a lambda)^+2))%:E<=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W<=
    (\sum_lambda a lambda)%R%:E.
Proof.
move=>hRect hW hA.
have [b [hB hBounds]]:=@rectifiable_coordinate_integrals_exist R m n hmn W hRect hW.
by rewrite (rectifiable_coordinate_masses_unique hA hB).
Qed.
