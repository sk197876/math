(** Federer (1969), 3.2.33, p. 270: prove existence
    of every displayed datum of the smooth counterexample. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMetricLipschitzLaws
  EuclideanOpenUnitCube EuclideanUnitCubeRectifiable
  PositiveUnitIntervalBumpUP DenseSmallIntervalFamilyUP IntervalBumpSeriesUP IntervalBumpPrimitiveUP IntervalBumpConstruction
  ScalarCylinderMapUP ScalarCylinderMapExistence ScalarCylinderSmooth ScalarCylinderLipschitz
  ScalarCylinderPositiveFibre ScalarCylinderPositiveIntegral RectifiablePositiveFibreCoarea
  SmoothCoareaRemainderExampleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_coarea_remainder_example_exists]: the whole
    smooth counterexample in Federer 3.2.33, p. 270,
    for every mu<m, represented as m=(mu+1)+k and
    target dimension mu+1. Actual bump, interval family,
    normally convergent series and integral primitive discharge
    the scalar construction. Actual coordinates prove smoothness,
    every fibre's nullity, the exact low-rank locus, its positive
    mass and the strictly positive original public Jacobian
    integral. The prior 3.2.32 theorem is applied with every
    hypothesis proved. Auxiliary choices stay inside this opaque
    existence theorem; no additional hypothesis is imposed. *)
Theorem smooth_coarea_remainder_example_exists (R:realType) mu k:
  exists (a b:nat->R) (phi psi g:R->R) (F:R_n R ((mu+1)+k)->R_n R (mu+1)),
    is_positive_unit_interval_bump phi /\is_dense_small_interval_family a b /\
    is_interval_bump_series a b phi psi /\is_interval_bump_primitive a b psi g /\
    is_scalar_cylinder_map g F /\is_smooth_coarea_remainder_example F.
Proof.
have [a [b [phi [psi [g [hPhi [hFamily [hSeries hPrimitive]]]]]]]]:=interval_bump_construction_exists R.
have [F hF]:=@scalar_cylinder_map_exists R mu k g.
have [hRect [hMeas hMass]]:=euclidean_open_unit_cube_measure_rectifiable R ((mu+1)+k).
have [L [hL hLip]]:=scalar_cylinder_lipschitz hF (interval_primitive_lipschitz hPrimitive).
have hPartial:=(@partial_total_restriction_lipschitz R
  (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k)))
  (inner_metric_space (@euclidean_inner_productP R (mu+1)))
  (@euclidean_open_unit_cube R ((mu+1)+k)) F L).2 hLip.
have hY:=scalar_cylinder_original_positive_fibre_empty hF hPrimitive.
have [hIntegral hPositive]:=scalar_cylinder_positive_remainder_integral hF hFamily hPrimitive.
exists a,b,phi,psi,g,F; split; first exact hPhi.
split; first exact hFamily.
split; first exact hSeries.
split; first exact hPrimitive.
split; first exact hF.
constructor.
- exact:(scalar_cylinder_smooth hF (interval_primitive_smooth hPrimitive)).
- exact hRect.
- exact hMeas.
- by exists L.
- apply:(@federer_3_2_32 R ((mu+1)+k) (mu+1) ((mu+1)+k) mu
    (partial_function_source_restrict (@euclidean_open_unit_cube R ((mu+1)+k)) (partial_function_total F)) L).
  + by rewrite -addnA leq_addr.
  + by rewrite partial_function_source_restrict_domain partial_function_total_domain setIT.
  + by rewrite partial_function_source_restrict_domain partial_function_total_domain setIT.
  + exact hPartial.
- exact hY.
- exact hPositive.
- exact hIntegral.
Qed.

(** Source for [federer_3_2_33_smooth]: the complete smooth
    counterexample assertion of Federer 3.2.33, p. 270,
    in its arbitrary printed source dimension m and every
    natural mu<m, with target dimension mu+1. The auxiliary
    complementary dimension is proved to exist by arithmetic;
    no positive lower-dimensional parameter is required. The
    analytic impossibility discussion is a separate theorem. *)
Theorem federer_3_2_33_smooth (R:realType) m mu:
  (mu<m)%N ->exists F:R_n R m->R_n R (mu+1),is_smooth_coarea_remainder_example F.
Proof.
move=>hMu.
have hBound:(mu+1<=m)%N by rewrite addn1.
have hDimension:((mu+1)+(m-(mu+1)))%N=m:=subnKC hBound.
rewrite -hDimension.
have [a [b [phi [psi [g [F [hPhi [hFamily [hSeries [hPrimitive [hF hExample]]]]]]]]]]]:=
  @smooth_coarea_remainder_example_exists R mu (m-(mu+1)).
by exists F.
Qed.
