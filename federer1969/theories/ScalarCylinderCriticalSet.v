(** Federer (1969), 3.2.33, p. 270: identify the exact
    critical source X using the original partial-map definition
    of 3.2.32 rather than a substituted differential field. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction MeasureRestriction HausdorffMeasure
  MeasureApproximateDifferentialUP MeasureApproximateDifferentialUniqueness PartialImageDimensionUP
  RectifiablePositiveFibreCoareaUP PartialTotalLinearImageDimension RealOpenIntervals
  EuclideanOpenUnitCube ScalarCylinderMapUP ScalarCylinderRank ScalarCylinderApproximateData IntervalBumpPrimitiveUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_cylinder_exact_critical_source]: the
    printed equality X=W intersect {x:x_(mu+1) in T minus V},
    Federer 3.2.33, p. 270. Every actual approximate
    differential is compared with the ordinary differential
    through the independent exact graph laws. The full cone
    identifies partial image dimension with actual rank; the
    scalar primitive's proved zero set completes both implications.
    All source points and both zero coordinate blocks remain. *)
Theorem scalar_cylinder_exact_critical_source (R:realType) mu k (a b:nat->R) (psi g:R->R)
    (F:R_n R ((mu+1)+k)->R_n R (mu+1)):
  is_scalar_cylinder_map g F ->is_interval_bump_primitive a b psi g ->
  let f:=partial_function_source_restrict (@euclidean_open_unit_cube R ((mu+1)+k)) (partial_function_total F) in
  partial_approximate_image_dimension_locus ((mu+1)+k) mu f=
    [set x|euclidean_open_unit_cube x /\
      (real_open_interval 0 1 `\` (\bigcup_j real_open_interval (a j) (b j)))
        (x (lshift k (rshift mu ord0)))].
Proof.
move=>hF hPrimitive f.
have hDom:partial_function_domain f=@euclidean_open_unit_cube R ((mu+1)+k).
  by rewrite /f partial_function_source_restrict_domain partial_function_total_domain setIT.
rewrite /partial_approximate_image_dimension_locus hDom.
apply/seteqP; split=>x.
- move=>[hx [d [hd hLow]]].
  have [L [hL [hOrdinary [hTotal [hJ hLower]]]]]:=scalar_cylinder_actual_approximate_data hF hPrimitive hx.
  have he:=measure_approximate_differential_unique hd hTotal.
  rewrite he in hLow.
  have hRanks:=(partial_total_linear_low_image_iff mu L).1 hLow.
  have hZero:=(scalar_cylinder_low_rank_iff_zero hL).1 hRanks.
  have hxT:real_open_interval 0 1 (x (lshift k (rshift mu ord0))).
    have /andP [h0 h1]:=hx (lshift k (rshift mu ord0)); by split.
  split; first exact hx.
  split; first exact hxT.
  exact:(interval_primitive_zero_coefficient hPrimitive hxT).1 hZero.
- move=>[hx [hxT hNot]].
  have [L [hL [hOrdinary [hTotal [hJ hLower]]]]]:=scalar_cylinder_actual_approximate_data hF hPrimitive hx.
  split; first exact hx.
  exists (partial_function_total L); split; first exact hTotal.
  apply:(partial_total_linear_low_image_iff mu L).2.
  apply:(scalar_cylinder_low_rank_iff_zero hL).2.
  exact:(interval_primitive_zero_coefficient hPrimitive hxT).2 hNot.
Qed.
