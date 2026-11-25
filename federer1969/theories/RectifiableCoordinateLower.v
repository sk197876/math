(** Federer (1969), 3.2.27, pp. 262–263: retain
    the printed lower inequality for arbitrary finite
    rectifiable W whenever its displayed actual coordinate
    integrals exist. Only the upper inequality requires
    the source-measurability correction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric ExteriorIndices
  RectifiableSetUP RectifiableBorelMeasureHull RectifiableCoordinateMassUP
  RectifiableCoordinateProjectionBounds CoordinateMassMonotonicity FiniteCoordinateNormOrder
  HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureHull BorelRegularMeasureUP
  ExtendedRealOrderTopology PartialFunctionBasic MappingMultiplicity CoordinateProjection
  EuclideanLebesgueDimensions MeasureIntegralUP NonnegativeExtendedNormOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_coordinate_projection_lower]: the
    lower inequality in 3.2.27, p. 262, with
    its original arbitrary-source scope. A true Borel
    rectifiable Hausdorff hull has the same Hausdorff
    mass. Fibre inclusion bounds the original actual
    coordinate integrals by those of the hull; monotonicity
    of the nonnegative coordinate norm finishes. No
    hull difference is asserted null. *)
Theorem rectifiable_coordinate_projection_lower (R:realType) m n
    (hmn:(m<=n)%N) (W:set (R_n R n)) (a:Lambda n m->R):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  is_rectifiable_coordinate_masses W a ->
  (Num.sqrt (\sum_lambda (a lambda)^+2))%:E<=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W.
Proof.
move=>hRect hA.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
have hH:=@hausdorff_measure_is_measure R X m.
have [M [hMBorel [hHull hMRect]]]:=rectifiable_borel_measure_hull hRect.
have hMMeas:=borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R X m) hMBorel.
have [b [hB [hLower hUpper]]]:=@rectifiable_coordinate_integrals_exist R m n hmn M hMRect hMMeas.
have hPoint lambda:(0<=a lambda<=b lambda)%R.
  apply/andP; split; first exact:coordinate_masses_nonnegative hA lambda.
  exact:(coordinate_masses_subset_mono (measure_hull_subset hHull) hA hB lambda).
have hNorm:=@finite_nonnegative_coordinate_norm_mono R (Finite.clone (Lambda n m) _) a b hPoint.
have hBound:=le_trans (lee_tofin hNorm) hLower.
have hMass:=measure_hull_equal_measure hH hHull.
by rewrite hMass.
Qed.

(** Source for [rectifiable_coordinate_integral_finite]: the
    actual coordinate integrals in 3.2.27, p. 262,
    are finite whenever they exist on a finite
    rectifiable source. Derive finiteness through a true
    Borel rectifiable measure hull and actual fibre
    monotonicity; the source itself need not be measurable.
    This justifies the real-valued coordinate-mass interface. *)
Theorem rectifiable_coordinate_integral_finite (R:realType) m n
    (hmn:(m<=n)%N) (W:set (R_n R n)) (lambda:Lambda n m) (z: \bar R):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y=>(@mapping_multiplicity R
      [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
      (R_n R m) (@coordinate_projection R n m lambda) W y:extended_real_line R))) z ->
  0<=z /\z \is a fin_num.
Proof.
move=>hRect hZ.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
have hH:=@hausdorff_measure_is_measure R X m.
have [M [hMBorel [hHull hMRect]]]:=rectifiable_borel_measure_hull hRect.
have hMMeas:=borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R X m) hMBorel.
have [b [hB hBounds]]:=@rectifiable_coordinate_integrals_exist R m n hmn M hMRect hMMeas.
have hUpper:=@coordinate_integral_subset_upper R m n W M lambda z b
  (measure_hull_subset hHull) hZ hB.
have hNonnegative:=@nonnegative_total_integral_value_ge0 R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
  (@euclidean_lebesgue_measure R m) (@euclidean_lebesgue_is_measure R m) _ _
  (fun y=>@mapping_multiplicity_nonnegative R (Choice.clone X _) (R_n R m)
    (@coordinate_projection R n m lambda) W y) hZ.
split; first exact hNonnegative.
rewrite (ge0_fin_numE hNonnegative); exact:(le_lt_trans hUpper (ltry _)).
Qed.
