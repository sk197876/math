(** Federer (1969), 3.2.20, p. 257: for every
    compact parameter piece the multiplicity of the composite map is
    finite almost everywhere, by the area formula 3.2.3, pp. 243–244. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueCompactInner RadonMeasureUP TopologicalBorel BorelRegularMeasureUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci ExtendedRealOrderTopology MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureFiniteUpperApproximant LipschitzUP HausdorffMeasure MappingMultiplicity
  EuclideanJacobianMeasurable EuclideanJacobianUpperBound EuclideanAreaFormula SubsetIntegralUpperConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_compact_multiplicity_finite]: the explicit
    finite-multiplicity assertion in Federer 3.2.20, p. 257.
    A compact source has finite Lebesgue mass; the actual Jacobian
    is bounded by the Lipschitz constant to the source dimension.
    Zero dimensions and empty compact sets are included. *)
Theorem euclidean_compact_multiplicity_finite (R : realType) m n
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (K : set (R_n R m)) :
  is_metric_lipschitz setT f ->
  @compact (inner_metric_space (@euclidean_inner_productP R m)) K ->
  measure_almost_everywhere (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    [set y|@mapping_multiplicity R _ _ f K y< +oo].
Proof.
move=> hLip hK.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @euclidean_lebesgue_measure R m.
pose nu := @hausdorff_measure R Y m.
have hm := euclidean_lebesgue_is_measure R m.
have hn := @hausdorff_measure_is_measure R Y m.
have hKm : measure_measurable mu K :=
  borel_regular_borel_measurable hm (euclidean_lebesgue_borel_regular R m)
    (closed_borel_set (compact_closed (@metric_hausdorff R X) hK)).
have hKFin : mu K< +oo := radon_compact_finite (@euclidean_lebesgue_radon R m) hK.
have [L [hL hBound]] := hLip.
pose C := (L^+m+1)%R.
have hL0 : (0<=L)%R := ltW hL.
have hLPow : (0<=L^+m)%R := exprn_ge0 m hL0.
have hC : (0<C)%R.
  apply: lt_le_trans ltr01 _; by rewrite /C lerDr.
have hJacBound x j : K x -> partial_function_graph (extended_euclidean_jacobian f) x j -> j<=C%:E.
  move=> hx hj; apply: le_trans (euclidean_jacobian_global_upper_bound hL0 hBound hj) _.
  by rewrite lee_fin /C lerDl.
have [a [hIS hIT]] := euclidean_area_formula hLip hKm.
have haBound := @subset_integral_positive_constant_upper_bound R X mu hm K
  (extended_euclidean_jacobian f) a C hKm hC hJacBound hIS.
have hK0 : 0<=mu K := @measure_nonnegative R X mu hm K.
have hKReal : mu K \is a fin_num by rewrite (ge0_fin_numE hK0).
have hBoundFin : C%:E*mu K< +oo by rewrite -(fineK hKReal) -EFinM ltry.
have haFin : a< +oo := le_lt_trans haBound hBoundFin.
pose N := partial_function_total (fun y=>(@mapping_multiplicity R X Y f K y:extended_real_line R)).
have hUpper : measure_upper_integral nu N< +oo.
  have he := @measure_upper_integral_unique R Y nu N _ a
    (measure_upper_integral_specification nu N) hIT.2.1.
  by rewrite he.
have hAE := finite_upper_integral_below_infinity_almost hn hUpper.
apply: (@measure_almost_everywhere_mono R Y nu hn _ _ _ hAE)=> y [z [hz hFin]].
by change (is_true (@mapping_multiplicity R X Y f K y< +oo)); rewrite (hz : @mapping_multiplicity R X Y f K y=z).
Qed.
