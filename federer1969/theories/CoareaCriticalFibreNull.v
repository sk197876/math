(** Federer (1969), 3.2.11, p. 249: the
    zero critical-source integral gives zero complementary
    fibre mass almost everywhere, by nonnegativity. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  HausdorffMeasure MappingMultiplicity MeasureUP MeasureAlmostUP MeasureAlmostBasic
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci MeasureIntegralUP
  MeasureNonnegativeZero ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_zero_fibre_integral_almost_null]:
    the zero-integral consequence used in the critical
    reduction of Federer 3.2.11, p. 249.
    The source need not have measurable fibres at all points. *)
Lemma coarea_zero_fibre_integral_almost_null (R:realType) m n d
    (f:R_n R m->R_n R n) A:
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) d (mapping_fibre f A y)
        :extended_real_line R))) 0 ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set y|@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) d
      (mapping_fibre f A y)=0].
Proof.
move=>hI.
pose mu:=@euclidean_lebesgue_measure R n.
pose hm:=euclidean_lebesgue_is_measure R n.
pose theta:=fun y=>(@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) d
  (mapping_fibre f A y):extended_real_line R).
have hp:measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_function_total theta)).
  apply:(@measure_almost_everywhere_mono R _ mu hm setT _ _ (measure_almost_everywhere_true hm))=>y _.
  exists (theta y); split; first by [].
  exact (@measure_nonnegative R _ _ (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R m)) d) (mapping_fibre f A y)).
have hAlmost:=nonnegative_integral_zero_almost_equal hm hI hp.
apply:(@measure_almost_everywhere_mono R _ mu hm _ _ _ hAlmost)=>y [t [ht hz]].
change (theta y=0).
change (theta y=t) in ht; change (0=t) in hz.
by rewrite ht -hz.
Qed.
