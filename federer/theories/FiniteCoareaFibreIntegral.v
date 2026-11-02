(** Federer (1969), 3.2.11, p. 249: for finite
    measurable source mass, the fibre-mass integral is finite
    by 2.10.25 and measurable by 2.10.26. This supporting
    fact is established before the critical coarea identity. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanHausdorffLebesgue HausdorffMeasure HausdorffFibreCost HausdorffFibreCutoffs
  HausdorffFibreIntegralBound CoareaNullFibres FiniteCoareaFibreMeasurability
  MappingMultiplicity LipschitzUP PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureNonnegativeIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_coarea_fibre_integral]: the finite
    integral of the original fibre mass used in the critical
    perturbation of Federer 3.2.11, p. 249.
    This is only an upper-bound consequence of Chapter 2,
    without using or assuming the coarea theorem. *)
Theorem finite_coarea_fibre_integral (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  (n<=m)%N ->is_metric_lipschitz setT f ->
  measure_measurable (@euclidean_lebesgue_measure R m) A ->euclidean_lebesgue_measure m A< +oo ->
  exists a:R,(0<=a)%R /\is_measure_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun y=>(@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre f A y)
        :extended_real_line R))) a%:E.
Proof.
move=>hnm hf hA hFin.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose hm:=euclidean_lebesgue_is_measure R n.
pose theta:=fun y:Y=>(@hausdorff_measure R X (m-n) (mapping_fibre f A y):extended_real_line R).
have ht:forall y,0<=theta y.
  move=>y; exact (@measure_nonnegative R [the choiceType of X] (@hausdorff_measure R X (m-n))
    (@hausdorff_measure_is_measure R X (m-n)) (mapping_fibre f A y)).
have hp:measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_function_total theta)).
  apply:(measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=>y _.
  exists (theta y); by split.
have hMeas:=(finite_coarea_fibre_measurability hnm hf hA hFin).1.
have [hi hNonnegative]:=nonnegative_measurable_function_integral hm hMeas hp.
have [L [hL hBound]]:=hf.
have hCond:hausdorff_fibre_integral_condition f A (m-n) n.
  right; exact (@coarea_euclidean_source_proper R n).
have hUpper:=@hausdorff_lipschitz_fibre_integral_bound R X Y f L (m-n) n A hBound hCond.
have hSource:@hausdorff_measure R X ((m-n)+n) A=euclidean_lebesgue_measure m A.
  have hDegree:=congr1 (fun d:nat=>@hausdorff_measure R X d A) (subnK hnm).
  by rewrite hDegree (euclidean_hausdorff_spherical_lebesgue A).1.
have hTarget:(@hausdorff_measure R Y n)=mu.
  apply:funext=>S; exact (euclidean_hausdorff_spherical_lebesgue S).1.
rewrite hSource hTarget in hUpper.
have hIntegral:=@measure_upper_integral_unique R Y mu _ _ _
  (measure_upper_integral_specification mu _) hi.2.1.
rewrite hIntegral in hUpper.
have hM:euclidean_lebesgue_measure m A \is a fin_num.
  rewrite ge0_fin_numE //; exact (@measure_nonnegative R [the choiceType of X] (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m) A).
have hFinite:measure_lower_integral mu (partial_function_total theta)< +oo.
  apply:le_lt_trans hUpper _.
  by rewrite -(fineK hM) -EFinM ltry.
case hValue:(measure_lower_integral mu (partial_function_total theta))=>[a| |] in hi hNonnegative hFinite.
- exists a; split=> //; by move:hNonnegative; rewrite lee_fin.
- by rewrite ltxx in hFinite.
- by [].
Qed.
