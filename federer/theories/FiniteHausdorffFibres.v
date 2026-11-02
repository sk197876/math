(** Federer (1969), 3.2.22(2), p. 258: finite
    complementary fibre mass follows already from the general
    upper-integral estimate 2.10.25, pp. 188–189.
    This avoids assuming the sharp rectifiable coarea equality. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  LipschitzUP LipschitzConstant HausdorffMeasure HausdorffFibreCost HausdorffFibreCutoffs
  HausdorffFibreTheorem CoareaNullFibres MappingMultiplicity MeasureUP MeasureIntegralBounds
  MeasureAlmostUP MeasureAlmostBasic MeasureFiniteUpperApproximant PartialExtendedOrderLoci
  PartialFunctionUP PartialFunctionBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_hausdorff_fibres_almost]: supporting
    finiteness in Federer 3.2.22(2), p. 258.
    For m>=mu, finite H^m source mass and a
    Lipschitz Euclidean map give H^(m-mu)-finite fibres
    for H^mu almost every target point. The Euclidean
    target is proper, discharging the alternative premise
    of 2.10.25. Source measurability, target rectifiability,
    and the sharp coarea formula are not needed. *)
Theorem finite_hausdorff_fibres_almost (R:realType) n k m mu
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R k)) A:
  (mu<=m)%N ->is_metric_lipschitz setT F ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m A< +oo ->
  measure_almost_everywhere (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R k)) mu)
    [set z|@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n))
      (m-mu) (mapping_fibre F A z)< +oo].
Proof.
move=>hDim hF hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R k).
pose beta:=@hausdorff_measure R Y mu.
have hb:=@hausdorff_measure_is_measure R Y mu.
have hCondition:hausdorff_fibre_integral_condition F A (m-mu) mu.
  right; exact:(@coarea_euclidean_source_proper R k).
have hBound:=@federer_2_10_25 R X Y F hF (m-mu) mu A hCondition.
rewrite (subnK hDim) in hBound.
have hMassNum:@hausdorff_measure R X m A \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative (@hausdorff_measure_is_measure R X m) A)) hFinite.
have hUpper:measure_upper_integral beta
    (partial_function_total (hausdorff_fibre_mass F A (m-mu)))< +oo.
  apply:(le_lt_trans hBound _).
  by rewrite -(fineK hMassNum) -EFinM ltry.
have hAE:=@finite_upper_integral_below_infinity_almost R [the choiceType of Y]
  beta hb (partial_function_total (hausdorff_fibre_mass F A (m-mu))) hUpper.
apply:(measure_almost_everywhere_mono hb _ hAE)=>z [r [hr hR]].
change (hausdorff_fibre_mass F A (m-mu) z=r) in hr.
change (is_true (hausdorff_fibre_mass F A (m-mu) z< +oo)).
by rewrite hr.
Qed.
