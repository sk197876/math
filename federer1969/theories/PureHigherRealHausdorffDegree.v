(** Federer (1969), 3.3.20, p. 306:
    pure one-dimensional unrectifiability for all higher
    real Hausdorff measures, including the degree-one endpoint. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric RectifiableSetUP
  RectifiableFiniteHausdorffMass PureUnrectifiableLaws RealHausdorffMeasure
  RealHausdorffNormalisation RealPowerDimensionDrop MetricRealPowerLength MetricRealPowerMeasure
  HausdorffMeasure HausdorffLengthCompatibility.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [pure_higher_real_hausdorff_degree]: the
    implication from pure (H1,1) to pure (H^(2m),1)
    in 3.3.20, p. 306, with 2m>=1.
    Above degree one every actual bounded rectifiable
    image has finite H1 mass and hence zero higher
    real-degree Hausdorff mass by actual 2.10.2.
    At the endpoint actual natural-degree compatibility
    retains the original pure hypothesis exactly. *)
Theorem pure_higher_real_hausdorff_degree (R:realType) n
    (p:R) (hp:(0<=p)%R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  (1<=p)%R ->is_purely_measure_m_unrectifiable
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) 1) 1 E ->
  is_purely_measure_m_unrectifiable
    (@real_hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) p hp) 1 E.
Proof.
move=>hDegree hPure.
apply/pure_unrectifiable_iff_rectifiable_subsets_null;split;first exact:real_hausdorff_measure_is_measure.
move=>F hFE hRect.
case:(eqVneq p (1:R)%R)=>hEqual.
- subst p.
  rewrite (@real_hausdorff_measure_natural R _ 1 hp F).
  have hNull:=(@pure_unrectifiable_iff_rectifiable_subsets_null R
    (inner_metric_space (@euclidean_inner_productP R n))
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) 1) 1 E).1 hPure.
  exact:(hNull.2 F hFE hRect).
- have hStrict:(1<p)%R by rewrite lt_neqAle eq_sym hEqual hDegree.
  have hFinite:=@rectifiable_finite_hausdorff_mass R 1 n F hRect.
  have hOne:(@metric_real_power_measure R (inner_metric_space (@euclidean_inner_productP R n)) 1 1 F< +oo).
    by rewrite metric_real_power_measure_length_agreement -hausdorff_measure_one_length.
  exact:(@metric_real_power_finite_higher_degree_zero R
    (inner_metric_space (@euclidean_inner_productP R n)) 1 (real_hausdorff_normalisation hp)
    1 p ltr01 (real_hausdorff_normalisation_positive hp) ler01 hStrict F hOne).
Qed.
