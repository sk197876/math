(** Federer (1969), 3.4.4, p. 318: positive
    Gamma-normalized real-dimensional mass of the original product image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  PowerCantorPairUP CriticalSharpProductUP CriticalSharpProductProbability BallGrowthProbabilityUP
  BallGrowthHausdorffLower RealHausdorffNormalisation RealHausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [critical_sharp_product_positive_hausdorff]: the
    strict inequality H^[nu+(m-nu)beta](f(B))>0 in
    3.4.4, p. 318, on its actual original
    coordinate product. Proved finite product probabilities and
    the actual diameter-power comparison give a positive lower
    bound with Federer's Gamma coefficient. No real-dimensional
    product inequality or normalization value is assumed. *)
Theorem critical_sharp_product_positive_hausdorff (R:realType) m nu (beta:R) n
    (A:set (real_line_metric R)) (f:R->R)
    (hDegree:(0<=(nu%:R+(m-nu)%:R*beta:R))%R):
  (nu<=m)%N ->(0<beta)%R ->(beta<1)%R ->is_power_cantor_pair 1 beta n A f ->
  (0<@real_hausdorff_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
    (nu%:R+(m-nu)%:R*beta)%R hDegree (@critical_sharp_product_source R m nu A))%E.
Proof.
move=>hNu hBeta hBetaUpper hPair.
have hDimension:(nu+(m-nu))%N=m by rewrite subnKC.
have hExists:=@critical_sharp_product_probability_exists R nu (m-nu)%N beta n A f hBeta hBetaUpper hPair.
rewrite hDimension in hExists.
have [K [mu hMu]]:=hExists.
pose b:=real_hausdorff_normalisation hDegree.
have hb:(0<b)%R:=real_hausdorff_normalisation_positive hDegree.
have hK:=ball_growth_coefficient_positive hMu.
have hPositive:(0<(b/K)%R%:E)%E by rewrite lte_fin;exact:divr_gt0 hb hK.
have hLower:=@ball_growth_probability_power_measure_lower R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
  (@critical_sharp_product_source R m nu A) K (nu%:R+(m-nu)%:R*beta)%R b mu hMu hb.
exact:lt_le_trans hPositive hLower.
Qed.
