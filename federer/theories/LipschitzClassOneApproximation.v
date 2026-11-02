(** Federer (1969), 3.2.29, p. 268:
    approximate a global Lipschitz map by a global
    class-one map with arbitrarily small disagreement,
    using the actual 3.1.16 theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  LipschitzUP LipschitzFiniteApproximateGrowth EuclideanLebesgueDimensions ApproximateMetricGrowth
  MeasureUP MeasureBasic MeasureAlmostUP MeasureApproximateOrderLimits CenteredBallRelations
  ContinuousMultilinearUP ContinuousMultilinearSealed NormRegularity NormClassHigherUP
  ApproximateGrowthClassOneApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_class_one_small_disagreement]:
    the first displayed approximation in Federer
    3.2.29, p. 268. The class-one approximant
    is defined globally and its disagreement with F
    has Lebesgue measure below every prescribed positive
    tolerance. No approximation or derivative is assumed. *)
Theorem lipschitz_class_one_small_disagreement (R:realType) m n
    (F:inner_metric_space (@euclidean_inner_productP R m.+1)->
      inner_metric_space (@euclidean_inner_productP R n)) L e:
  is_metric_lipschitz_bound setT F L ->0<e ->
  exists f:R_n R m.+1->R_n R n,
    norm_class (inner_norm_real_norm (@euclidean_inner_productP R m.+1))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f 1 /\
    (@euclidean_lebesgue_measure R m.+1 (~` [set x|F x=f x])<e%:E)%E.
Proof.
move=>hLip he.
pose X:=R_n R m.+1.
pose Y:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R m.+1).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m.+1).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose Z j:=@ContinuousMultilinear.space R j X Y NX NY hNX hNY.
pose ev j:=@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY.
pose ZN j:=@ContinuousMultilinear.norm R j X Y NX NY hNX hNY.
have hZ j:is_continuous_multilinear_space NX NY (ev j) (ZN j):=
  @ContinuousMultilinear.laws R j X Y NX NY hNX hNY.
pose P:= [set a| (measure_approximate_upper_limit (@euclidean_lebesgue_measure R m.+1)
  (@centered_closed_ball_relation R [the metricType R of inner_metric_space (@euclidean_inner_productP R m.+1)])
  (partial_metric_growth_quotient setT F a) a < +oo)%E].
have hAll a:P a:=@lipschitz_finite_approximate_growth R m n F L a hLip.
have hGrowth:measure_almost_everywhere_on (@euclidean_lebesgue_measure R m.+1) setT P.
  have hEmpty:setT `\` P=set0.
    apply/seteqP; split=>[a [_ hn]|a []]; exfalso; exact:hn (hAll a).
  rewrite /measure_almost_everywhere_on hEmpty; exact:measure_empty (euclidean_lebesgue_is_measure R m.+1).
have [f [hf hError]]:=@federer_3_1_16 R m.+1 n Z ev ZN hZ setT F hGrowth e he.
exists f; split; first exact hf.
by rewrite setTD in hError.
Qed.
