(** Federer (1969), 3.2.39, p. 276: normalize
    the actual finite tube comparison by its positive normal ball. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  EuclideanBallVolume MinkowskiContents MinkowskiContentsBasic MetricOpenThickening
  FiniteFamilyLayersUP FiniteFamilyLayerTubeMeasureBound MeasureUP MeasureBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_minkowski_layer_tube_sum_bound]: the
    integrated and normalized finite-family comparison in Federer
    3.2.39, p. 276, before taking limits. Every actual
    tube is open and the common normalizer is strictly positive
    at every positive real radius, including zero normal degree.
    All measure and finite distribution laws are discharged. *)
Lemma finite_minkowski_layer_tube_sum_bound (R:realType) n m (I:finType)
    (K:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (S:'I_(#|I|)->set (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  is_finite_family_layers K S ->(0<r)%R ->
  (\sum_j minkowski_tube_quotient m (S j) r)<=\sum_i minkowski_tube_quotient m (K i) r.
Proof.
move=>hS hr.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose hm:=euclidean_lebesgue_is_measure R n.
have hOpen U:open U ->measure_measurable mu U.
  move=>hU; exact:euclidean_borel_measurable (open_borel_set hU).
have hTube:=@finite_family_layer_tube_measure_bound R X I mu K S r hm hOpen hS.
have hPositive:=minkowski_tube_denominator_positive n m hr.
pose c:=((euclidean_unit_ball_volume R (n-m)*r^+(n-m))%R%:E)^-1.
have hc:0<=c.
  rewrite /c inve_ge0 lee_fin; exact:ltW hPositive.
have hScaled:=lee_wpmul2r hc hTube.
have hLeft:(\sum_j mu (metric_open_thickening (S j) r))*c=
    \sum_j mu (metric_open_thickening (S j) r)*c.
  apply:ge0_sume_distrl=>j _; exact:measure_nonnegative hm _.
have hRight:(\sum_i mu (metric_open_thickening (K i) r))*c=
    \sum_i mu (metric_open_thickening (K i) r)*c.
  apply:ge0_sume_distrl=>i _; exact:measure_nonnegative hm _.
rewrite /minkowski_tube_quotient.
by rewrite -hLeft -hRight.
Qed.
