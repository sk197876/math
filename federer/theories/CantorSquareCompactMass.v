(** Federer (1969), 3.2.40, p. 276: compactness and the
    finite critical Hausdorff length of the actual same-factor
    Cantor square. Minkowski estimates are separate conclusions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  EuclideanRealPlane EuclideanRealPlaneTopology EuclideanCantorProduct
  RealPower MetricCartesianProductUP PowerCantorPairUP PowerCantorSelfProduct
  MetricRealPowerLength HausdorffLengthCompatibility HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_cantor_product_compact]: supporting compactness
    of E in Federer 3.2.40, p. 276. The actual coordinate
    pairing carries the compact Cartesian product onto E.
    This topology lemma permits distinct compact factors. *)
Lemma euclidean_cantor_product_compact (R:realType)
    (A B:set (real_line_metric R)):
  compact A ->compact B ->compact (euclidean_cantor_product A B).
Proof.
move=>hA hB.
pose L:=real_line_metric R.
pose P:=[the topologicalType of (L*L)%type].
pose E:=inner_metric_space (@euclidean_inner_productP R 2).
pose f (p:L*L):=euclidean_real_plane_pair p.1 p.2.
have hImage:f @` (A `*` B)=euclidean_cantor_product A B.
  apply/seteqP; split.
  - move=>z [[a b] [ha hb] <-].
    by rewrite /euclidean_cantor_product /=
      (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
      (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
  - move=>z [ha hb].
    exists (euclidean_real_plane_first z,euclidean_real_plane_second z); first by split.
    exact:(@metric_product_pair_coordinates R [the metricType R of E]
      [the metricType R of L] [the metricType R of L]
      (@euclidean_real_plane_pair R) (@euclidean_real_plane_first R) (@euclidean_real_plane_second R)
      (@euclidean_real_plane_is_metric_product R) z).
rewrite -hImage.
exact:(@continuous_compact P E f (A `*` B)
  (continuous_subspaceT (@euclidean_real_plane_pair_continuous R)) (compact_setX hA hB)).
Qed.

(** Source for [critical_cantor_square_Hausdorff_upper_bound]: supporting
    finite critical length in Federer 3.2.40, p. 276, from the
    same-factor square cover of 2.10.29, p. 193. At m= 1/2
    the target exponent is exactly one with its proved unit
    normalization. No fractional Gamma normalization is used. *)
Lemma critical_cantor_square_Hausdorff_upper_bound (R:realType) (c:R)
    (n:nat->nat) (A:set (real_line_metric R)) (f:R->R):
  (0<c)%R ->is_power_cantor_pair c (1/2:R) n A f ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1
    (euclidean_cantor_product A A)<=(real_power 2 (1/2:R))%:E.
Proof.
move=>hc hPair.
have hm:(0<(1/2:R))%R by lra.
have hm1:((1/2:R)<1)%R by lra.
have hBound:=@power_cantor_self_product_bound R c (1/2:R) 1 n A f hc hm hm1 ler01 hPair.
have hExponent:((2:R)*(1/2)= 1)%R by field.
rewrite hExponent metric_real_power_measure_length_agreement mul1r
  -hausdorff_measure_one_length in hBound.
exact hBound.
Qed.
