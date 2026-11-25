(** Federer (1969), 3.2.40, p. 276: identify the
    original Cantor carrier for every positive power-gauge
    coefficient. Auxiliary cumulative functions may change,
    but all original interval levels and the set stay fixed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PowerCantorPairUP
  PowerCantorCoefficientInvariance PowerConcaveIntervalGauge ConcaveCantorFunction
  CriticalCantorSquareLowerContent EuclideanCantorProduct MinkowskiContents EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [power_cantor_carrier_coefficient_change]: supporting
    use of a unit product measure for the original A(m,n)
    in Federer 3.2.40, p. 276. Positive gauge scaling
    leaves the actual tree and limit set unchanged. Prove
    existence of the new cumulative function through the
    earlier opaque laws; its value is not asserted equal
    to the original function. No fractional normalization
    identity is needed to identify the geometric carrier. *)
Theorem power_cantor_carrier_coefficient_change (R:realType) (c d m:R)
    (n:nat->nat) (A:set (real_line_metric R)) (f:R->R):
  0<c ->0<d ->0<m ->m<1 ->is_power_cantor_pair c m n A f ->
  exists g,is_power_cantor_pair d m n A g.
Proof.
move=>hc hd hm hm1 [J [H [hJ [hTree [hA hCumulative]]]]].
have hNew:=@power_cantor_tree_coefficient_change R c d m J n H hc hd hTree.
have hg:=power_concave_interval_gauge hd hm hm1.
have [g hG]:=@concave_cantor_cumulative_exists R _ hg J n H A hNew hA.
exists g; exists J,H; split=>//; split=>//; by split.
Qed.

(** Source for [critical_original_cantor_square_lower_content_positive]:
    the critical positive lower content in Federer 3.2.40,
    p. 276, for every original positive gauge coefficient.
    Preserve the actual carrier by the preceding proved
    coefficient change, then use the unit product measure.
    The bound is geometric and independent of normalization. *)
Lemma critical_original_cantor_square_lower_content_positive (R:realType) (c:R)
    (n:nat->nat) (A:set (real_line_metric R)) (f:R->R):
  0<c ->is_power_cantor_pair c (1/2:R) n A f ->
  ((euclidean_unit_ball_volume R 2/8)%:E<=
    lower_minkowski_content 1 (euclidean_cantor_product A A))%E.
Proof.
move=>hc hPair.
have hm:(0<(1/2:R)) by rewrite divr_gt0 // ltr0n.
have hm1:((1/2:R)<1) by rewrite ltr_pdivrMr ?ltr0n // mul1r ltr1n.
have [g hUnit]:=@power_cantor_carrier_coefficient_change R c 1 (1/2:R) n A f
  hc ltr01 hm hm1 hPair.
exact:critical_cantor_square_lower_content_positive hUnit.
Qed.
