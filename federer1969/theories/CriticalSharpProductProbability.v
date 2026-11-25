(** Federer (1969), 3.4.4, p. 318: actual
    finite product probability on the original positive image set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanLebesgueHaar EuclideanBallVolume RealMetricBackground RealLineSeparability SeparableMetricBaseSealed
  EuclideanScalarLastProduct CriticalSharpProductUP CriticalSharpProductSourceBlocks
  PowerCantorPairUP BallGrowthProbabilityUP BallGrowthProduct UnitCubeBallProbability CantorBallProbability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [critical_sharp_product_probability_exists]: the
    positive image measure asserted in 3.4.4, p. 318,
    before its Hausdorff comparison. Start with actual unit-cube
    restricted Lebesgue probability on R^nu and adjoin the
    original Cantor factor through the actual Euclidean/scalar
    product laws. Closed measurability, unit source mass, and
    real-degree growth are proved at every finite stage. *)
Theorem critical_sharp_product_probability_exists (R:realType) nu l (beta:R) n
    (A:set (real_line_metric R)) (f:R->R):
  (0<beta)%R ->(beta<1)%R ->is_power_cantor_pair 1 beta n A f ->
  exists K:R,exists mu:set (inner_metric_space (@euclidean_inner_productP R (nu+l)))->\bar R,
    @is_ball_growth_probability R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R (nu+l))]
      (@critical_sharp_product_source R (nu+l) nu A)
      K (nu%:R+l%:R*beta)%R mu.
Proof.
move=>hBeta hBetaUpper hPair.
have [D [hCount hDense]]:=@real_line_countable_dense R.
pose V:=@SeparableMetricBase.value R [the metricType R of real_line_metric R] D hCount hDense.
have hV:=@SeparableMetricBase.laws R [the metricType R of real_line_metric R] D hCount hDense.
have [eta hEta]:=@original_cantor_ball_probability_exists R beta n A f hBeta hBetaUpper hPair.
elim:l=>[|l [K [mu hMu]]].
- have [mu hMu]:=@unit_cube_ball_probability_exists R nu.
  rewrite addn0 mul0r addr0 critical_sharp_source_empty_last_block.
  exists (euclidean_unit_ball_volume R nu),mu;exact:hMu.
- have [U hU]:=@euclidean_countable_open_base R (nu+l).
  have [rho hRho]:=@ball_growth_probability_product R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R ((nu+l)+1))]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R (nu+l))]
    [the metricType R of real_line_metric R]
    (@euclidean_scalar_last_pair R (nu+l)) (@euclidean_scalar_last_first R (nu+l))
    (@euclidean_scalar_last_second R (nu+l)) (@euclidean_scalar_last_metric_product R (nu+l))
    (@critical_sharp_product_source R (nu+l) nu A) A K (RealPower.real_power 2 beta)
    (nu%:R+l%:R*beta)%R beta mu eta U V hU hV
    (@euclidean_scalar_last_pair_continuous R (nu+l))
    (@euclidean_scalar_last_first_continuous R (nu+l))
    (@euclidean_scalar_last_second_continuous R (nu+l)) hBeta hMu hEta.
  have hSource:=@critical_sharp_source_scalar_product R (nu+l) nu A (leq_addr l nu).
  have hDegree:(nu%:R+l%:R*beta+beta=nu%:R+l.+1%:R*beta)%R by rewrite -addn1 natrD;ring.
  rewrite -hSource hDegree in hRho.
  rewrite addnS -addn1.
  exists (K*RealPower.real_power 2 beta)%R,rho.
  exact:hRho.
Qed.
