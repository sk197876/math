(** Federer (1969), 3.2.40, p. 276, first paragraph:
    the complete original same-factor Cantor-square example.
    The separate compact triangular graph remains a different
    assertion of the numbered item. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric
  EuclideanCantorProduct EuclideanBallVolume HausdorffMeasure MinkowskiContents
  PowerCantorPairUP PowerCantorPair PowerCantorCarrierCoefficient
  RapidPowerCantorScalesUP RapidPowerCantorScales RapidPowerCantorScalesLaws
  RapidCantorSquareUpperContent PowerCantorSquareLowerContent
  SubcriticalCantorSquareHausdorffNull CantorSquareCompactMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_2_40_cantor_square]: all conclusions
    of the first paragraph of Federer 3.2.40, p. 276.
    For every 0<m<=1/2 and positive gauge coefficient there
    is an actual original pair A(m,n), f with n_j tending
    to infinity, whose same-factor square is compact and
    has infinite upper content. Its lower content is zero
    below the critical exponent, and positive finite at
    the critical exponent; its Hausdorff length is zero
    below that exponent. A quantitative rapid schedule is
    proved to exist. No assertion is made that every
    merely diverging schedule suffices. Auxiliary choices
    remain existential; no global example is selected. *)
Theorem federer_3_2_40_cantor_square (R:realType) (c m:R):
  (0<c)%R ->(0<m)%R ->(m<=1/2)%R ->
  exists (n:nat->nat) (s:nat->R) (A:set (real_line_metric R)) (f:R->R),
    is_rapid_power_cantor_scales c m n s /\is_power_cantor_pair c m n A f /\
    (forall N:nat,exists J:nat,forall j,(J<=j)%N ->(N<=n j)%N) /\
    compact (euclidean_cantor_product A A) /\
    upper_minkowski_content 1 (euclidean_cantor_product A A)=+oo /\
    ((m<1/2)%R ->lower_minkowski_content 1 (euclidean_cantor_product A A)=0 /\
      @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1
        (euclidean_cantor_product A A)=0) /\
    (m=(1/2)%R ->(0<lower_minkowski_content 1 (euclidean_cantor_product A A) < +oo)%E).
Proof.
move=>hc hm hmHalf.
have hm1:(m<1)%R by lra.
have [n [s hScales]]:=@rapid_power_cantor_scales_exist R c m hc hm hm1.
have hCounts j:(2<=n j)%N.
  have hj2:(2<=j.+2)%N by [].
  exact:leq_trans hj2 (rapid_power_cantor_count hScales j).
have [A [f hPair]]:=@power_cantor_pair_exists R c m n hc hm hm1 hCounts.
have hA:compact A:=(@power_cantor_pair_properties R c m n A f hc hm hm1 hPair).1.
have hCompact:=euclidean_cantor_product_compact hA hA.
have hUpper:=@rapid_cantor_square_upper_content_infinite R c m n s A f hc hm hmHalf hScales hPair.
exists n,s,A,f; split; first exact hScales.
split; first exact hPair.
split; first exact:rapid_power_cantor_subdivisions_diverge hScales.
split; first exact hCompact.
split; first exact hUpper.
split.
- move=>hStrict; split.
  + exact:subcritical_cantor_square_lower_content_zero hc hm hStrict hPair.
  + exact:subcritical_cantor_square_Hausdorff_null hc hm hStrict hPair.
- move=>hCritical.
  have hPairCritical:is_power_cantor_pair c (1/2:R) n A f by rewrite -hCritical.
  have hLower:=@critical_original_cantor_square_lower_content_positive R c n A f hc hPairCritical.
  have hFinite:=@critical_cantor_square_lower_content_finite_bound R c n A f hc hPairCritical.
  have hConstant:(0<euclidean_unit_ball_volume R 2/8)%R.
    have hAlpha:=(euclidean_unit_ball_volumeE R 2).2.
    by rewrite divr_gt0 // ltr0n.
  have hPositive:0<lower_minkowski_content 1 (euclidean_cantor_product A A).
    apply:lt_le_trans _ hLower; by rewrite lte_fin.
  apply/andP; split; first exact hPositive.
  exact:le_lt_trans hFinite (ltry _).
Qed.
