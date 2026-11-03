(** Federer (1969), 3.2.40, p. 276: the
    actual same-factor Cantor square has infinite upper
    Minkowski content for a proved rapid schedule. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge RealPower
  EuclideanInnerProduct InnerMetric EuclideanCantorProduct EuclideanBallVolume
  RapidPowerCantorScalesUP PowerCantorPairUP RapidCantorSquareStepLower
  RapidCantorGapRadii CantorSplitRadius MinkowskiContents PositiveRadiusUnboundedValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rapid_cantor_square_upper_content_infinite]: the
    infinite upper content in the first example of Federer
    3.2.40, p. 276. True finite source-point packings have
    quotients growing at least linearly in the stage number;
    their actual gap radii tend to zero. This proves the
    full real-radius limsup is infinite. It asserts no
    corresponding divergence of the lower content. *)
Theorem rapid_cantor_square_upper_content_infinite (R:realType) (c m:R)
    (n:nat->nat) (s:nat->R) (A:set (real_line_metric R)) (f:R->R):
  (0<c)%R ->(0<m)%R ->(m<=1/2)%R ->
  is_rapid_power_cantor_scales c m n s ->is_power_cantor_pair c m n A f ->
  upper_minkowski_content 1 (euclidean_cantor_product A A)=+oo.
Proof.
move=>hc hm hmHalf hScales [J [H [hJ [hTree [hA hCumulative]]]]].
pose C:=(euclidean_unit_ball_volume R 2/8)%R.
have hC:(0<C)%R.
  have hAlpha:=(euclidean_unit_ball_volumeE R 2).2.
  by rewrite /C divr_gt0 // ltr0n.
apply:(@positive_radius_upper_infinite_from_spikes R
  (minkowski_tube_quotient 1 (euclidean_cantor_product A A)))=>b d hd.
have [N hSmall]:=@rapid_cantor_gap_radii_eventually_small R c m n s J H d
  hc hm hmHalf hScales hJ hTree hd.
pose B:=Num.bound (`|b|/C)%R.
have hRatio:(0<=`|b|/C)%R by apply:divr_ge0; [exact:normr_ge0|exact:ltW hC].
have hInteger:(`|b|/C<B%:R)%R:=archi_boundP hRatio.
have hLarge:(`|b|<C*B%:R)%R.
  by move:hInteger; rewrite ltr_pdivrMr // mulrC.
pose j:=maxn N B.
have hNj:(N<=j)%N:=leq_maxl N B.
have hBj:(B<=j.+1)%N:=leq_trans (leq_maxr N B) (leqnSn j).
have hCast:((B%:R:R)<=j.+1%:R)%R by rewrite ler_nat.
have hUpper:=ler_wpM2l (ltW hC) hCast.
have hThreshold:(b<=C*j.+1%:R)%R.
  exact:le_trans (ler_norm b) (le_trans (ltW hLarge) hUpper).
pose r:=((cantor_split_spacing (s j) (n j) (s j.+1)-s j.+1)/4)%R.
exists r; split; first exact:hSmall j hNj.
have hBound:=@rapid_cantor_square_step_tube_lower_bound R c m n s J H A
  hc hm hmHalf hScales hJ hTree hA j.
apply:le_trans _ hBound; by rewrite lee_fin.
Qed.
