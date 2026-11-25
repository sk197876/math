(** Federer (1969), 3.2.40, p. 276: zero lower
    content below the critical exponent and finite lower
    content at the critical exponent, for the actual
    same-factor square of any original power Cantor pair. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric
  EuclideanCantorProduct EuclideanBallVolume PowerCantorPairUP
  PowerCantorSquareSmallRadii RealPower RealPowerContinuity
  PositiveRadiusUnboundedValues MinkowskiContents MinkowskiContentsBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [planar_level_tube_constant_positive]: supporting
    positivity of the finite ball-cover coefficient used for
    Federer 3.2.40, p. 276. This fixed scalar is not a new
    measure normalization or a chosen geometric object. *)
Lemma planar_level_tube_constant_positive (R:realType):
  (0<euclidean_unit_ball_volume R 2*(Num.sqrt 2+1)^+2/2)%R.
Proof.
have hAlpha:=(euclidean_unit_ball_volumeE R 2).2.
have hRoot:(0<=Num.sqrt (2:R))%R:=sqrtr_ge0 _.
have hBase:(0<Num.sqrt (2:R)+1)%R by lra.
have hSquare:(0<(Num.sqrt (2:R)+1)^+2)%R:=exprn_gt0 2 hBase.
have hNumerator:=mulr_gt0 hAlpha hSquare.
by rewrite divr_gt0 // ltr0n.
Qed.

(** Source for [subcritical_cantor_square_lower_content_zero]: the
    zero lower Minkowski content for 0<m<1/2 in Federer
    3.2.40, p. 276. Positive real powers tend to zero at
    small true level widths; the real-radius liminf criterion
    retains every radius, not merely a selected sequence. *)
Theorem subcritical_cantor_square_lower_content_zero (R:realType) (c m:R)
    (n:nat->nat) (A:set (real_line_metric R)) (f:R->R):
  (0<c)%R ->(0<m)%R ->(m<1/2)%R ->is_power_cantor_pair c m n A f ->
  lower_minkowski_content 1 (euclidean_cantor_product A A)=0.
Proof.
move=>hc hm hmHalf hPair.
have hm1:(m<1)%R by lra.
pose C:=(euclidean_unit_ball_volume R 2*(Num.sqrt 2+1)^+2/2)%R.
have hC:(0<C)%R:=planar_level_tube_constant_positive R.
pose p:=(1-2 * m)%R.
have hp:(0<p)%R by rewrite /p; lra.
apply:(@positive_radius_lower_zero_from_small_values R
  (minkowski_tube_quotient 1 (euclidean_cantor_product A A))).
- move=>r hr; exact:minkowski_tube_quotient_nonnegative hr.
- move=>e d he hd.
  have hBase:(0<e/C)%R by rewrite divr_gt0.
  pose cutoff:=real_power (e/C)%R (p^-1)%R.
  have hCutoff:(0<cutoff)%R:=@real_power_strictly_positive R (e/C)%R (p^-1)%R hBase.
  have hPower:real_power cutoff p=(e/C)%R.
    exact:(@real_power_inverse_power R (e/C)%R p (ltW hBase) hp).
  have hSmall:(0<Num.min d cutoff)%R by rewrite lt_min hd hCutoff.
  have [r [/andP[hr hrMin] hTube]]:=@power_cantor_square_arbitrarily_small_level_bound R c m n A f
    (Num.min d cutoff) hc hm hm1 hPair hSmall.
  have hMinD:(Num.min d cutoff<=d)%R by rewrite ge_min lexx.
  have hMinC:(Num.min d cutoff<=cutoff)%R by rewrite ge_min lexx orbT.
  have hrD:(r<d)%R:=lt_le_trans hrMin hMinD.
  have hrCutoff:(r<=cutoff)%R:=ltW (lt_le_trans hrMin hMinC).
  have hPowerBound:=@real_power_monotone R r cutoff p (ltW hr) hrCutoff hp.
  rewrite hPower in hPowerBound.
  have hCancel:(C*(e/C)=e)%R by rewrite mulrC divfK ?gt_eqF.
  exists r; split; first by apply/andP; split.
  apply:le_trans hTube _.
  change (is_true ((C*real_power r p)%R%:E<=e%:E)%E).
  rewrite lee_fin -hCancel.
  exact:(ler_wpM2l (ltW hC) hPowerBound).
Qed.

(** Source for [critical_cantor_square_lower_content_finite_bound]:
    finite upper bound for the critical lower content in Federer
    3.2.40, p. 276. At m=1/2 the exponent 1-2m vanishes
    on every positive level width, giving one finite bound
    at arbitrarily small radii. This is a lower-limit bound. *)
Theorem critical_cantor_square_lower_content_finite_bound (R:realType) (c:R)
    (n:nat->nat) (A:set (real_line_metric R)) (f:R->R):
  (0<c)%R ->is_power_cantor_pair c (1/2:R) n A f ->
  lower_minkowski_content 1 (euclidean_cantor_product A A)<=
    (euclidean_unit_ball_volume R 2*(Num.sqrt 2+1)^+2/2)%R%:E.
Proof.
move=>hc hPair.
have hm:(0<(1/2:R))%R by lra.
have hm1:((1/2:R)<1)%R by lra.
apply:(@positive_radius_lower_bound_from_small_values R
  (minkowski_tube_quotient 1 (euclidean_cantor_product A A))
  (euclidean_unit_ball_volume R 2*(Num.sqrt 2+1)^+2/2)%R)=>e d he hd.
have [r [hr hTube]]:=@power_cantor_square_arbitrarily_small_level_bound R c (1/2:R) n A f d
  hc hm hm1 hPair hd.
have hExponent:(1-2*(1/2:R)=0)%R by field.
rewrite hExponent real_power_zero_exponent mulr1 in hTube.
exists r; split=>//; apply:le_trans hTube _.
rewrite lee_fin lerDl; exact:ltW he.
Qed.
