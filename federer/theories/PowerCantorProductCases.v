(** Federer (1969), 2.10.29, p. 194: the two cases t_j>=d>=tau_j and
    tau_j>=d>=t_(j+1). Combine the actual factor interval masses with the
    product rectangle law and the scalar root comparison. The auxiliary
    normalising coefficient is c>0; the bound before Federer's division by
    6*c^2 is retained explicitly. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground RealPower RealPowerSuccessor CompactIntervalGauge MetricDiameter
  MetricCartesianProductUP MetricCartesianRectangleBounds MeasureUP MetricRealPowerMeasure
  PowerCantorPairUP PowerCantorIntervalBounds PowerCantorProductMeasure PowerCantorProductScalar
  InterleavedCantorScalesUP InterleavedCantorScalesLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [power_cantor_factor_product_bound]: supporting
    multiplication of one ordinary power bound and
    one factor-six linear bound in 2.10.29,
    p. 194. The exponent k may be zero. *)
Lemma power_cantor_factor_product_bound (R : realType) (c m k d r : R) j (u v : \bar R) :
  (0<c)%R -> (0<m)%R -> (0<d)%R -> (d<=1)%R -> (0<r)%R ->
  (d<=r^+j.+1)%R -> (k+(j.+1%:R)^-1<=m+1)%R ->
  0<=v -> u<=(c*real_power d m)%R%:E ->
  v<=(6*(c*real_power r m)*d/r)%R%:E ->
  u*v<=(6*c*c*real_power d k*real_power r m)%R%:E.
Proof.
move=> hc hm hd hd1 hr hsmall hexp hv hu hvl.
have hcp : (0<=c*real_power d m)%R := mulr_ge0 (ltW hc) (real_power_nonnegative d m).
have hcpE : 0<=(c*real_power d m)%R%:E by rewrite lee_fin.
have hh := le_trans (lee_wpmul2r hv hu) (lee_wpmul2l hcpE hvl).
rewrite -EFinM in hh.
have heq : ((c*real_power d m)*(6*(c*real_power r m)*d/r))%R=
    (6*c*c*(real_power d (m+1)*real_power r m/r))%R.
  rewrite real_power_positive_successor ?ltW //; ring.
have hK : (0<=6*c*c)%R by apply: mulr_ge0 (ltW hc); apply: mulr_ge0 (ltW hc); exact: ler0n.
have hs := @power_cantor_product_scale_bound R d r m k j hd hd1 hr hsmall hexp.
have hb := ler_wpM2l hK hs.
rewrite !mulrA in hb.
apply: le_trans hh _; rewrite heq lee_fin !mulrA.
exact hb.
Qed.

(** Source for [interleaved_power_cantor_product_band_bound]: direct
    two-case local bound in 2.10.29, p. 194.
    The width r is sigma_(j-1) in the first
    case and s_j in the second, with book
    spacing index j represented here by j-1.
    No measurability premise is imposed on S. *)
Theorem interleaved_power_cantor_product_band_bound (R : realType) (P : metricType R)
    (pair : real_line_metric R -> real_line_metric R -> P)
    (first second : P -> real_line_metric R)
    (hp : is_metric_cartesian_product pair first second)
    (c m k : R) (hc : (0<=c)%R) D A B f g :
  (0<c)%R -> (0<m)%R -> (m<1)%R ->
  is_interleaved_cantor_scales (fun t=>(c*real_power t m)%R) D ->
  is_power_cantor_pair c m (cantor_left_subdivision D) A f ->
  is_power_cantor_pair c m (cantor_right_subdivision D) B g ->
  forall j (S : set P) (d : R), S !=set0 ->
    (0<d)%R -> (d<=1)%R -> extended_metric_diameter S<=d%:E ->
    (d<=cantor_left_spacing D j)%R -> (cantor_left_spacing D j.+1<=d)%R ->
    (k+(j.+1%:R)^-1<=m+1)%R ->
    exists r : R, (r=cantor_right_width D j \/ r=cantor_left_width D j.+1) /\
      @power_cantor_product_measure R P pair c m hc A B S<=
        (6*c*c*real_power d k*real_power r m)%R%:E.
Proof.
move=> hcp hm hm1 hD hA hB j S d hS hd hd1 hdiam htop hbottom hexp.
have [U [V [hU [hV hcover]]]] := @metric_cartesian_real_rectangle_hull R P pair first second hp S d hS (ltW hd) hdiam.
have hrect := @power_cantor_product_rectangle_bound R P pair first second hp c m hc A B S U V hcover.
have hu := @power_cantor_pair_interval_bound R c m _ A f hcp hm hm1 hA U.
have hv := @power_cantor_pair_interval_bound R c m _ B g hcp hm hm1 hB V.
rewrite hU in hu; rewrite hV in hv.
have hmR := @metric_real_power_measure_is_measure R [the metricType R of real_line_metric R] c m hc.
have [hlt [hls [hrt [hrs hnext]]]] := interleaved_cantor_scales_interleaving hD j.
have [hlpos hrpos] := interleaved_cantor_widths_positive hD j.
have [hlnpos hrnpos] := interleaved_cantor_widths_positive hD j.+1.
case: (leP (cantor_right_spacing D j) d)=> hcase.
- have hlow : (cantor_right_spacing D j<=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val V)))%R by rewrite hV.
  have hhigh : (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val V))<=cantor_right_width D j)%R.
    rewrite hV; exact: le_trans htop hlt.
  have hlinear := @interleaved_power_cantor_right_linear_bound R c m D B g hcp hm hm1 hD hB j V hlow hhigh.
  rewrite hV in hlinear.
  have hpow := le_trans htop (interleaved_cantor_left_small_spacing hD j).
  exists (cantor_right_width D j); split; first by left.
  exact (le_trans hrect (@power_cantor_factor_product_bound R c m k d _ j _ _
    hcp hm hd hd1 hrpos hpow hexp (measure_nonnegative hmR _) hu hlinear)).
- have hlow : (cantor_left_spacing D j.+1<=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val U)))%R by rewrite hU.
  have hhigh : (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val U))<=cantor_left_width D j.+1)%R.
    rewrite hU; exact: le_trans (ltW hcase) hrt.
  have hlinear := @interleaved_power_cantor_left_linear_bound R c m D A f hcp hm hm1 hD hA j.+1 U hlow hhigh.
  rewrite hU in hlinear.
  have hpow := le_trans (ltW hcase) (interleaved_cantor_right_small_spacing hD j).
  exists (cantor_left_width D j.+1); split; first by right.
  apply: le_trans hrect _; rewrite muleC.
  exact (@power_cantor_factor_product_bound R c m k d _ j _ _
    hcp hm hd hd1 hlnpos hpow hexp (measure_nonnegative hmR _) hv hlinear).
Qed.
