(** Federer (1969), 2.10.29, p. 194: the product measure has arbitrarily
    small k-dimensional local covering density for k<m+1. Use the proved
    two-case estimate, shrinking width powers and the index-dependent
    exponent error. The real power-gauge coefficient b>0 is arbitrary, so no
    Euler-Gamma formula is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground RealPower MetricDiameterUP MetricDiameter MetricRealPowerCost
  MeasureUP MeasureBasic MetricCartesianProductUP PowerCantorPairUP PowerCantorProductMeasure PowerCantorProductCases
  InterleavedCantorScalesUP InterleavedCantorScalesLaws InterleavedCantorCutoffs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [interleaved_power_cantor_product_small_density]: direct
    arbitrarily small local product bound in
    2.10.29, p. 194, expanded to include
    diameter zero and k=0. The positive
    coefficient b of the target covering measure
    is independent of the factor coefficient c. *)
Theorem interleaved_power_cantor_product_small_density (R : realType) (P : metricType R)
    (pair : real_line_metric R -> real_line_metric R -> P)
    (first second : P -> real_line_metric R)
    (hp : is_metric_cartesian_product pair first second)
    (c m k b : R) (hc : (0<=c)%R) D A B f g :
  (0<c)%R -> (0<m)%R -> (m<1)%R -> (0<=k)%R -> (k<m+1)%R -> (0<b)%R ->
  is_interleaved_cantor_scales (fun t=>(c*real_power t m)%R) D ->
  is_power_cantor_pair c m (cantor_left_subdivision D) A f ->
  is_power_cantor_pair c m (cantor_right_subdivision D) B g ->
  forall e : R, (0<e)%R -> exists delta : R, (0<delta)%R /\
    forall S : set P, extended_metric_diameter S<=delta%:E ->
      @power_cantor_product_measure R P pair c m hc A B S<=e%:E*metric_real_diameter_cost b k S.
Proof.
move=> hcp hm hm1 hk hgap hb hD hA hB e he.
pose K := (6*c*c)%R.
have hK : (0<K)%R by rewrite /K !mulr_gt0 ?ltr0n.
pose eta := (e*b/K)%R.
have heta : (0<eta)%R by rewrite /eta divr_gt0 // mulr_gt0.
have [Nw hw] := @interleaved_cantor_width_powers_small R _ D hD m eta hm heta.
have [Ne heindex] := @reciprocal_index_exponent_error_small R m k hgap.
pose N := maxn Nw Ne.
have hNw : (Nw<=N)%N := leq_maxl _ _.
have hNe : (Ne<=N)%N := leq_maxr _ _.
have hspacing : (0<cantor_left_spacing D N)%R.
  have [_ [hls _]] := interleaved_cantor_scales_interleaving hD N.
  exact (lt_le_trans (interleaved_cantor_widths_positive hD N.+1).1 hls).
pose delta := Order.min 1%R (cantor_left_spacing D N).
have hdelta : (0<delta)%R by rewrite /delta lt_min ltr01 hspacing.
exists delta; split=> // S hSdiam.
have hnu := @power_cantor_product_is_measure R P pair c m hc A B.
have hcost : 0<=e%:E*metric_real_diameter_cost b k S.
  apply: mule_ge0; first by rewrite lee_fin; exact: ltW he.
  exact: metric_real_power_cost_nonnegative (ltW hb).
have [hS0|hSne] := eqVneq S set0.
  rewrite hS0 (measure_empty hnu); by move: hcost; rewrite hS0.
have hSneP : S !=set0 by apply/set0P.
pose Dsize := extended_metric_diameter S.
have hD0 : 0<=Dsize := metric_diameter_nonnegative (extended_metric_diameter_specification S).
have hDfinite : Dsize< +oo := le_lt_trans hSdiam (ltry delta).
have hDnum : Dsize \is a fin_num by rewrite (ge0_fin_numE hD0).
pose d := fine Dsize.
have hDeq : Dsize=d%:E := esym (fineK hDnum).
have hd0 : (0<=d)%R by move: hD0; rewrite hDeq lee_fin.
have hdc : (d<=delta)%R by move: hSdiam; rewrite -/Dsize hDeq lee_fin.
have [hdz|hdne] := eqVneq d 0%R.
- have hz : extended_metric_diameter S=0 by rewrite -/Dsize hDeq hdz.
  by rewrite (@power_cantor_product_zero_diameter R P pair first second hp c m hc _ _ A B f g hcp hm hm1 hA hB S hz).
have hd : (0<d)%R by rewrite lt_neqAle eq_sym hdne hd0.
have /andP [hd1 hdn] : ((d<=1) && (d<=cantor_left_spacing D N))%R.
  by move: hdc; rewrite /delta le_min.
have [j [hNj [htop hbottom]]] := interleaved_cantor_spacing_band hD hd hdn.
have hexp := heindex j (leq_trans hNe hNj).
have hdiam : extended_metric_diameter S<=d%:E by rewrite -/Dsize hDeq.
have [r [hr hbound]] := @interleaved_power_cantor_product_band_bound R P pair first second hp
  c m k hc D A B f g hcp hm hm1 hD hA hB j S d hSneP hd hd1 hdiam htop hbottom hexp.
have hwidth : (real_power r m<=eta)%R.
  case: hr=> ->.
  - exact: (hw j (leq_trans hNw hNj)).2.
  - exact: (hw j.+1 (leq_trans hNw (leq_trans hNj (leqnSn j)))).1.
have hcoeff : (0<=K*real_power d k)%R := mulr_ge0 (ltW hK) (real_power_nonnegative d k).
have hsmall := ler_wpM2l hcoeff hwidth.
have hKe : (K*eta=e*b)%R by rewrite /eta mulrC divfK ?gt_eqF.
have heq : (K*real_power d k*eta=e*(b*real_power d k))%R.
  by rewrite mulrAC hKe mulrA.
apply: le_trans hbound _.
rewrite /metric_real_diameter_cost -/Dsize hDeq metric_real_power_cost_finite -EFinM lee_fin.
rewrite -heq; exact hsmall.
Qed.
