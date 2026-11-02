(** Federer (1969), 2.10.17(2), p. 179, proof: exhaust A by the increasing
    sets B(mu,t,1/(n+1)), apply the scale bound, and use regular continuity
    below. This quantitative local-bound formulation is separated from the
    density quotient, whose zero-denominator convention requires correction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleEnvelopeLaws
  CaratheodoryLimitUP CaratheodoryBorelRegular CaratheodoryDensityGoodSets
  MeasureUP RegularMeasureUP RegularMeasureContinuity ExtendedRealOrderLimit ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_density_local_bound]: supporting
    local-to-global step in the proof of 2.10.17(2), p. 179 The local
    generator estimate is explicit, so this theorem is independent of the
    disputed quotient convention and assumes no measurability of A or B. *)
Theorem caratheodory_density_local_bound (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R)
    (mu psi : set X -> \bar R) (A : set X) (t : R) :
  is_measure mu -> is_regular_measure mu -> (forall j, 0<=c j) ->
  is_caratheodory_limit S c psi -> (0<t)%R ->
  (forall x, A x -> exists delta : \bar R, 0<delta /\
    forall j, S j x -> extended_metric_diameter (S j)<=delta -> mu (A `&` S j)<=t%:E*c j) ->
  mu A<=t%:E*psi A.
Proof.
move=> hm hr hc hpsi ht hlocal.
pose d n := (((n.+1)%:R : R)^-1)%:E.
pose B n := caratheodory_density_good_set S c mu A t (d n).
have hd n : 0<d n := reciprocal_metric_cutoff_positive R n.
have hdm n m : (n<=m)%N -> d m<=d n.
  move=> hnm; rewrite /d lee_fin.
  have hnpos : (0 < (n.+1)%:R :> R)%R by rewrite ltr0n.
  have hmpos : (0 < (m.+1)%:R :> R)%R by rewrite ltr0n.
  by rewrite (@lef_pV2 R _ _ hmpos hnpos) ler_nat.
have hBmono n m : (n<=m)%N -> B n `<=` B m.
  move=> hnm; exact: caratheodory_density_good_set_cutoff (hdm n m hnm).
have hcover : (\bigcup_n B n)=A.
  apply/seteqP; split.
  - move=> x [n _ hx]; exact hx.1.
  - move=> x hx; have [delta [hdelta hbound]] := hlocal x hx.
    have [n hn] := reciprocal_metric_cutoffs_cofinal hdelta.
    exists n=> //; split=> // j hj hdiam.
    exact: hbound j hj (le_trans hdiam hn).
have hlim := @regular_measure_continuity_below R X mu hm hr B hBmono.
rewrite hcover in hlim.
apply: (extended_order_limit_upper_bound hlim.2)=> n.
pose nu := metric_scale_envelope S c (d n).
have hn := metric_scale_envelope_specification S c (d n).
have hb := @caratheodory_density_good_set_bound R X J S c mu nu A t (d n) hm hc ht hn.
apply: le_trans hb _.
apply: lee_wpmul2l; first by rewrite lee_fin; exact: ltW ht.
have hsub : caratheodory_density_good_set S c mu A t (d n) `<=` A.
  exact: caratheodory_density_good_set_subset.
have hmono := @metric_scale_envelope_mono R X J S c (d n) nu hn _ A hsub.
apply: le_trans hmono _.
exact (@caratheodory_limit_upper R X J S c psi hpsi A (d n) nu (hd n) hn).
Qed.
