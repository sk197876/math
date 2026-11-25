(** Federer (1969), 3.2.7, p. 246: quantitative
    multiplicity of the printed oscillatory curve.
    Each positive sine cycle supplies one distinct
    crossing of all sufficiently small positive levels. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype lra ring.
From Federer Require Import RealMetricBackground RealTrigonometrySealed RealSineCycleValues
  OscillationCycleGeometry OscillatorySubstitutionCurve LocallyAbsolutelyContinuousCurve
  MappingMultiplicity ContinuousCrossingsMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [oscillatory_curve_cycle_zero]: the
    printed curve vanishes at the chosen reciprocal
    sine zeroes, supporting Federer 3.2.7, p. 246. *)
Lemma oscillatory_curve_cycle_zero (R:realType) L k:
  oscillatory_substitution_curve (@oscillation_zero_parameter R L k)= 0.
Proof.
rewrite /oscillatory_substitution_curve /oscillation_zero_parameter invrK real_sine_cycle_zero mulr0.
by [].
Qed.

(** Source for [oscillatory_curve_cycle_peak]: the
    positive peak height of the printed curve,
    supporting Federer 3.2.7, p. 246. *)
Lemma oscillatory_curve_cycle_peak (R:realType) L k:
  1<=2*L%:R*(@RealTrigonometry.half_period R) ->
  oscillatory_substitution_curve (@oscillation_peak_parameter R L k)=
    (@oscillation_peak_parameter R L k)*Num.sqrt ((@oscillation_peak_parameter R L k)).
Proof.
move=>hL.
have [hPos _]:=oscillation_cycle_parameter_bounds k hL.
rewrite /oscillatory_substitution_curve (ger0_norm (ltW hPos)).
rewrite /oscillation_peak_parameter invrK real_sine_cycle_peak mulr1.
by [].
Qed.

(** Source for [oscillatory_curve_peak_lower_bound]:
    on the selected unit-interval cycles, x sqrt(x)
    is at least x^2. This weaker height bound
    suffices for Federer 3.2.7, p. 246. *)
Lemma oscillatory_curve_peak_lower_bound (R:realType) L k:
  1<=2*L%:R*(@RealTrigonometry.half_period R) ->
  (@oscillation_peak_parameter R L k)^+2<=
    oscillatory_substitution_curve (@oscillation_peak_parameter R L k).
Proof.
move=>hL; have [hPos [hLess hOne]]:=oscillation_cycle_parameter_bounds k hL.
have hP1:(@oscillation_peak_parameter R L k)<=1:=le_trans (ltW hLess) hOne.
rewrite (oscillatory_curve_cycle_peak k hL).
have hs:=sqr_sqrtr (ltW hPos).
have hs0:=sqrtr_ge0 ((@oscillation_peak_parameter R L k)).
have hRoot:(@oscillation_peak_parameter R L k)<=Num.sqrt ((@oscillation_peak_parameter R L k)).
  nra.
rewrite expr2; exact (ler_wpM2l (ltW hPos) hRoot).
Qed.

(** Source for [oscillatory_curve_small_level_multiplicity]:
    actual counting fibres of the third example
    in Federer 3.2.7, p. 246: there exists
    c in (0,1] such that every positive y<=c^2/n^2
    has at least n distinct preimages in [0,1]. *)
Theorem oscillatory_curve_small_level_multiplicity (R:realType):
  exists c:R,0<c<=1 /\ forall n:nat,(0<n)%N -> forall y:R,
    0<y -> y<=(c/n%:R)^+2 ->
    (n%:R%:E<=@mapping_multiplicity R [the choiceType of real_line_metric R] R
      (@oscillatory_substitution_curve R) `[0%R,1%R] y)%E.
Proof.
have [L [hLPos hL]]:=oscillation_cycle_offset_exists R.
pose c:=@oscillation_crossing_constant R L.
have hc:0<c<=1:=oscillation_crossing_constant_bounds hL.
exists c; split=>// n hn y hy hY.
pose l:=fun i:'I_n=>@oscillation_peak_parameter R L i.
pose r:=fun i:'I_n=>@oscillation_zero_parameter R L i.
apply:(@continuous_disjoint_crossings_multiplicity_bound R
  (@oscillatory_substitution_curve R) `[0%R,1%R] n l r y).
- exact (locally_absolutely_continuous_curve_continuous
    (@oscillatory_substitution_curve_locally_absolutely_continuous R)).
- move=>i; exact:ltW (oscillation_cycle_parameter_bounds i hL).2.1.
- move=>i x; rewrite /= !in_itv /= =>/andP[hxl hxr].
  have [hPos [_ hOne]]:=oscillation_cycle_parameter_bounds i hL.
  rewrite /l /r in hxl hxr; apply/andP; split; lra.
- move=>i j hNe x hi hj.
  have hVal:(i:nat)!=(j:nat) by apply/eqP=>he; have hh: i=j:=val_inj he; by rewrite hh eqxx in hNe.
  case:(ltngtP (i:nat) (j:nat))=>hOrder; last by rewrite hOrder eqxx in hVal.
  + have hSep:=oscillation_cycle_parameters_separated hL hOrder.
    move:hi hj; rewrite /l /r =>/andP[hil hir] /andP[hjl hjr]; lra.
  + have hSep:=oscillation_cycle_parameters_separated hL hOrder.
    move:hi hj; rewrite /l /r =>/andP[hil hir] /andP[hjl hjr]; lra.
- move=>i; rewrite /r oscillatory_curve_cycle_zero.
  have hLow:c/n%:R<=l i:=oscillation_peak_reciprocal_index_bound hL hn (ltn_ord i).
  have hCPos:0<c/n%:R by rewrite divr_gt0 ?(andP hc).1 // ltr0n.
  have hPeak:=oscillatory_curve_peak_lower_bound i hL.
  rewrite /l in hLow; apply/andP; split; first exact:ltW hy.
  have hSq:(c/n%:R)^+2<=((@oscillation_peak_parameter R L i))^+2 by nra.
  exact (le_trans hY (le_trans hSq hPeak)).
Qed.
