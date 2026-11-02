(** Borel regularity of the measure introduced in Federer (1969), 2.9.8, p.
    156. Convert them to Borel almost covers using the original class-M
    reference measure and 2.2.3, p. 61, then intersect reciprocal-error
    covers to attain the density mass. This proves, rather than assumes, the
    Borel regularity needed for applying 2.9.7. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialExtendedOrderLoci
  MeasureUP MeasureBasic MeasureAlmostUP MeasurableFunctionUP BorelRegularMeasureUP TopologicalBorel
  MeasureDerivationContext DerivationMeasurableCover DensityMeasurableAlmostCover
  MeasureDensityUP MeasureDensityCover MeasureDensityMeasurable MeasureDensityNullSets
  ExtendedRealReciprocalBounds VitaliMassObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [density_borel_almost_cover]: supporting Borel cover for the
    class-M assertion in Federer 2.9.8, p. 156. The density mass of a
    finite-mass target is approximated from above by Borel supersets, via. *)
Lemma density_borel_almost_cover (R : realType) (X : metricType R)
    (phi nu : set X -> \bar R) (f : partial_function X (extended_real_line R)) S (e : R) :
  is_derivation_measure phi -> is_measure_density phi f nu -> is_measure_measurable_function phi f ->
  measure_almost_everywhere phi (partial_extended_nonnegative_locus f) ->
  nu S< +oo -> (0<e)%R ->
  exists B, borel_set B /\ S `<=` B /\ nu B<nu S+e%:E.
Proof.
move=> hf hn hfm hp hSf he; have hm := derivation_measure_law hf.
have hmn := @measure_density_is_measure R X phi nu hm f hn hp.
have [B [hBm [hSB herr]]] := @density_measurable_almost_cover R X phi nu f S e hm hn hfm hp hSf he.
have [C [hC [hBC hz]]] := @derivation_measurable_borel_cover R X phi B hf hBm.
have hzn := @measure_density_null_set R X phi nu hm f (C `\` B) hn hz.
have hbound := @null_remainder_measure_cover_bound R X nu C B hmn hzn.
exists C; split=> //; split.
- move=> x hx; exact: hBC x (hSB x hx).
- exact: le_lt_trans hbound herr.
Qed.

(** Source for [density_is_borel_regular]: supporting
    Borel regularity of psi in Federer 2.9.8,
    p. 156. A countable intersection of
    reciprocal-error Borel covers attains every finite
    mass; the whole space handles an infinite mass.
    Local bounded finiteness of the density is not
    assumed here and is established separately. *)
Theorem density_is_borel_regular (R : realType) (X : metricType R)
    (phi nu : set X -> \bar R) (f : partial_function X (extended_real_line R)) :
  is_derivation_measure phi -> is_measure_density phi f nu -> is_measure_measurable_function phi f ->
  measure_almost_everywhere phi (partial_extended_nonnegative_locus f) ->
  is_borel_regular_measure nu.
Proof.
move=> hf hn hfm hp; have hm := derivation_measure_law hf.
have hmn := @measure_density_is_measure R X phi nu hm f hn hp.
constructor.
- move=> U hU; apply: (@measure_density_preserves_measurable_sets R X phi nu hm f U hn hp).
  exact (@borel_regular_open_measurable R X phi (derivation_measure_borel_regular hf) U hU).
- move=> S; case: (ltP (nu S) +oo)=> hSf.
  + have hex n : exists B, borel_set B /\ S `<=` B /\ nu B<nu S+((n.+1%:R : R)^-1)%:E.
      apply: (@density_borel_almost_cover R X phi nu f S _ hf hn hfm hp hSf).
      by rewrite invr_gt0 ltr0n.
    pose C n := projT1 (cid (hex n)).
    have hC n : borel_set (C n) /\ S `<=` C n /\ nu (C n)<nu S+((n.+1%:R : R)^-1)%:E := projT2 (cid (hex n)).
    pose B := \bigcap_n C n.
    have hSB : S `<=` B by move=> x hx n _; exact: (hC n).2.1 x hx.
    have hB : borel_set B.
      apply: (@borel_set_countable_intersection X _ setT C (countableP _)); first by exists 0%N.
      by move=> n _; exact: (hC n).1.
    exists B; split=> //; split=> //.
    apply/eqP; rewrite eq_le; apply/andP; split; first exact (@measure_mono R X nu hmn S B hSB).
    have hfin : nu S \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hmn S)).
    rewrite -(fineK hfin); apply: extended_real_reciprocal_upper_bound=> n.
    have hBC : B `<=` C n by move=> x hx; exact: hx n Logic.I.
    have h := le_lt_trans (@measure_mono R X nu hmn B (C n) hBC) (hC n).2.2.
    rewrite -(fineK hfin) -EFinD in h; exact: ltW h.
  + exists setT; split; first by move=> x _.
    split; first exact: open_borel_set openT.
    apply/eqP; rewrite eq_le; apply/andP; split; first exact (@measure_mono R X nu hmn S setT (subsetT S)).
    exact: le_trans (leey (nu setT)) hSf.
Qed.
