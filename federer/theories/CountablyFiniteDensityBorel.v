(** Federer (1969), 4.1.7, p. 358: the
    measurable norm density defines a Borel regular
    measure on the original open domain. The
    supporting proof uses 2.4.10, p. 85, and
    finite-piece Borel approximation from 2.2.3,
    pp. 61–62. No bounded-set finiteness is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureDensityMeasurable ExtendedRealOrderTopology PartialFunctionUP PartialExtendedOrderLoci
  MeasureUP MeasureBasic MeasurableFunctionUP MeasureAlmostUP CountablyMeasurableUP
  BorelRegularMeasureUP TopologicalBorel CountablyFiniteBorelCover DensityMeasurableAlmostCover
  MeasureDensityUP MeasureDensityCover MeasureDensityNullSets ExtendedRealReciprocalBounds
  VitaliMassObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_finite_density_borel_almost_cover]:
    every finite weighted mass has Borel almost
    covers, supporting Federer 4.1.7, p. 358,
    by 2.4.10, p. 85, and 2.2.3,
    pp. 61–62. The original target need not be
    measurable for either measure. *)
Lemma countably_finite_density_borel_almost_cover (R:realType) (X:topologicalType)
    (mu nu:set X->\bar R) (h:partial_function X (extended_real_line R)) A (e:R):
  is_measure mu ->is_borel_regular_measure mu ->
  measure_countably_measurable mu setT ->
  is_measure_density mu h nu ->is_measure_measurable_function mu h ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus h) ->
  nu A< +oo ->(0<e)%R ->
  exists B,borel_set B /\ A `<=` B /\ nu B<nu A+e%:E.
Proof.
move=>hm hr hCount hn hh hp hFinite he.
have hnM:=@measure_density_is_measure R X mu nu hm h hn hp.
have [C [hC [hAC hError]]]:=
  @density_measurable_almost_cover R X mu nu h A e hm hn hh hp hFinite he.
have [B [hB [hCB hZero]]]:=
  @countably_finite_measurable_borel_cover R X mu hm hr hCount C hC.
have hZeroN:=@measure_density_null_set R X mu nu hm h (B `\` C) hn hZero.
have hBound:=@null_remainder_measure_cover_bound R X nu B C hnM hZeroN.
exists B; split=>//; split.
- move=>x hx; exact:hCB x (hAC x hx).
- exact:le_lt_trans hBound hError.
Qed.

(** Source for [countably_finite_density_borel_regular]:
    Borel regularity of the original weighted measure,
    supporting Federer 4.1.7, p. 358. The
    earlier finite-error hull construction of 2.2.3,
    pp. 61–62, applies on the countably finite
    original domain. Local finiteness of the weighted
    measure is a separate assertion. *)
Theorem countably_finite_density_borel_regular (R:realType) (X:topologicalType)
    (mu nu:set X->\bar R) (h:partial_function X (extended_real_line R)):
  is_measure mu ->is_borel_regular_measure mu ->
  measure_countably_measurable mu setT ->
  is_measure_density mu h nu ->is_measure_measurable_function mu h ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus h) ->
  is_borel_regular_measure nu.
Proof.
move=>hm hr hCount hn hh hp.
have hnM:=@measure_density_is_measure R X mu nu hm h hn hp.
constructor.
- move=>V hV; apply:(@measure_density_preserves_measurable_sets R X mu nu hm h V hn hp).
  exact:(@borel_regular_open_measurable R X mu hr V hV).
- move=>A; case:(ltP (nu A) +oo)=>hFinite.
  + have hex n:exists B,borel_set B /\ A `<=` B /\
        nu B<nu A+((n.+1%:R:R)^-1)%:E.
      apply:(@countably_finite_density_borel_almost_cover R X mu nu h A _
        hm hr hCount hn hh hp hFinite).
      by rewrite invr_gt0 ltr0n.
    pose C n:=projT1 (cid (hex n)).
    have hC n:=projT2 (cid (hex n)).
    pose B:=\bigcap_n C n.
    have hAB:A `<=` B by move=>x hx n _; exact:(hC n).2.1 x hx.
    have hB:borel_set B.
      apply:(@borel_set_countable_intersection X _ setT C (countableP _));
        first by exists 0%N.
      by move=>n _; exact:(hC n).1.
    exists B; split=>//; split=>//.
    apply/eqP; rewrite eq_le; apply/andP; split; first exact:(measure_mono hnM hAB).
    have hNum:nu A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hnM A)).
    rewrite -(fineK hNum); apply:extended_real_reciprocal_upper_bound=>n.
    have hBC:B `<=` C n by move=>x hx; exact:hx n Logic.I.
    have hBound:=le_lt_trans (measure_mono hnM hBC) (hC n).2.2.
    rewrite -(fineK hNum) -EFinD in hBound; exact:ltW hBound.
  + exists setT; split; first by move=>x _.
    split; first exact:open_borel_set openT.
    apply/eqP; rewrite eq_le; apply/andP; split;
      first exact:(measure_mono hnM (subsetT A)).
    exact:le_trans (leey (nu setT)) hFinite.
Qed.
