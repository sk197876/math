(** Federer (1969), 2.3.2(7), p. 75: the thin strip above r has arbitrarily
    small measure when the test set has finite measure. The proof bounds the
    strip by the tail of the band series. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology MeasureUP MeasureIndexedCover
  MeasurableSeparationUP ReciprocalLevelBands LevelBandParityBounds NonnegativeSum
  NonnegativeSeriesTails.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [level_band_series_finite]: supporting finite
    band-series assertion in Federer 2.3.2(7), p. 75.
    Its bound is mu(T)+mu(T), with finite mu(T). *)
Lemma level_band_series_finite (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (T : set X) (r : R) :
  is_measure_level_separated mu f -> mu T < +oo ->
  nonnegative_sum setT (fun n => mu (test_reciprocal_level_band f T r n)) < +oo.
Proof.
move=> hs hT; apply: le_lt_trans (@level_band_series_bound R X mu hm f T r hs) _.
exact (lte_add_pinfty hT hT).
Qed.

(** Source for [level_thin_strip_small]: direct epsilon estimate for the
    thin strip in Federer 2.3.2(7), p. 75, just before the final splitting
    inequality *)
Theorem level_thin_strip_small (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (T : set X) (r eps : R) :
  is_measure_level_separated mu f -> mu T < +oo -> (0 < eps)%R ->
  exists N, mu (T `&` partial_function_preimage f
    [set y | r%:E < y /\ y <= (reciprocal_level_endpoint r N)%:E]) < eps%:E.
Proof.
move=> hs hT he.
have hseries := @level_band_series_finite R X mu hm f T r hs hT.
have [N hN] := @nonnegative_series_tail_small R
  (fun n => mu (test_reciprocal_level_band f T r n)) eps
  (fun n => @measure_nonnegative R X mu hm _) hseries he.
exists N; apply: le_lt_trans _ hN.
apply: (@measure_indexed_cover R X nat mu hm _ [set n | (N <= n)%N]
  (fun n => test_reciprocal_level_band f T r n) (countableP _)).
move=> x [hx [y [hy [hry hyr]]]].
have [n [hn hband]] := @reciprocal_level_tail_crossing R r N y hry hyr.
exists n=> //; split=> //; by exists y.
Qed.
