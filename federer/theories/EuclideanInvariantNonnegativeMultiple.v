(** Supporting Haar comparison for Federer (1969),
    3.2.45, p. 280, using 2.7.7, p. 125,
    and the Euclidean Haar measure of 2.7.16, p. 134. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  cardinality constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanAdditiveGroup
  EuclideanLebesgue EuclideanLebesgueDimensions EuclideanLebesgueHaar TranslationInvariantHaar HaarIntegralUP
  MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_invariant_nonnegative_multiple]:
    supporting zero-measure extension of Haar uniqueness
    used in Federer 3.2.45, p. 280; compare
    2.7.7, p. 125, and 2.7.16, p. 134.
    An invariant Borel regular measure, finite on compact
    sets, is a nonnegative finite multiple of actual
    Lebesgue measure. If no compact set has positive
    mass, the existing countable compact cover proves
    that every set has mass zero. The multiplication
    here is the total extended-real multiplication;
    a later original partial-product theorem retains its domain. *)
Theorem euclidean_invariant_nonnegative_multiple (R : realType) n
    (phi : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :
  is_invariant_borel_measure (fun x y : inner_metric_space (@euclidean_inner_productP R n) => (x+y)%R) phi ->
  exists2 d : R, (0 <= d)%R & forall A,
    phi A = d%:E * @euclidean_lebesgue_measure R n A.
Proof.
move=> hPhi.
have hMeasure := invariant_borel_measure_law hPhi.
case: (pselect (exists C, compact C /\ 0 < phi C))=> [[C [hC hPositive]]|hNo].
- have [base hBase] := @euclidean_countable_open_base R n.
  have [hOpen hCompact hCover] := @euclidean_ball_cover R n.
  have hHaar := invariant_borel_left_haar (euclidean_additive_lch_group R n)
    hBase hOpen hCompact hCover hPhi hC hPositive.
  have [d hD hValue] := @euclidean_haar_measure_multiple R n phi (or_introl hHaar).
  exists d; first exact: ltW hD.
  exact hValue.
- have hCompactZero (C : set (inner_metric_space (@euclidean_inner_productP R n)))
      (hC : compact C) : phi C = 0.
    apply/eqP; rewrite eq_le (measure_nonnegative hMeasure) andbT.
    rewrite leNgt; apply/negP=> hPositive; apply: hNo.
    by exists C.
  have [hOpen hCompact hCover] := @euclidean_ball_cover R n.
  have hBallZero j : phi (@euclidean_open_ball_sequence R n j) = 0.
    have [C hC hSub] := hCompact j.
    have hBound := measure_mono hMeasure hSub.
    rewrite (hCompactZero C hC) in hBound.
    by apply/eqP; rewrite eq_le hBound (measure_nonnegative hMeasure).
  have hWholeCover : setT `<=` \bigcup_(j in @setT nat) @euclidean_open_ball_sequence R n j.
    move=> x _; have [j hJ] := hCover x; by exists j.
  have hBound := @measure_indexed_cover R _ nat phi hMeasure setT setT
    (@euclidean_open_ball_sequence R n) (countableP _) hWholeCover.
  rewrite (nonnegative_sum_zero (fun j _ => hBallZero j)) in hBound.
  exists 0%R; first exact: lexx.
  move=> A; rewrite mul0e; apply/eqP; rewrite eq_le (measure_nonnegative hMeasure) andbT.
  exact: le_trans (measure_mono hMeasure (subsetT A)) hBound.
Qed.
