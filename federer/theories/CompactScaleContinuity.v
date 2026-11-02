(** Federer (1969), 2.10.20, p. 182, final two compact-sequence statements.
    Open generators give equality with the mass of the intersection. The
    displayed interior-refining cost hypothesis instead gives an upper bound
    by the smaller-cutoff mass. The proof expands the printed brief
    assertions through compact neighbourhoods and the already sealed open
    envelope of 2.5.14, pp. 107–108. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MetricDiameter MetricScaleEnvelopeUP MetricScaleCutoffCost
  MetricScaleWeightedBound MetricScaleMeasureBound OpenCoverContentUP OpenCoverEnvelope
  ExtendedRealBounds ExtendedRealOrderLimit ExtendedRealDecreasingLimit CompactOpenEnvelopeBound
  InteriorRefiningMetricCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_scale_compact_open_continuity]: direct
    open-generator compact-sequence assertion in 2.10.20,
    p. 182. The supporting result allows any cutoff,
    and requires no finite initial mass. *)
Theorem metric_scale_compact_open_continuity (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R) (delta : \bar R)
    (nu : set X -> \bar R) (C : nat -> set X) :
  is_metric_scale_envelope S c delta nu -> (forall j, 0<=c j) ->
  (forall j, open (S j)) -> (forall n, compact (C n)) ->
  (forall n m, (n<=m)%N -> C m `<=` C n) ->
  extended_decreases_to (fun n => nu (C n)) (nu (\bigcap_n C n)).
Proof.
move=> hn hc hOpen hC hdec.
have hm := metric_scale_envelope_is_measure hn hc.
have ho := metric_scale_open_generator_envelope hn hc hOpen.
have hclosed n : closed (C n) := compact_closed (@metric_hausdorff R X) (hC n).
have hseq n m (hnm : (n<=m)%N) : nu (C m)<=nu (C n).
  exact: (@measure_mono R X nu hm (C m) (C n) (hdec n m hnm)).
have hlim := @extended_decreasing_limit R (fun n => nu (C n)) hseq.
have hb := @compact_decreasing_open_envelope_bound R X nu nu C hm ho (hC 0%N) hclosed hdec.
have hl : nu (\bigcap_n C n)<=extended_real_inf [set b | exists n, b=nu (C n)].
  apply: extended_real_inf_greatest=> b [n ->].
  apply: (@measure_mono R X nu hm)=> x hx; exact: hx n I.
have he : extended_real_inf [set b | exists n, b=nu (C n)]=nu (\bigcap_n C n).
  apply/eqP; by rewrite eq_le hb hl.
by rewrite he in hlim.
Qed.

(** Source for [metric_scale_compact_interior_refinement]: direct
    final inequality in 2.10.20, p. 182. The
    two scales remain independent objects specified by
    their covering laws. The supporting implication needs
    only the printed cost-infimum law; finite and
    infinite costs and limit values are retained. *)
Theorem metric_scale_compact_interior_refinement (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (c : J -> \bar R) (xi delta : \bar R)
    (small large : set X -> \bar R) (C : nat -> set X) :
  is_metric_scale_envelope S c xi small -> is_metric_scale_envelope S c delta large ->
  (forall j, 0<=c j) -> is_interior_refining_metric_cost S c xi delta ->
  (forall n, compact (C n)) -> (forall n m, (n<=m)%N -> C m `<=` C n) ->
  exists l, extended_decreases_to (fun n => large (C n)) l /\ l<=small (\bigcap_n C n).
Proof.
move=> hs hl hc href hC hdec.
have hm := metric_scale_envelope_is_measure hl hc.
pose ha := @measure_open_cover_content R X large hm.
pose omega := @open_cover_envelope R X large ha.
have how := @open_cover_envelope_specification R X large ha.
have hom := @open_cover_envelope_is_measure R X large ha.
have hclosed n : closed (C n) := compact_closed (@metric_hausdorff R X) (hC n).
have hbound := @compact_decreasing_open_envelope_bound R X large omega C hm how (hC 0%N) hclosed hdec.
have hgen j (hj : extended_metric_diameter (S j)<=xi) : omega (S j)<=c j.
  rewrite (href j hj); apply: extended_real_inf_greatest=> b [k [hjk [hkd ->]]].
  have h1 := @open_cover_envelope_lower R X large omega how (S j) (interior (S k))
    (open_interior _) hjk.
  have h2 : large (interior (S k))<=large (S k).
    apply: (@measure_mono R X large hm)=> x hx; exact: interior_subset hx.
  have h3 := @metric_scale_generator_bound R X J S c delta large k hl (hc k) hkd.
  exact: le_trans h1 (le_trans h2 h3).
have hcomp := @measure_bounded_by_metric_scale_envelope R X J S c xi small omega hs hom hgen.
pose l := extended_real_inf [set b | exists n, b=large (C n)].
exists l; split.
- apply: extended_decreasing_limit=> n m hnm.
  exact: (@measure_mono R X large hm (C m) (C n) (hdec n m hnm)).
- exact: le_trans hbound (hcomp (\bigcap_n C n)).
Qed.

(** Source for [federer_2_10_20_compact_open]: printed
    first compact-sequence assertion of 2.10.20,
    p. 182, with finite positive cutoff and the
    actual set family F. No finite-mass premise is added. *)
Theorem federer_2_10_20_compact_open (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (delta : R) (nu : set X -> \bar R)
    (C : nat -> set X) :
  (0<delta)%R -> (forall S, F S -> 0<=c S) -> (forall S, F S -> open S) ->
  is_metric_scale_envelope (fun j : set_type F => val j) (fun j => c (val j)) delta%:E nu ->
  (forall n, compact (C n)) -> (forall n m, (n<=m)%N -> C m `<=` C n) ->
  extended_decreases_to (fun n => nu (C n)) (nu (\bigcap_n C n)).
Proof.
move=> hd hc ho hn hC hdec.
apply: (metric_scale_compact_open_continuity hn _ _ hC hdec).
- move=> j; exact: hc _ (set_valP j).
- move=> j; exact: ho _ (set_valP j).
Qed.

(** Source for [federer_2_10_20_compact_refinement]: printed
    final assertion of 2.10.20, p. 182. The
    indexed infimum ranges exactly over T in F whose
    interiors contain S and whose diameters are at most
    delta. The source's 0<xi<delta is retained. *)
Theorem federer_2_10_20_compact_refinement (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (xi delta : R)
    (small large : set X -> \bar R) (C : nat -> set X) :
  (0<xi<delta)%R -> (forall S, F S -> 0<=c S) ->
  is_metric_scale_envelope (fun j : set_type F => val j) (fun j => c (val j)) xi%:E small ->
  is_metric_scale_envelope (fun j : set_type F => val j) (fun j => c (val j)) delta%:E large ->
  is_interior_refining_metric_cost (fun j : set_type F => val j) (fun j => c (val j)) xi%:E delta%:E ->
  (forall n, compact (C n)) -> (forall n m, (n<=m)%N -> C m `<=` C n) ->
  exists l, extended_decreases_to (fun n => large (C n)) l /\ l<=small (\bigcap_n C n).
Proof.
move=> hxd hc hs hl href hC hdec.
apply: (metric_scale_compact_interior_refinement hs hl _ href hC hdec)=> j.
exact: hc _ (set_valP j).
Qed.
