(** Federer (1969), 2.10.26, p. 190: the displayed countable-intersection
    formula for closed fibre- mass sublevels of a compact source set. The
    finite open cover budget is strictly t+1/j, as checked in the scan. Use
    open-generator approximation and the abstract covering-infimum laws; no
    particular measure construction is unfolded. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealReciprocalBounds MetricDiameter
  HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost HausdorffFibreCutoffs
  CompactFibreOpenCovers CompactHausdorffOpenApproximation MetricScaleEnvelopeUP MetricScaleEnvelopeLaws
  MetricScaleCutoffCost CaratheodoryLimitUP CaratheodoryBorelRegular MeasureUP MeasureBasic
  NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_scale_set_family_bound]: supporting
    cover comparison for the reverse sublevel inclusion
    in 2.10.26, p. 190. Covers are families of
    actual sets, while the existing infimum interface
    indexes nonempty generators. The singleton-cover and
    outer-measure laws bridge these presentations. *)
Lemma hausdorff_scale_set_family_bound (R : realType) (X : metricType R)
    (k : nat) (delta : \bar R) (nu : set X -> \bar R) (B : set X) (G : set (set X)) :
  is_metric_scale_envelope (fun j : @nonempty_metric_sets R X=>val j)
    (fun j=>hausdorff_diameter_cost k (val j)) delta nu ->
  countable G -> (forall S, G S -> S!=set0 /\ extended_metric_diameter S<=delta) ->
  B `<=` \bigcup_(S in G) S -> nu B<=nonnegative_sum G (fun S=>hausdorff_diameter_cost k S).
Proof.
move=> hn hG hS hcover.
have hm := metric_scale_envelope_is_measure hn
  (fun j=>hausdorff_diameter_cost_nonnegative k (val j)).
apply: le_trans (@measure_countable_cover R X nu hm B G hG hcover) _.
apply: nonnegative_sum_mono=> S hGS.
pose j : @nonempty_metric_sets R X := Sub S (mem_set (hS S hGS).1).
have hc : S `<=` \bigcup_(i in [set j]) val i by move=> x hx; exists j.
have hdiam (i : @nonempty_metric_sets R X) (hi : [set j] i) :
    extended_metric_diameter (val i)<=delta.
  rewrite (hi : i=j); exact: (hS S hGS).2.
have hh := @metric_scale_envelope_lower R X (@nonempty_metric_sets R X)
  (fun i=>val i) (fun i=>hausdorff_diameter_cost k (val i)) delta nu hn S [set j]
  (countable1 j) hdiam hc.
by rewrite nonnegative_sum_singleton in hh; last exact: hausdorff_diameter_cost_nonnegative.
Qed.

(** Source for [compact_fibre_mass_closed_level_formula]:
    direct displayed formula in 2.10.26, p. 190.
    Index n denotes the positive book index j=n+1.
    The proof works for every finite real t,
    strengthening the printed t>0 restriction. *)
Theorem compact_fibre_mass_closed_level_formula (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) (k : nat) (t : R) :
  continuous f -> compact A ->
  [set y | hausdorff_fibre_mass f A k y<=t%:E]=
    \bigcap_n fibre_open_cover_locus f A k ((n.+1%:R : R)^-1)%R%:E
      (t+(n.+1%:R : R)^-1)%R%:E.
Proof.
move=> hf hA; apply/seteqP; split.
- move=> y hy n _.
  have hpre : closed (f @^-1` [set y]).
    exact: (continuous_closedP f).1 hf _ (compact_closed (@metric_hausdorff R Y) (@compact_set1 Y y)).
  have hK := compact_closedI hA hpre.
  have hd : (0<(n.+1%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
  have hb : @hausdorff_measure R X k (A `&` f @^-1` [set y])<
      (t+(n.+1%:R : R)^-1)%R%:E.
    apply: le_lt_trans hy _; rewrite lte_fin ltrDl; exact hd.
  have [G [hG [hS [hcover hcost]]]] := compact_hausdorff_finite_open_cover_below hK hd hb.
  exists G; split=> //; split=> //; by split.
- move=> y hy; change (is_true (@hausdorff_measure R X k (A `&` f @^-1` [set y])<=t%:E)).
  apply: (caratheodory_limit_least (@hausdorff_measure_specification R X k))=> delta nu hd hn.
  have [N hN] := reciprocal_metric_cutoffs_cofinal hd.
  apply: (@extended_real_reciprocal_upper_bound R (nu (A `&` f @^-1` [set y])) t)=> n.
  have [G [hG [hS [hcover hcost]]]] := hy (n+N)%N Logic.I.
  have hsize S (hGS : G S) : S!=set0 /\ extended_metric_diameter S<=delta.
    split; first exact: (hS S hGS).2.1.
    apply: le_trans (hS S hGS).2.2 (le_trans _ hN).
    rewrite lee_fin; exact: fibre_reciprocal_cutoff_antitone (leq_addl n N).
  have hh := @hausdorff_scale_set_family_bound R X k delta nu _ G hn
    (finite_set_countable hG) hsize hcover.
  apply: le_trans (ltW (le_lt_trans hh hcost)) _.
  rewrite lee_fin lerD2l; exact: fibre_reciprocal_cutoff_antitone (leq_addr N n).
Qed.
