(** Federer (1969), 2.10.28(3), p. 192: the upper mass bound psi(A intersect
    T)<=zeta(T). Every finite level is special for the corrected single
    root. Its intersections with T cover A intersect T, and their diameters
    tend uniformly to zero. Apply (1) and the abstract covering infimum,
    then its cutoff supremum. Use Federer's erratum p. 4, book p. 192 line
    4, for card(H_0)=1. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge CompactIntervalDiameter MetricDiameter
  ConcaveIntervalGaugeUP ConcaveIntervalMeasure SpecialIntervalFamilyUP SpecialIntervalTreeLevels
  SpecialIntervalClipping CaratheodoryLimitUP CaratheodoryBorelRegular MetricScaleEnvelopeUP
  MetricScaleIndexedCover NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_28_3_upper]: direct first
    mass conclusion in 2.10.28(3), p. 192.
    The limit set is used through its abstract
    membership laws; the corrected single-root
    tree and printed mesh hypothesis suffice.
    Empty limits and degenerate test intervals
    remain included. *)
Theorem federer_2_10_28_3_upper (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (H : nat -> {fset compact_real_intervals R})
    (ht : is_special_interval_tree h H) (A : set (real_line_metric R))
    (hA : is_special_interval_tree_limit H A) (T : compact_real_intervals R) :
  concave_interval_measure h (A `&` val T)<=(concave_interval_cost h (val T))%:E.
Proof.
have [J hroot] := @special_tree_single_root R h H ht.
have hlevels := @special_interval_tree_level_special R h hg H ht J hroot.
apply: (caratheodory_limit_least (concave_interval_measure_specification h))=> delta nu hd hn.
have [n hcut] := reciprocal_metric_cutoffs_cofinal hd.
pose e := ((n.+1%:R : R)^-1)%R.
have he : (0<e)%R by rewrite /e invr_gt0 ltr0n.
have [N hmesh] := @special_tree_mesh R h H ht e he.
pose I := compact_real_intervals R.
pose D := [set S : I | S \in H N /\ val T `&` val S !=set0].
have hDsub : D `<=` [set S : I | S \in H N] by move=> S hS; exact hS.1.
have hD : countable D := sub_countable (subset_card_le hDsub) (finite_set_countable (finite_fset (H N))).
have hex (S : I) : exists V : I, D S -> val V=val T `&` val S.
  case: (pselect (D S))=> hS.
  - have hI := compact_real_interval_intersection (set_valP T) (set_valP S) hS.2.
    exists (Sub (val T `&` val S) (mem_set hI)); by move=> _.
  - exists J; by move=> hfalse; case: (hS hfalse).
pose q (S : I) := projT1 (cid (hex S)).
have hq (S : I) (hS : D S) : val (q S)=val T `&` val S := projT2 (cid (hex S)) hS.
have hsize (S : I) (hS : D S) : extended_metric_diameter (val (q S))<=delta.
  rewrite (hq S hS).
  apply: le_trans (@extended_metric_diameter_mono R [the metricType R of real_line_metric R]
    (val T `&` val S) (val S) (fun x hx=>hx.2)) _.
  have hsmall : extended_metric_diameter (val S)<=e%:E.
    exact ((@compact_interval_diameter_bound R (val S) e (set_valP S)).2
      (hmesh N (leqnn N) S hS.1)).
  exact: le_trans hsmall hcut.
have hcover : A `&` val T `<=` \bigcup_(S in D) val (q S).
  move=> x [hxA hxT]; have [S [hS hxS]] := (hA x).1 hxA N.
  have hactive : D S by split=> //; exists x; by split.
  exists S; first exact hactive.
  rewrite (hq S hactive); by split.
pose c := fun V : I=>(concave_interval_cost h (val V))%:E.
have hc V : 0<=c V by rewrite /c lee_fin; exact (@concave_interval_cost_nonnegative R h hg (val V)).
have hb := @metric_scale_envelope_indexed_cover R [the metricType R of real_line_metric R] I I
  (fun V=>val V) c delta nu hn (A `&` val T) D q hD (fun S _=>hc (q S)) hsize hcover.
have hcosteq : nonnegative_sum D (fun S=>c (q S))=
    nonnegative_sum D (fun S=>(concave_interval_cost h (val T `&` val S))%:E).
  apply: nonnegative_sum_ext=> S hS; by rewrite /c (hq S hS).
have hbudget := @nonnegative_sum_subset R I D [set S : I | S \in H N]
  (fun S=>(concave_interval_cost h (val T `&` val S))%:E) hDsub.
rewrite hcosteq in hb.
have hnonn (S : I) : 0<=(concave_interval_cost h (val T `&` val S))%:E.
  rewrite lee_fin; exact (@concave_interval_cost_nonnegative R h hg (val T `&` val S)).
rewrite (@nonnegative_sum_finite R I (H N)
  (fun S=>(concave_interval_cost h (val T `&` val S))%:E) (fun S _=>hnonn S)) sumEFin in hbudget.
have hfinal := @federer_2_10_28_1 R h hg J T (H N) (hlevels N).
have hfinalE : (\sum_(S <- H N) concave_interval_cost h (val T `&` val S))%:E<=
    (concave_interval_cost h (val T))%:E by rewrite lee_fin.
exact: le_trans (le_trans hb hbudget) hfinalE.
Qed.
