(** Federer (1969), 4.1.7, p. 358:
    the weighted measure used in the original
    dominated-density proof is Radon on U.
    This supporting theorem keeps the original
    compact finiteness and compact/open covers
    explicit; the covers are supplied by 4.1.1. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialExtendedOrderLoci
  MeasureUP MeasureBasic MeasureAlmostUP MeasurableFunctionUP RadonMeasureUP RadonBorelRegularity
  RadonCompactCoverCountablyMeasurable CountablyFiniteDensityBorel CountableLocalFiniteMetricRadon
  MeasureDensityUP MeasureDensityCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_compact_finite_radon_density]:
    a measurable nonnegative density with finite
    compact masses defines a Radon measure on
    the countably covered original domain, supporting
    Federer 4.1.7, p. 358, by 2.4.10,
    p. 85, and 2.2.5, pp. 62–63.
    No bounded-set finiteness is assumed. *)
Theorem countable_compact_finite_radon_density (R:realType) (X:metricType R)
    (mu nu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (h:partial_function X (extended_real_line R)) (C W:nat->set X):
  is_measure_density mu h nu ->is_measure_measurable_function mu h ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus h) ->
  (forall K,compact K ->nu K< +oo) ->
  (forall j,compact (C j)) ->(forall j,open (W j)) ->(forall j,W j `<=` C j) ->
  setT `<=` \bigcup_j C j ->setT `<=` \bigcup_j W j ->is_radon_measure nu.
Proof.
move=>hn hh hp hFinite hC hW hWC hCover hWCover.
have hCount:=@radon_compact_cover_countably_measurable R X mu hm hr C hC hCover.
have hNu:=@measure_density_is_measure R X mu nu hm h hn hp.
have hBorel:=@countably_finite_density_borel_regular R X mu nu h hm
  (radon_borel_regular hm hr) hCount hn hh hp.
have hWF j:open (W j) /\nu (W j)< +oo.
  split; first exact:hW.
  exact:le_lt_trans (measure_mono hNu (hWC j)) (hFinite _ (hC j)).
exact:(@countable_locally_finite_metric_radon R X nu C W hNu hBorel
  (radon_locally_compact hr) hFinite hC hCover hWF hWCover).
Qed.
