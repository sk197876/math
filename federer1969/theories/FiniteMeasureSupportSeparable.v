(** Federer (1969), 2.2.16, p. 71, first assertion: the support of a finite
    Borel-measurable metric measure is separable. Follow the union of
    maximal separated sets in the printed proof. The conclusion uses the
    actual metric subspace of support points, including an empty support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureSupport SeparatedMetricSetUP SeparatedMetricNet
  MaximalSeparatedSealed SeparatedSupportCountable MetricSubsetBackground ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_support_separable]: direct
    first conclusion of Federer 2.2.16, p. 71.
    Countably many maximal 2/n-separated support sets have a
    countable union dense in the support. The ambient metric
    space need not be complete or separable. *)
Theorem finite_measure_support_separable (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  mu setT < +oo -> (forall U, open U -> measure_measurable mu U) ->
  exists D : set (metric_subset (measure_support mu)), countable D /\ dense D.
Proof.
move=> hf ho.
pose S := measure_support mu.
pose r k : R := (((k.+1)%:R)^-1)%R.
have hr k : (0 < r k)%R by rewrite /r invr_gt0 ltr0n.
pose N k := @MaximalSeparated.value R X S (r k + r k)%R.
have hN k := @MaximalSeparated.laws R X S (r k + r k)%R.
have hnc k : countable (N k).
  exact: (@separated_support_set_countable R X mu hm (N k) (r k) hf ho (hr k)
    (separated_subset_inside (hN k)) (separated_subset_separation (hN k))).
pose D0 := \bigcup_k N k.
have hD0 : countable D0.
  apply: bigcup_countable; first exact: countableP.
  by move=> k _; exact: hnc k.
pose D : set (metric_subset S) := [set z | D0 (val z)].
exists D; split.
- have /countable_injP[g hg] := hD0.
  apply/countable_injP; exists (fun z : metric_subset S => g (val z)).
  move=> x y; rewrite !inE=> hx hy he; apply: val_inj.
  apply: hg he; exact: mem_set.
- move=> W [x hx] hW.
  have hnb : nbhs x W by rewrite openE in hW; exact: hW x hx.
  have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP x W) hnb.
  have he2 : (0 < e/2)%R by rewrite divr_gt0 // ltr0n.
  have [k hk] := positive_reciprocal_nat_small he2.
  have hrr : (0 <= r k + r k)%R := addr_ge0 (ltW (hr k)) (ltW (hr k)).
  have [y [hy hdist]] := @maximal_separated_subset_covers R X S (N k)
    (r k+r k)%R hrr (hN k) (val x) (set_valP x).
  have hyS : S y := @separated_subset_inside R X S (r k+r k)%R (N k) (hN k) y hy.
  pose z : metric_subset S := Sub y (mem_set hyS).
  exists z; split.
  + apply: hb; change ((mdist (val x) y < e)%R).
    have hh := ltrD hk hk; rewrite -splitr in hh.
    exact: le_lt_trans hdist hh.
  + exists k; first exact Logic.I; exact hy.
Qed.
