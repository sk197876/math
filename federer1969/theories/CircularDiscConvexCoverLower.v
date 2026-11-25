(** Federer (1969), 3.3.19, pp. 302–304:
    every sufficiently small original countable open
    convex cover has first-gauge cost at least
    lambda for every original 0<lambda<pi. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex MetricDiameter CoveringFamilyUP
  CircularTrigonometrySealed CircularDiscTreeUP CircularDiscLimitUP CircularDiscHitMeasureUP CircularDiscHitMeasureLaws
  CircularDiscSubordinateGaugeBound CircularDiscSubordinateFiniteCover
  IntegralGeometricGauge NonnegativeSum NonnegativeSumScale MeasureUP MeasureBasic MeasureIndexedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Cover.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation q:=(@integral_geometric_gauge R 2 1 (leqnSn 1) 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_small_convex_cover_lower]:
    the displayed countable-cover inequality preceding
    and following the boundary argument in 3.3.19,
    pp. 302–304. The original actual
    hit measures, finite subcover and common fine
    level are local witnesses. Every selected
    covering index remains in the original family;
    no finite-cover, boundary or mass premise is added. *)
Theorem circular_disc_small_convex_cover_lower (lam:R):0<lam ->lam<p ->
  exists d:R,0<d /\forall (I:choiceType) (D:set I) (U:I->set E),
    countable D ->(forall i,D i ->open (U i) /\is_inner_convex (U i) /\
      (extended_metric_diameter (U i)<=d%:E)%E) ->
    A `<=` \bigcup_(i in D) U i ->(lam%:E<=nonnegative_sum D (fun i=>q (U i)))%E.
Proof.
move=>hLam hLamP.
have [psi [hPsi hMeasures]]:=@circular_disc_hit_measures_exist R H.
have [d [hd hSetBound]]:=@circular_disc_subordinate_gauge_bound R H hH psi hPsi lam hLam hLamP.
exists d;split=>//;move=>I D U hCountable hU hCover.
have [nu [G [hGD [hGCover hContained]]]]:=@circular_disc_subordinate_finite_cover R H A I D U hH hA
  (fun i hi=>(hU i hi).1) hCover.
have hMu:=hMeasures nu.+1.
have hCoverMass:=@measure_indexed_cover R E I (psi nu.+1) hMu A [set` G] U
  (finite_set_countable (finite_fset G)) hGCover.
have hWeighted:=lee_wpmul2l (lee_tofin (ltW hLam)) hCoverMass.
rewrite (@circular_disc_hit_limit_mass_one R H psi hPsi hH A hA nu.+1) mule1 in hWeighted.
have hScale:=@nonnegative_sum_scale R I [set` G] (fun i=>psi nu.+1 (U i)) lam (ltW hLam)
  (fun i _=>measure_nonnegative hMu (U i)).
rewrite -hScale in hWeighted.
apply:(le_trans hWeighted).
apply:(le_trans _ (@nonnegative_sum_subset R I [set` G] D (fun i=>q (U i))
  (fun i hi=>hGD i hi))).
apply:nonnegative_sum_mono=>i hi.
have hiD:=hGD i hi.
exact:(hSetBound nu (U i) (hU i hiD).1 (hU i hiD).2.1 (hU i hiD).2.2 (hContained i hi)).
Qed.
End Cover.
