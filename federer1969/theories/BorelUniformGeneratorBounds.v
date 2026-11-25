(** Federer (1969), 2.10.24(1), p. 187: finite-mass sets are approximated by
    Borel sets on which small generators have a uniform intersection-cost
    bound. The proof expands the appeal to 2.10.18(3) and Borel regularity:
    reciprocal-cutoff good sets exhaust the density-good points, continuity
    below supplies enough mass, and a finite Borel hull preserves all
    measurable-generator intersections. Source context:
    WeightedMetricEnvelopeUP.v. Corrected zero-cost density conventions are
    those already documented in CaratheodoryDensityFunction.v, not new
    assumptions here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP RegularMeasureContinuity TopologicalBorel BorelHullGeneratorBounds
  CaratheodoryDensityUpperBound CaratheodoryDensityFunction CaratheodoryDensityGoodSets
  CoveringRelationLimits CaratheodoryBorelRegular MetricDiameter ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [upper_density_good_sets_cover]: supporting
    uniform-cutoff exhaustion used for B_j in
    2.10.24(1), p. 187. Only the upper
    density conclusion at most one is required;
    generator costs may vanish under the already
    corrected covering quotient. *)
Theorem upper_density_good_sets_cover (R : realType) (X : metricType R)
    (F : set (set X)) (c mu : set X -> \bar R) (A : set X) (t : R) :
  is_measure mu -> (forall S, F S -> 0<=c S) -> (1<t)%R ->
  measure_almost_everywhere mu [set x | covering_upper_limit (caratheodory_family_relation F)
    (caratheodory_density_function mu c A) x<=1] ->
  mu (A `\` \bigcup_n caratheodory_density_good_set
    (fun j : set_type F=>val j) (fun j=>c (val j)) mu A t (((n.+1%:R : R)^-1)%R)%:E)=0.
Proof.
move=> hm hc ht hden.
have ht0 : (0<t)%R := lt_trans (@ltr01 R) ht.
apply: (@measure_null_subset R X mu hm _ _ _ hden)=> x [hxA hxU] hdx.
have htE : (1<t%:E) by rewrite lte_fin.
have hlt := le_lt_trans hdx htE.
have [delta [hd hlocal]] := @caratheodory_density_upper_local_estimate R X mu hm c
  (caratheodory_family_relation F) A x t ht0 (fun S hS=>hc S hS.1) hlt.
have [n hn] := reciprocal_metric_cutoffs_cofinal hd.
apply: hxU; exists n=> //; split=> // j hxj hdj.
exact: hlocal (val j) (conj (set_valP j) hxj) (le_trans hdj hn).
Qed.

(** Source for [borel_uniform_generator_approximation]: supporting
    single finite-stage Borel approximation for
    2.10.24(1), p. 187. Every prescribed
    positive mass tolerance and cost factor t>1
    admits a Borel subset with a uniform positive
    generator cutoff. No measurability of the
    intermediate density-good subsets is assumed. *)
Theorem borel_uniform_generator_approximation (R : realType) (X : metricType R)
    (F : set (set X)) (c mu : set X -> \bar R) (A : set X) (t e : R) :
  is_measure mu -> is_borel_regular_measure mu -> borel_set A -> mu A< +oo ->
  (forall S, F S -> 0<=c S) -> (forall S, F S -> measure_measurable mu S) ->
  (1<t)%R -> (0<e)%R ->
  measure_almost_everywhere mu [set x | covering_upper_limit (caratheodory_family_relation F)
    (caratheodory_density_function mu c A) x<=1] ->
  exists B (r : R), borel_set B /\ B `<=` A /\ (0<r)%R /\ mu (A `\` B)<e%:E /\
    forall S, F S -> extended_metric_diameter S<=r%:E -> mu (B `&` S)<=t%:E*c S.
Proof.
move=> hm hr hAb hAfin hc hS ht he hden.
pose r n := ((n.+1%:R : R)^-1)%R.
pose H n := caratheodory_density_good_set (fun j : set_type F=>val j)
  (fun j=>c (val j)) mu A t (r n)%:E.
have hHA n : H n `<=` A := @caratheodory_density_good_set_subset R X [the choiceType of set_type F]
  (fun j=>val j) (fun j=>c (val j)) mu A t (r n)%:E.
have hinc n m (hnm : (n<=m)%N) : H n `<=` H m.
  apply: (@caratheodory_density_good_set_cutoff R X [the choiceType of set_type F]
    (fun j=>val j) (fun j=>c (val j)) mu A t (r m)%:E (r n)%:E).
  have hn : (0<n.+1%:R :> R)%R by rewrite ltr0n.
  have hmp : (0<m.+1%:R :> R)%R by rewrite ltr0n.
  by rewrite lee_fin /r (lef_pV2 hmp hn) ler_nat.
have hnull : mu (A `\` \bigcup_n H n)=0 := @upper_density_good_sets_cover R X F c mu A t hm hc ht hden.
have hUA : (\bigcup_n H n) `<=` A by move=> x [n _ hx]; exact: hHA n x hx.
have hmass : mu (\bigcup_n H n)=mu A.
  apply/eqP; rewrite eq_le (@measure_mono R X mu hm _ _ hUA) /=.
  have hcov : A `<=` (\bigcup_n H n) `|` (A `\` \bigcup_n H n).
    move=> x hx; case: (pselect ((\bigcup_n H n) x))=> hxH; [by left|right; by split].
  have hh := @measure_binary_cover R X mu hm A (\bigcup_n H n) (A `\` \bigcup_n H n) hcov.
  by rewrite hnull adde0 in hh.
have hlim := regular_measure_continuity_below hm (borel_regular_is_regular hm hr) hinc.
rewrite hmass in hlim.
have hAfin_num : mu A \is a fin_num.
  rewrite ge0_fin_numE; last exact: (@measure_nonnegative R X mu hm A).
  exact hAfin.
have hlt : mu A-e%:E<mu A.
  rewrite lte_subel_addr // -{1}[mu A]adde0 lteD2lE // lte_fin; exact he.
have [N hN] := hlim.2.1 _ hlt.
have hnear := hN N (leqnn N); rewrite lte_subel_addr // in hnear.
pose J := [the choiceType of set_type F].
pose b (j : J) := t%:E*c (val j).
pose P : set J := [set j | extended_metric_diameter (val j)<=(r N)%:E].
have hb j : 0<=b j.
  apply: mule_ge0; [rewrite lee_fin; exact: ltW (lt_trans (@ltr01 R) ht)|exact: hc _ (set_valP j)].
have htest j : measure_measurable mu (val j) := hS _ (set_valP j).
have hlocal j : P j -> (H N `&` val j)!=set0 -> mu (A `&` val j)<=b j.
  move=> hdj [x [hx hxj]]; exact: hx.2 j hxj hdj.
have [B [hB [hHB [hBA [hval hBgen]]]]] := @borel_hull_preserves_generator_bounds R X J mu
  (fun j=>val j) b P A (H N) hm hr hAb hAfin (hHA N) htest hb hlocal.
have hBm := borel_regular_borel_measurable hm hr hB.
have hi : A `&` B=B.
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hBA x hx.
have hsplit := hBm A; rewrite hi in hsplit.
have hBfinite : mu B \is a fin_num.
  rewrite ge0_fin_numE; last exact: (@measure_nonnegative R X mu hm B).
  exact: le_lt_trans (@measure_mono R X mu hm B A hBA) hAfin.
have hloss : mu (A `\` B)<e%:E.
  have hh := hnear; rewrite -hval hsplit lteD2lE // in hh.
exists B,(r N); split=> //; split=> //; split.
- by rewrite /r invr_gt0 ltr0n.
- split=> // S hFS hdS.
  exact: hBgen (exist _ S (mem_set hFS)) hdS.
Qed.
