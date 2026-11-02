(** Federer (1969), 2.10.24(2), pp. 187–188: supporting reduction of
    countable weighted covers to finite covers using 2.10.22. Strict
    positive level sets are increasing unions of the corresponding
    finite-prefix level sets, even when the pointwise sum is infinite. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderLimit ExtendedRealLimitBounds IncreasingProjectionLoss
  NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction NonnegativeSumContinuity
  CountableFiniteExhaustionUP CountableFiniteExhaustionSealed FiniteExhaustionSumLimit
  WeightedMetricEnvelopeUP FiniteWeightedGeneratorSums.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_weighted_level_finite_reduction]:
    supporting use of continuity below in 2.10.24(2),
    p. 188, first paragraph. Continuity is assumed
    here as a proved input property, subsequently
    supplied by 2.10.22. No measurability or finite
    pointwise sum is required. *)
Theorem countable_weighted_level_finite_reduction (R : realType) (X J : choiceType)
    (S : J -> set X) (G : set J) (u : J -> R) (nu : set X -> \bar R) (t B : \bar R) :
  has_increasing_set_continuity nu -> countable G -> (forall j, G j -> (0<=u j)%R) ->
  (forall P : {fset J}, (forall j, j \in P -> G j) ->
    nu [set x | t<weighted_generator_sum S [set` P] u x]<=B) ->
  nu [set x | t<weighted_generator_sum S G u x]<=B.
Proof.
move=> hcont hG hu hfinite.
pose C := @CountableFiniteExhaustion.value J G hG.
have hC := @CountableFiniteExhaustion.laws J G hG.
pose A n := [set x | t<weighted_generator_sum S [set` C n] u x].
have hinc n m (hnm : (n<=m)%N) : A n `<=` A m.
  move=> x hx; apply: lt_le_trans hx _; apply: nonnegative_sum_subset=> j [hj hxj]; split=> //.
  exact: (fsubsetP (finite_exhaustion_increasing hC hnm)) j hj.
have hsum x : extended_increases_to (fun n=>weighted_generator_sum S [set` C n] u x)
    (weighted_generator_sum S G u x).
  pose v j := if x \in S j then (u j)%:E else 0.
  have hv j (hj : G j) : 0<=v j by rewrite /v; case: ifP=> _; [rewrite lee_fin; exact: hu|exact: lexx].
  have hlim := finite_exhaustion_nonnegative_sum_limit hC hv.
  have he n : \sum_(j <- C n) v j=weighted_generator_sum S [set` C n] u x.
    rewrite (finite_weighted_generator_point_sum _ _ (fun j hj=>hu j (finite_exhaustion_subset hC hj))) /v -sumEFin.
    apply: eq_big_seq=> j hj; by case: ifP.
  have hvsum : nonnegative_sum G v=weighted_generator_sum S G u x.
    rewrite /weighted_generator_sum -nonnegative_sum_restrict; apply: nonnegative_sum_ext=> j hj.
    have heq : (j \in [set j | S j x])=(x \in S j).
      apply/idP/idP=> /set_mem hx; apply: mem_set; exact hx.
    by rewrite /v heq.
  have hefun : (fun n=>\sum_(j <- C n) v j)=(fun n=>weighted_generator_sum S [set` C n] u x) by apply: funext.
  by rewrite hefun hvsum in hlim.
have hUA : (\bigcup_n A n)=[set x | t<weighted_generator_sum S G u x].
  apply/seteqP; split.
  - move=> x [n _ hx]; apply: lt_le_trans hx _; apply: nonnegative_sum_subset=> j [hj hxj]; split=> //.
    exact (@finite_exhaustion_subset J G C hC n j hj).
  - move=> x hx; have [N hN] := (hsum x).2.1 t hx; exists N=> //; exact: hN N (leqnn N).
have hlim := hcont A hinc; rewrite hUA in hlim.
apply: (@extended_order_limit_upper_bound R _ _ B hlim.2)=> n; apply: hfinite.
by move=> j hj; exact (@finite_exhaustion_subset J G C hC n j hj).
Qed.
