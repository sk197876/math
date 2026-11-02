(** Federer (1969), 2.10.24, pp. 186–187: supporting assembly of countably
    many increasingly fine weighted covers into one admissible cover. Group
    occurrences of each original generator. Infinite aggregate weights have
    zero diameter and zero cost, so their countable union has zero actual
    final measure and can be removed. All remaining weights are proved
    finite real numbers, as the book requires. This is a proof expansion of
    the infimum/upper-integral comparison, not an extension of the weight
    domain. Source context: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import WeightedMetricEnvelopeUP WeightedRepeatedGenerators WeightedCoverReindexing
  CaratheodoryNullGenerators CaratheodoryLimitUP CaratheodoryLimitMeasure MetricDiameter
  MeasureUP MeasureAlmostUP MeasureAlmostBasic NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [fine_weighted_cover_assembly]: supporting
    weighted cover construction for the upper-integral
    comparison in 2.10.24, p. 187. The
    total source cost must be finite; no final
    mass finiteness, generator measurability or weight
    positivity away from zero is assumed. *)
Theorem fine_weighted_cover_assembly (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (delta : \bar R) (f : X -> \bar R) (G : nat -> set J) (a : nat -> J -> R) :
  is_caratheodory_limit S c psi -> (forall j, 0<=c j) ->
  (forall n, countable (G n)) -> (forall n j, G n j -> (0<=a n j)%R) ->
  (forall n j, G n j -> extended_metric_diameter (S j)<=delta) ->
  (forall e : R, (0<e)%R -> exists N, forall n j, (N<=n)%N -> G n j -> extended_metric_diameter (S j)<=e%:E) ->
  nonnegative_sum setT (fun n=>weighted_generator_cost c (G n) (a n))< +oo ->
  measure_almost_everywhere psi [set x | f x<=nonnegative_sum setT (fun n=>weighted_generator_sum S (G n) (a n) x)] ->
  exists H u, is_weighted_metric_cover S psi delta f H u /\
    weighted_generator_cost c H u<=nonnegative_sum setT (fun n=>weighted_generator_cost c (G n) (a n)).
Proof.
move=> hpsi hc hG ha hdiam hfine hfinite hdom.
have hm := caratheodory_limit_is_measure hpsi hc.
pose sigma j := repeated_generator_weight G a j.
pose U := \bigcup_n G n.
pose B := U `&` [set j | sigma j=+oo].
pose H := U `&` [set j | sigma j< +oo].
pose u j := fine (sigma j).
have hU : countable U := bigcup_countable (countableP setT) (fun n _=>hG n).
have hB : countable B := sub_countable (subset_card_le (fun j (hj : B j)=>hj.1)) hU.
have hH : countable H := sub_countable (subset_card_le (fun j (hj : H j)=>hj.1)) hU.
have hs0 j : 0<=sigma j := nonnegative_sum_nonnegative _ _.
have hreal j (hj : H j) : sigma j=(u j)%:E.
  have hh : sigma j \is a fin_num by rewrite (ge0_fin_numE (hs0 j)); exact hj.2.
  by rewrite /u fineK.
have hu0 j (hj : H j) : (0<=u j)%R by have hh := hs0 j; rewrite (hreal j hj) lee_fin in hh.
have hbad j (hj : B j) : extended_metric_diameter (S j)=0 /\ c j=0.
  split.
  - exact: (@infinite_repeated_weight_zero_diameter R X J S G a j hfine hj.2).
  - exact: (@infinite_repeated_weight_zero_cost R J G a c j ha hc hfinite hj.2).
pose Z := \bigcup_(j in B) S j.
have hZ : psi Z=0 := caratheodory_countable_zero_diameter_null hpsi hc hB hbad.
have hoff : measure_almost_everywhere psi (~` Z) by rewrite /measure_almost_everywhere setCK.
have hpoint x (hxZ : ~Z x) : weighted_generator_sum S H u x=
    nonnegative_sum setT (fun n=>weighted_generator_sum S (G n) (a n) x).
  rewrite (weighted_cover_point_reindexing S x ha).
  pose A := [set j | S j x].
  have hnull : nonnegative_sum (A `\` H) sigma=0.
    apply: nonnegative_sum_zero=> j [hjx hjH].
    case: (pselect (U j))=> [hjU|hjU].
    - have hinf : sigma j=+oo.
        apply/eqP; rewrite eq_le leey /= leNgt; apply/negP=> hfin; apply: hjH; by split.
      exfalso; apply: hxZ; exists j=> //; by split.
    - apply: nonnegative_sum_zero=> n hn.
      exfalso; apply: hjU; by exists n.
  have hsplit := @nonnegative_sum_split R J A H sigma (fun j _=>hs0 j).
  rewrite hnull adde0 setIC in hsplit.
  rewrite /weighted_generator_sum hsplit.
  apply: nonnegative_sum_ext=> j [hjH hjx]; exact: esym (hreal j hjH).
have hcover : is_weighted_metric_cover S psi delta f H u.
  constructor.
  - exact hH.
  - exact hu0.
  - move=> j [[n _ hnj] _]; exact: hdiam n j hnj.
  - apply: (@measure_almost_everywhere_mono R X psi hm _ _ _ (measure_almost_everywhere_and hm hdom hoff)).
    move=> x [hx hxZ]; change (is_true (f x<=weighted_generator_sum S H u x)).
    rewrite (hpoint x hxZ); exact hx.
exists H,u; split=> //.
have heq : weighted_generator_cost c H u=nonnegative_sum H (fun j=>sigma j*c j).
  apply: nonnegative_sum_ext=> j hj; by rewrite (hreal j hj).
rewrite heq (weighted_cover_cost_reindexing ha hc).
apply: nonnegative_sum_subset=> j hj; exact Logic.I.
Qed.
