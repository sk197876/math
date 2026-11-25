(** Federer (1969), 2.10.24, pp. 186–188: supporting Borel level sets of
    weighted Borel covering sums, needed in the final-paragraph application
    of 2.10.8, p. 175. Finite sums split into Borel cells; a countable
    finite exhaustion gives strict superlevels as countable unions. Rational
    order density gives closed superlevels. These are applications of 2.2.1,
    pp. 59–60, and 2.3.2(2), p. 73, not extra geometric claims attributed to
    the book. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import TopologicalBorel BorelFamilyBasic
  WeightedMetricEnvelopeUP FiniteWeightedGeneratorSums NonnegativeSum NonnegativeSumSupport
  NonnegativeSumRestriction CountableFiniteExhaustionUP CountableFiniteExhaustionSealed
  FiniteExhaustionSumLimit ExtendedRealOrderLimit ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_weighted_borel_strict_level]: supporting
    finite Borel-cell computation for the weighted sums
    in 2.10.24, p. 186. Indices in the sequence
    may repeat and the scalar weights may be arbitrary
    finite real numbers in this finite lemma. *)
Lemma finite_weighted_borel_strict_level (R : realType) (X : topologicalType) (J : choiceType)
    (S : J -> set X) (u : J -> R) (P : seq J) (t : R) :
  (forall j, j \in P -> borel_set (S j)) ->
  borel_set [set x | (t<\sum_(j <- P) (if x \in S j then u j else 0))%R].
Proof.
elim: P t=> [|j P ih] t hS.
- have hzero : [set x : X | (t<\sum_(j <- [::]) (if x \in S j then u j else 0))%R]=
      [set x : X | (t<0)%R].
    apply/seteqP; split=> x hx.
    * change (is_true (t<0)%R).
      have hh : (t<\sum_(j <- [::]) (if x \in S j then u j else 0))%R := hx.
      by rewrite big_nil in hh.
    * change (is_true (t<\sum_(j <- [::]) (if x \in S j then u j else 0))%R).
      by rewrite big_nil.
  rewrite hzero.
  case ht: (t<0)%R.
  + have he : [set x : X | true]=setT.
      by apply/seteqP; split=> x _.
    rewrite he; exact: open_borel_set openT.
  + have he : [set x : X | false]=set0.
      by apply/seteqP; split=> [x hx|x []].
    rewrite he; exact: open_borel_set open0.
have hSj : borel_set (S j) := hS j (mem_head j P).
have htail k (hk : k \in P) : borel_set (S k) by apply: hS; rewrite in_cons hk orbT.
pose V r := [set x | (r<\sum_(k <- P) (if x \in S k then u k else 0))%R].
have hV r : borel_set (V r) := ih r htail.
have he : [set x | (t<\sum_(k <- j::P) (if x \in S k then u k else 0))%R]=
    (S j `&` V (t-u j)%R) `|` ((~` S j) `&` V t).
  apply/seteqP; split=> x.
  - move=> hx; change (is_true (t<\sum_(k <- j::P) (if x \in S k then u k else 0))%R) in hx.
    case hxS: (x \in S j); rewrite big_cons hxS /= in hx.
    + left; split; first exact: set_mem hxS.
      change (is_true (t-u j<\sum_(k <- P) (if x \in S k then u k else 0))%R); lra.
    + right; split.
      * move=> hxj; by rewrite (mem_set hxj) in hxS.
      * change (is_true (t<\sum_(k <- P) (if x \in S k then u k else 0))%R); by rewrite add0r in hx.
  - move=> [[hxS hx]|[hxS hx]].
    + change (is_true (t-u j<\sum_(k <- P) (if x \in S k then u k else 0))%R) in hx.
      change (is_true (t<\sum_(k <- j::P) (if x \in S k then u k else 0))%R).
      rewrite big_cons (mem_set hxS); lra.
    + have hnx : x \notin S j by apply/negP=> /set_mem hxj; exact: hxS hxj.
      change (is_true (t<\sum_(k <- j::P) (if x \in S k then u k else 0))%R).
      rewrite big_cons (negbTE hnx) add0r; exact hx.
rewrite he; apply: (borel_family_binary_union (borel_sets_family X));
  apply: (borel_family_binary_intersection (borel_sets_family X))=> //.
exact: borel_set_complement hSj.
Qed.

(** Source for [countable_weighted_borel_strict_level]: supporting
    Borel strict superlevels for the countable weighted
    sums in 2.10.24, p. 186. Finite exhaustion and
    the actual increasing numerical-sum limit retain
    possible infinite values and repeated generators. *)
Theorem countable_weighted_borel_strict_level (R : realType) (X : topologicalType) (J : choiceType)
    (S : J -> set X) (G : set J) (u : J -> R) (t : R) :
  countable G -> (forall j, G j -> (0<=u j)%R) -> (forall j, G j -> borel_set (S j)) ->
  borel_set [set x | t%:E<weighted_generator_sum S G u x].
Proof.
move=> hG hu hS.
pose C := @CountableFiniteExhaustion.value J G hG.
have hC := @CountableFiniteExhaustion.laws J G hG.
pose A n := [set x | t%:E<weighted_generator_sum S [set` C n] u x].
have hA n : borel_set (A n).
  have he : A n=[set x | (t<\sum_(j <- C n) (if x \in S j then u j else 0))%R].
    apply/seteqP; split=> x hx.
    - have hh : t%:E<weighted_generator_sum S [set` C n] u x := hx.
      change (is_true (t<\sum_(j <- C n) (if x \in S j then u j else 0))%R).
      by rewrite (@finite_weighted_generator_point_sum R X J S (C n) u x
        (fun j hj=>hu j (finite_exhaustion_subset hC hj))) lte_fin in hh.
    - change (is_true (t%:E<weighted_generator_sum S [set` C n] u x)).
      rewrite (@finite_weighted_generator_point_sum R X J S (C n) u x
        (fun j hj=>hu j (finite_exhaustion_subset hC hj))) lte_fin; exact hx.
  rewrite he; apply: finite_weighted_borel_strict_level=> j hj.
  exact: hS j (finite_exhaustion_subset hC hj).
have hsum x : extended_increases_to (fun n=>weighted_generator_sum S [set` C n] u x)
    (weighted_generator_sum S G u x).
  pose v j := if x \in S j then (u j)%:E else 0.
  have hv j (hj : G j) : 0<=v j.
    rewrite /v; case: ifP=> _; [rewrite lee_fin; exact: hu|exact: lexx].
  have hh := finite_exhaustion_nonnegative_sum_limit hC hv.
  have he n : \sum_(j <- C n) v j=weighted_generator_sum S [set` C n] u x.
    rewrite (@finite_weighted_generator_point_sum R X J S (C n) u x (fun j hj=>hu j (finite_exhaustion_subset hC hj))) /v -sumEFin.
    apply: eq_big_seq=> j hj; by case: ifP.
  have hefull : nonnegative_sum G v=weighted_generator_sum S G u x.
    rewrite /weighted_generator_sum -nonnegative_sum_restrict; apply: nonnegative_sum_ext=> j hj.
    have hi : (j \in [set j | S j x])=(x \in S j).
      apply/idP/idP=> /set_mem hx; apply: mem_set; exact hx.
    by rewrite /v hi.
  have hefun : (fun n=>\sum_(j <- C n) v j)=(fun n=>weighted_generator_sum S [set` C n] u x) by apply: funext.
  by rewrite hefun hefull in hh.
have he : [set x | t%:E<weighted_generator_sum S G u x]=\bigcup_n A n.
  apply/seteqP; split.
  - move=> x hx; have [N hN] := (hsum x).2.1 t%:E hx.
    exists N=> //; exact: hN N (leqnn N).
  - move=> x [n _ hx]; apply: lt_le_trans hx _.
    apply: nonnegative_sum_subset=> j [hj hxj]; split=> //.
    exact: (@finite_exhaustion_subset J G C hC n j hj).
rewrite he; exact: (@borel_set_countable_union X [the choiceType of (nat : Type)] setT A
  (countableP _) (fun n _=>hA n)).
Qed.

(** Source for [countable_weighted_borel_closed_level]: supporting
    Borel closed superlevels for the null-hull argument
    in the final paragraph of 2.10.24, p. 188.
    Rational order density expresses a closed superlevel
    as a nonempty countable intersection of strict ones. *)
Theorem countable_weighted_borel_closed_level (R : realType) (X : topologicalType) (J : choiceType)
    (S : J -> set X) (G : set J) (u : J -> R) (t : R) :
  countable G -> (forall j, G j -> (0<=u j)%R) -> (forall j, G j -> borel_set (S j)) ->
  borel_set [set x | t%:E<=weighted_generator_sum S G u x].
Proof.
move=> hG hu hS.
pose D := [set q : rat | ((ratr q : R)<t)%R].
pose A q := [set x | (ratr q : R)%:E<weighted_generator_sum S G u x].
have he : [set x | t%:E<=weighted_generator_sum S G u x]=\bigcap_(q in D) A q.
  apply/seteqP; split.
  - move=> x hx q hq; apply: lt_le_trans _ hx; rewrite lte_fin; exact hq.
  - move=> x hx; change (is_true (t%:E<=weighted_generator_sum S G u x)).
    rewrite leNgt; apply/negP=> hg.
    have [q [hgq hqt]] := @extended_rationals_order_dense R _ _ hg.
    have hqD : D q by rewrite /D; move: hqt; rewrite lte_fin.
    have hh := lt_trans hgq (hx q hqD); by rewrite ltxx in hh.
rewrite he; apply: (@borel_set_countable_intersection X [the choiceType of (rat : Type)] D A (countableP _) _).
- have [q [_ hqt]] := @extended_rationals_order_dense R -oo t%:E (ltNyr t).
  exists q; move: hqt; by rewrite lte_fin.
- move=> q hq; exact: countable_weighted_borel_strict_level hG hu hS.
Qed.
