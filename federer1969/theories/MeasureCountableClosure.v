(** Federer (1969), 2.1.3(2), pp. 55-56: countable closure of measurable
    sets. The proof uses the same finite unions and restrictions as Federer.
    It passes their splitting bounds to the numerical sum directly; this
    avoids first proving continuity from above. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumAdd
  NonnegativeSumContinuity MeasureUP MeasureBasic MeasureSplit
  MeasureRestriction MeasureFiniteClosure MeasureCountableAdditivity
  SetSequenceDisjointification MeasureSequencePrefixes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_measurable_sequence_union]: Federer
    2.1.3(2), proof p. 56; measurable finite unions exhaust the
    sequence union, and restriction to the arbitrary test set yields
    its splitting equality. Here the limiting step is expressed by
    finite-subsum bounds, valid also for tests of infinite measure. *)
Theorem measure_measurable_sequence_union (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (F : nat -> set I) :
  (forall n, measure_measurable mu (F n)) ->
  measure_measurable mu (\bigcup_n F n).
Proof.
move=> hF T; apply/eqP; rewrite eq_le (measure_split_upper hm) /=.
pose nu := measure_restrict mu T.
have hn : is_measure nu := measure_restrict_is_measure hm T.
have hFn : forall n, measure_measurable nu (F n).
  move=> n; exact: measure_restrict_measurable (hF n).
have hD : forall n, measure_measurable nu (set_sequence_disjointify F n).
  exact: (@measure_sequence_disjointify_measurable R I nu hn F hFn).
have hs := @measure_sequence_disjoint_additivity R I nu hn
  (set_sequence_disjointify F) hD (@set_sequence_disjointify_disjoint I F).
rewrite set_sequence_disjointify_union in hs.
change (nu (\bigcup_n F n) + mu (T `\` \bigcup_n F n) <= mu T).
rewrite hs; apply: nonnegative_sum_add_bound; first exact: (@measure_nonnegative R I mu hm).
move=> C _.
have [N hN] : exists N, forall k, k \in C -> (k < N)%N.
  apply: (@finite_increasing_cover _ (fun n => [set k | (k < n)%N]) C).
  - move=> n m hnm k hk; exact: leq_trans hk hnm.
  - move=> k _; exists k.+1; exact: ltnSn.
have hb := @nonnegative_sum_upper R _ [set k | (k < N)%N]
  (fun k => nu (set_sequence_disjointify F k)) C hN.
rewrite -(@measure_sequence_disjointify_prefix_sum R I nu hn F hFn N) in hb.
have hc : mu (T `\` \bigcup_n F n) <= mu (T `\` set_sequence_prefix F N).
  apply: (@measure_mono R I mu hm _ _)=> x [ht hu]; split=> //.
  move=> [k hk hx]; apply: hu; by exists k.
have hsplit := (@measure_sequence_prefix_measurable R I mu hm F hF N T).
rewrite /measure_restrict /nu in hb.
rewrite hsplit; exact: leeD hb hc.
Qed.

(** Source for [measure_measurable_countable_union]: Federer
    2.1.3(2), pp. 55-56; the countable-family formulation. The empty
    family is also allowed, since its union is empty. A countable
    injection into the naturals gives a sequence with empty gaps. *)
Theorem measure_measurable_countable_union (R : realType) (I J : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (D : set J) (F : J -> set I) :
  countable D -> (forall j, D j -> measure_measurable mu (F j)) ->
  measure_measurable mu (\bigcup_(j in D) F j).
Proof.
move=> /countable_injP[g hg] hF.
pose G n := \bigcup_(j in D `&` [set j | g j == n]) F j.
have hG : forall n, measure_measurable mu (G n).
  move=> n; case: (pselect (exists j, D j /\ g j == n))=> [[j [hj hjn]]|hn].
  - have he : G n = F j.
      apply/seteqP; split.
      + move=> x [k [hk hkn] hx].
        have hkj : k = j.
          apply: hg; [exact: mem_set hk | exact: mem_set hj |].
          by move/eqP: hkn=> ->; move/eqP: hjn=> ->.
        by rewrite -hkj.
      + move=> x hx; exists j=> //; by split.
    rewrite he; exact: hF.
  - have he : G n = set0.
      apply/seteqP; split=> [x [j [hj hjn] _]|x []].
      exfalso; apply: hn; by exists j.
    rewrite he; exact: measure_measurable_empty hm.
have he : (\bigcup_n G n) = \bigcup_(j in D) F j.
  apply/seteqP; split.
  - move=> x [n _ [j [hj _] hx]]; by exists j.
  - move=> x [j hj hx]; exists (g j)=> //; exists j=> //; split=> //; exact: eqxx.
rewrite -he; exact: (@measure_measurable_sequence_union R I mu hm G hG).
Qed.

(** Source for [measure_measurable_countable_intersection]: Federer
    2.1.3(2), pp. 55-56; countable intersections, by complements.
    The empty-family case is included with intersection equal to X,
    strengthening the book's stated nonempty-family convention. *)
Theorem measure_measurable_countable_intersection (R : realType) (I J : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (D : set J) (F : J -> set I) :
  countable D -> (forall j, D j -> measure_measurable mu (F j)) ->
  measure_measurable mu (\bigcap_(j in D) F j).
Proof.
move=> hD hF.
have hC : forall j, D j -> measure_measurable mu (~` F j).
  move=> j hj; exact: measure_measurable_complement (hF j hj).
have hu := @measure_measurable_countable_union R I J mu hm D (fun j => ~` F j) hD hC.
have hc := measure_measurable_complement hu.
move: hc; rewrite setC_bigcup.
under eq_bigcapr do rewrite setCK.
by [].
Qed.
