(** Federer (1969), 2.6.2, p. 116: a set of finite product measure has an
    enclosing P2 set W whose product measure and repeated integral equal the
    original measure. The existing prefix-intersection identity from the
    earlier 2.5.3 development is reused as set-theoretic infrastructure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealReciprocalBounds PartialFunctionBasic
  MeasureUP MeasureBasic MeasureCountableClosure MeasureIntegralUP NonnegativeSum
  ProductMeasure ProductMeasureSequenceInfimum ProductCoverApproximation ProductRectangleHullUP ProductSections
  CountableRectangleUnionUP CountableRectangleIntersections DecreasingRectangleFubini FunctionLatticePrefixHulls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_finite_repeated_integral_hull]: direct
    finite-measure enclosing-set assertion in Federer 2.6.2, p. 116 The hull
    has measurable sections at every point, lies in P2, and its repeated
    integral is the actual product measure. *)
Theorem product_finite_repeated_integral_hull (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  product_measure ha hb S < +oo ->
  exists W, S `<=` W /\ is_countable_rectangle_intersection alpha beta W /\
    product_measure ha hb W = product_measure ha hb S /\
    (forall x, measure_measurable beta (product_vertical_section W x)) /\
    is_measure_integral alpha (partial_function_total (fun x => beta (product_vertical_section W x)))
      (product_measure ha hb W).
Proof.
move=> hfin; pose nu := product_measure ha hb; have hnu := product_measure_is_measure ha hb.
have hnum : nu S \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hnu S)).
pose r := fine (nu S).
have er : nu S = r%:E by rewrite /r fineK.
have hex n : exists (A : nat -> set X) (B : nat -> set Y),
    (forall m, measure_measurable alpha (A m) /\ measure_measurable beta (B m)) /\
    S `<=` (\bigcup_m (A m `*` B m)) /\
    nonnegative_sum setT (fun m => alpha (A m)*beta (B m)) < (r + ((n.+1)%:R)^-1)%:E.
  apply: product_measure_sequence_strict_approximation.
  change (nu S < (r + ((n.+1)%:R)^-1)%:E).
  by rewrite er lte_fin ltrDl invr_gt0 ltr0n.
pose A n := projT1 (cid (hex n)).
pose B n := projT1 (cid (projT2 (cid (hex n)))).
have h n := projT2 (cid (projT2 (cid (hex n)))).
pose U n := \bigcup_m (A n m `*` B n m).
pose V n := \bigcap_(i in [set i | (i <= n)%N]) U i.
have hU n : is_countable_rectangle_union alpha beta (U n).
  exists (A n), (B n); by split; first exact: (h n).1.
have hV n : is_countable_rectangle_union alpha beta (V n).
  elim: n=> [|n IH].
  - have he : V 0%N = U 0%N.
      apply/seteqP; split=> z hz.
      + exact: hz 0%N (leqnn 0%N).
      + move=> i hi; have /eqP ei : i == 0%N by move: hi; rewrite /= leqn0.
        by rewrite ei.
    rewrite he; exact: hU.
  - rewrite /V set_sequence_prefix_intersection_step.
    exact (@countable_rectangle_union_intersection R X Y alpha beta ha hb _ _ IH (hU n.+1)).
have hsub n : S `<=` V n by move=> z hz i hi; exact: (h i).2.1 z hz.
have hdec n m : (n <= m)%N -> V m `<=` V n.
  move=> hnm z hz i hi; exact: hz i (leq_trans hi hnm).
have hbnd n : nu (V n) < (r + ((n.+1)%:R)^-1)%:E.
  apply: le_lt_trans _ (h n).2.2.
  apply: (@product_measure_sequence_cover_bound R X Y alpha beta ha hb (V n) (A n) (B n) (h n).1).
  move=> z hz; exact: hz n (leqnn n).
have hf0 : nu (V 0%N) < +oo := lt_trans (hbnd 0%N) (ltry _).
pose W := \bigcap_n V n.
have hSW : S `<=` W by move=> z hz n _; exact: hsub n z hz.
have hWU : W = \bigcap_n U n.
  apply/seteqP; split=> z hz.
  - move=> n _; exact (hz n Logic.I n (leqnn n)).
  - move=> n _ i hi; exact (hz i Logic.I).
have hP2 : is_countable_rectangle_intersection alpha beta W.
  exists A,B; split; first by move=> n m; exact: (h n).1 m.
  exact: hWU.
have he : nu W = nu S.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite er; apply: extended_real_reciprocal_upper_bound=> n.
    apply: le_trans _ (ltW (hbnd n)); apply: (@measure_mono R (X * Y)%type nu hnu W (V n)).
    move=> z hz; exact: hz n I.
  - exact: (@measure_mono R (X * Y)%type nu hnu S W hSW).
exists W; split=> //; split=> //; split=> //; split.
- move=> x; rewrite /W product_vertical_intersection.
  apply: (@measure_measurable_countable_intersection R Y [the choiceType of (nat : Type)] beta hb setT _ (countableP setT))=> n _.
  exact (@countable_rectangle_union_sections_measurable R X Y alpha beta hb (V n) (hV n) x).
- exact (@decreasing_rectangle_union_vertical_integral R X Y alpha beta ha hb V hV hdec hf0).
Qed.
