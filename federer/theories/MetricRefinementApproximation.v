(** Federer (1969), 2.10.1, p. 170, alternative open-cover formula. The
    corrected reference is [F12], Federer, On Lebesgue area (1955) Follow
    the measurable-partition and summable-error proof there, using the
    reciprocal-radius layers of MetricOpenCoverLayers.v. No separability
    hypothesis is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import NonnegativeSum NonnegativeSumAdd NonnegativeSumCover
  NonnegativeSumSupport GeometricErrorBudget MetricDiameter MetricScaleEnvelope
  MetricScaleEnvelopeUP MetricScaleApproximation CaratheodoryLimitUP
  CaratheodoryLimitMeasure CaratheodoryMetricMeasure MetricOpenCoverLayers
  OpenRefinementBoundUP SetSequenceDisjointification MeasureUP MeasureBasic
  MeasureSequencePrefixes MeasureDisjointIntersectionSum ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_open_refining_cover_approximation]: direct
    cover-construction direction of the alternative formula in
    Federer 2.10.1, p. 170, corrected reference Federer1955
    Theorem 2.5, pp. 291–292. Split A by disjoint
    measurable open-cover layers, choose a sufficiently fine
    cover of each part with a geometric error, and unite
    the retained generators meeting their parts. The sum is
    at most mu(A)+epsilon/2, leaving strict-error room. *)
Theorem metric_open_refining_cover_approximation (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) (A : set X) (M e : R) (H : set (set X)) :
  is_caratheodory_limit S cost mu -> (forall j, 0<=cost j) ->
  mu A=M%:E -> (0<e)%R -> (forall U, H U -> open U) ->
  A `<=` \bigcup_(U in H) U ->
  exists G : set J, countable G /\ A `<=` \bigcup_(j in G) S j /\
    (forall j, G j -> exists U, H U /\ S j `<=` U) /\
    nonnegative_sum G cost<=mu A+(e/2)%:E.
Proof.
move=> hmu hc hM he hopen hcover.
have hm := caratheodory_limit_is_measure hmu hc.
pose V := metric_open_cover_layer H.
pose C := set_sequence_disjointify V.
pose B n := C n `&` A.
have hVm n : measure_measurable mu (V n).
  exact (@caratheodory_limit_open_measurable R X J S cost mu hmu hc
    (V n) (@metric_open_cover_layer_open R X H n)).
have hCm n : measure_measurable mu (C n).
  exact (@measure_sequence_disjointify_measurable R X mu hm V hVm n).
have hAll : A `<=` \bigcup_n C n.
  rewrite /C set_sequence_disjointify_union.
  exact: metric_open_cover_layers_cover hopen hcover.
have hUnion : ((\bigcup_n C n) `&` A)=A.
  apply/seteqP; split=> x; [by move=> [_ hx]|move=> hx; split=> //; exact: hAll].
have hsum : nonnegative_sum setT (fun n => mu (B n))=mu A.
  have hsplit := @measure_disjoint_union_intersection_sum R X mu C hm hCm
    (@set_sequence_disjointify_disjoint X V) A.
  by rewrite hUnion in hsplit.
pose d n : R := ((n.+1%:R)^-1)%R.
have hd n : 0<(d n)%:E by rewrite /d lte_fin invr_gt0 ltr0n.
have hBbound n : mu (B n)<=mu A.
  exact (@measure_mono R X mu hm (B n) A (fun x hx => hx.2)).
have hBfin n : mu (B n) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm (B n))).
  apply: le_lt_trans (hBbound n) _; by rewrite hM ltry.
have hex n : exists G : set J, countable G /\
    (forall j, G j -> extended_metric_diameter (S j)<=(d n)%:E) /\
    B n `<=` \bigcup_(j in G) S j /\
    nonnegative_sum G cost<mu (B n)+(geometric_error_budget e n)%:E.
  have hn := metric_scale_envelope_specification S cost (d n)%:E.
  have hle := @caratheodory_limit_upper R X J S cost mu hmu (B n) (d n)%:E _ (hd n) hn.
  apply: (@metric_scale_envelope_approximation R X J S cost (d n)%:E _ (B n) _ hn).
  apply: le_lt_trans hle _.
  rewrite -(fineK (hBfin n)) -EFinD lte_fin ltrDl.
  exact: geometric_error_budget_positive.
pose Q n := projT1 (cid (hex n)).
have hQ n := projT2 (cid (hex n)).
pose G n := Q n `&` [set j | exists x, B n x /\ S j x].
have hGc n : countable (G n).
  apply: (sub_countable _ (hQ n).1).
  apply: subset_card_le=> j hj; exact: hj.1.
have hGcover n : B n `<=` \bigcup_(j in G n) S j.
  move=> x hx; have [j hj hs] := (hQ n).2.2.1 x hx.
  exists j=> //; split=> //; by exists x.
have hGref n j : G n j -> exists U, H U /\ S j `<=` U.
  move=> [hj [x [[hx _] hs]]].
  apply: (@metric_open_cover_layer_refinement R X H n (S j) ((hQ n).2.1 j hj)).
  exists x; split=> //; exact: hx.1.
have hGsum n : nonnegative_sum (G n) cost<=mu (B n)+(geometric_error_budget e n)%:E.
  apply: le_trans _ (ltW (hQ n).2.2.2).
  apply: nonnegative_sum_subset=> j hj; exact: hj.1.
pose U := \bigcup_n G n.
have hUc : countable U.
  apply: bigcup_countable (countableP setT) _=> n _; exact: hGc.
have hUA : A `<=` \bigcup_(j in U) S j.
  move=> x hx; have [n _ hxn] := hAll x hx.
  have [j hj hs] := hGcover n x (conj hxn hx).
  exists j=> //; by exists n.
exists U; split=> //; split=> //; split.
- move=> j [n _ hj]; exact: hGref n j hj.
- have hcoverU : U `<=` \bigcup_n G n by [].
  apply: le_trans (@nonnegative_sum_cover R J nat U setT G cost hc hcoverU) _.
  apply: le_trans (@nonnegative_sum_mono R nat setT _ _ (fun n _ => hGsum n)) _.
  have herror n (_ : setT n) : 0<=(geometric_error_budget e n)%:E.
    rewrite lee_fin; exact: ltW (geometric_error_budget_positive n he).
  rewrite (@nonnegative_sum_add R nat setT (fun n => mu (B n))
    (fun n => (geometric_error_budget e n)%:E)
    (fun n _ => measure_nonnegative hm (B n)) herror) hsum.
  exact: leeD (lexx _) (geometric_error_sum_bound he).
Qed.

(** Source for [metric_caratheodory_open_refinement_bound]: direct
    strict-threshold direction of the alternative characterisation
    in Federer 2.10.1, p. 170, corrected reference
    Federer1955 Theorem 2.5, pp. 291–292. Every threshold
    strictly above mu(A) admits a refined countable cover for
    every open cover of A, even if A is not measurable. *)
Theorem metric_caratheodory_open_refinement_bound (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) (A : set X) (t : \bar R) :
  is_caratheodory_limit S cost mu -> (forall j, 0<=cost j) -> mu A<t ->
  is_open_refinement_bound S cost A t.
Proof.
move=> hmu hc ht H hopen hcover.
have hm := caratheodory_limit_is_measure hmu hc.
have hfin : mu A \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm A)); exact: lt_le_trans ht (leey _).
pose M := fine (mu A).
have hM : mu A=M%:E by rewrite /M fineK.
have [q [hMq hqt]] := @extended_rationals_order_dense R (mu A) t ht.
pose e : R := ((ratr q : R)-M)%R.
have he : (0<e)%R by rewrite /e subr_gt0; move: hMq; rewrite hM lte_fin.
have [G [hG [hcov [href hb]]]] := @metric_open_refining_cover_approximation R X J S cost mu
  A M e H hmu hc hM he hopen hcover.
exists G; split=> //; split=> //; split=> //.
apply: le_lt_trans hb _; apply: lt_trans _ hqt.
rewrite hM -EFinD lte_fin.
have hEq : (M+e=(ratr q : R))%R by rewrite /e addrCA subrr addr0.
have hh : (M+e/2<(ratr q : R))%R.
  rewrite -hEq ltrD2l ltr_pdivrMr ?ltr0n //.
  by rewrite -{1}[e]mulr1 (ltr_pM2l he) ltr1n.
exact hh.
Qed.
