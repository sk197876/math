(** Federer (1969), 2.10.24, p. 188, final paragraph: supporting
    metric-measure argument for restricted weighted functionals.
    Sufficiently small generators cannot meet two positively separated sets.
    Split their original index set and finite coefficients, then pass to the
    cutoff supremum. The resulting metric criterion is 2.3.2(9), p. 75. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import WeightedMetricEnvelopeUP WeightedMetricEnvelopeLaws WeightedMetricEnvelope
  WeightedMetricLimitUP WeightedMetricLimitLaws WeightedMetricLimit WeightedRestrictionMeasure
  CaratheodoryLimitUP CaratheodoryLimitMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MetricDiameterUP MetricDiameter NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction
  MeasurableSeparationUP CaratheodoryMetricCriterion MeasurableBorelFamily TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_metric_limit_add_bound]: supporting
    passage to the cutoff supremum after addition of
    a fixed nonnegative extended value for 2.10.24,
    p. 188. This is the weighted analogue of the
    order step in 2.10.1, p. 170; no integral
    equality or measure law is assumed. *)
Lemma weighted_metric_limit_add_bound (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (L : (X -> \bar R) -> \bar R) (f : X -> \bar R) (z b : \bar R) :
  is_weighted_metric_limit S c psi L -> 0<=z ->
  (forall delta lambda, 0<delta -> is_weighted_metric_envelope S c psi delta lambda -> lambda f+z<=b) ->
  L f+z<=b.
Proof.
move=> hL; case: z=> [r| |] hz hb; last by [].
- rewrite -leeBrDr //; apply: (weighted_metric_limit_least hL)=> delta lambda hd hl.
  rewrite leeBrDr //; exact: hb delta lambda hd hl.
- have hl := weighted_metric_envelope_specification S c psi 1.
  have hpos : (0<1 :> \bar R) by [].
  have hbase := hb 1 _ hpos hl.
  have hn := weighted_metric_envelope_nonnegative hl f.
  have hh := leeD hn (lexx (+oo : \bar R)); rewrite add0e in hh.
  exact: le_trans (leey _) (le_trans hh hbase).
Qed.

(** Source for [weighted_restriction_cutoff_separated]: supporting
    disjoint-index splitting for the final paragraph of
    2.10.24, p. 188, following the fine-cover argument
    of 2.10.1, p. 170. The two sets need not
    be measurable and the costs may be infinite. *)
Theorem weighted_restriction_cutoff_separated (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (delta : \bar R) (lambda : (X -> \bar R) -> \bar R)
    (f : X -> \bar R) (A B : set X) (e : R) :
  is_measure psi -> is_weighted_metric_envelope S c psi delta lambda ->
  (forall j, 0<=c j) -> delta<e%:E ->
  (forall x, A x -> forall y, B y -> (e<=mdist x y)%R) ->
  lambda (weighted_function_restriction f A)+lambda (weighted_function_restriction f B)<=
    lambda (weighted_function_restriction f (A `|` B)).
Proof.
move=> hm hl hc hde hsep.
apply: (weighted_metric_envelope_greatest hl)=> G u hcover.
have hu j (hj : G j) : (0<=u j)%R := @weighted_metric_cover_nonnegative R X J S psi delta
  (weighted_function_restriction f (A `|` B)) G u hcover j hj.
have hdiam j (hj : G j) : extended_metric_diameter (S j)<=delta :=
  @weighted_metric_cover_diameter R X J S psi delta (weighted_function_restriction f (A `|` B)) G u hcover j hj.
pose H := [set j | exists x, A x /\ S j x].
have hGA : countable (G `&` H).
  apply: (sub_countable _ (weighted_metric_cover_countable hcover)); apply: subset_card_le=> j [hj _]; exact hj.
have hGB : countable (G `\` H).
  apply: (sub_countable _ (weighted_metric_cover_countable hcover)); apply: subset_card_le=> j [hj _]; exact hj.
have havoid j (hj : G j) y (hy : B y) (hSy : S j y) : ~H j.
  move=> [x [hx hSx]].
  have hp := @metric_diameter_upper R X (S j) (extended_metric_diameter (S j))
    (extended_metric_diameter_specification (S j)) x y hSx hSy.
  have he : e%:E<=(mdist x y)%:E by rewrite lee_fin; exact: hsep x hx y hy.
  have hle : e%:E<=delta := le_trans he (le_trans hp (weighted_metric_cover_diameter hcover hj)).
  by move: hde; rewrite ltNge hle.
have hpointA x (hx : A x) : weighted_generator_sum S (G `&` H) u x=weighted_generator_sum S G u x.
  rewrite /weighted_generator_sum.
  have he : [set j | (G `&` H) j /\ S j x]=[set j | G j /\ S j x].
    apply/seteqP; split=> [j [[hj _] hSj]|j [hj hSj]]; first by split.
    split=> //; split=> //; by exists x.
  by rewrite he.
have hpointB x (hx : B x) : weighted_generator_sum S (G `\` H) u x=weighted_generator_sum S G u x.
  rewrite /weighted_generator_sum.
  have he : [set j | (G `\` H) j /\ S j x]=[set j | G j /\ S j x].
    apply/seteqP; split=> [j [[hj _] hSj]|j [hj hSj]]; first by split.
    split=> //; split=> //; exact: havoid j hj x hx hSj.
  by rewrite he.
have hrestricted (C : set X) (K : set J) :
    countable K -> K `<=` G -> C `<=` (A `|` B) ->
    (forall x, C x -> weighted_generator_sum S K u x=weighted_generator_sum S G u x) ->
    is_weighted_metric_cover S psi delta (weighted_function_restriction f C) K u.
  move=> hK hKG hCU hpoint; constructor.
  - exact hK.
  - move=> j hj; exact: hu j (hKG j hj).
  - move=> j hj; exact: hdiam j (hKG j hj).
  - apply: (@measure_almost_everywhere_mono R X psi hm _ _ _ (weighted_metric_cover_dominates hcover))=> x hx.
    change (is_true (weighted_function_restriction f C x<=weighted_generator_sum S K u x)).
    rewrite /weighted_function_restriction; case hxC: (x \in C); last exact: nonnegative_sum_nonnegative.
    have hxCU := mem_set (hCU x (set_mem hxC)).
    change (is_true (weighted_function_restriction f (A `|` B) x<=weighted_generator_sum S G u x)) in hx.
    rewrite /weighted_function_restriction hxCU in hx.
    by rewrite (hpoint x (set_mem hxC)).
have hAcov := hrestricted A (G `&` H) hGA (fun j hj=>hj.1) (fun x hx=>or_introl hx) hpointA.
have hBcov := hrestricted B (G `\` H) hGB (fun j hj=>hj.1) (fun x hx=>or_intror hx) hpointB.
have hh := leeD (weighted_metric_envelope_lower hl hAcov) (weighted_metric_envelope_lower hl hBcov).
change (is_true (lambda (weighted_function_restriction f A)+lambda (weighted_function_restriction f B)<=
  nonnegative_sum G (fun j=>(u j)%:E*c j))).
rewrite (@nonnegative_sum_split R J G H (fun j=>(u j)%:E*c j))=> // j hj.
apply: mule_ge0; [rewrite lee_fin; exact: hu j hj|exact: hc].
Qed.

(** Source for [weighted_restriction_metric_separated]: supporting
    metric additivity for the auxiliary measure used in
    2.10.24, p. 188. A common smaller cutoff controls
    both restrictions, including infinite limiting values;
    this supplies the premise of 2.3.2(9), p. 75. *)
Theorem weighted_restriction_metric_separated (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (f : X -> \bar R) :
  is_caratheodory_limit S c psi -> (forall j, 0<=c j) ->
  is_metric_separated_measure (weighted_restriction_measure S c psi f).
Proof.
move=> hpsi hc A B [e [he hsep]].
have hm := caratheodory_limit_is_measure hpsi hc.
pose L := weighted_metric_limit S c psi.
have hL := weighted_metric_limit_specification S c psi.
rewrite !weighted_restriction_measureE.
apply: (@weighted_metric_limit_add_bound R X J S c psi L _ _ _ hL
  (weighted_metric_limit_nonnegative hL _))=> delta lambda hd hl.
rewrite addeC.
apply: (@weighted_metric_limit_add_bound R X J S c psi L _ _ _ hL
  (weighted_metric_envelope_nonnegative hl _))=> eta xi heta hxi.
rewrite addeC.
have hh : (0<e/2)%R by rewrite divr_gt0 // ltr0n.
have hhalf : (e/2<e)%R by rewrite ltr_pdivrMr ?ltr0n // mulr_natr ltrDl.
pose theta := Order.min delta (Order.min eta (e/2)%:E).
have ht : 0<theta by rewrite /theta !lt_min hd heta lte_fin hh.
have htd : theta<=delta by rewrite /theta ge_min lexx.
have hte : theta<=eta by rewrite /theta !ge_min lexx orbT.
have hth : theta<=(e/2)%:E by rewrite /theta !ge_min lexx !orbT.
have hsmall : theta<e%:E by apply: le_lt_trans hth _; rewrite lte_fin.
pose tau := weighted_metric_envelope S c psi theta.
have hspec := weighted_metric_envelope_specification S c psi theta.
have hA := @weighted_metric_envelope_antitone_cutoff R X J S c psi theta delta tau lambda hspec hl htd
  (weighted_function_restriction f A).
have hB := @weighted_metric_envelope_antitone_cutoff R X J S c psi theta eta tau xi hspec hxi hte
  (weighted_function_restriction f B).
apply: le_trans (leeD hA hB) _.
apply: le_trans (@weighted_restriction_cutoff_separated R X J S c psi theta tau f A B e
  hm hspec hc hsmall hsep) _.
exact: (@weighted_metric_limit_upper R X J S c psi L hL _ theta tau ht hspec).
Qed.

(** Source for [weighted_restriction_borel_measurable]: supporting
    Borel measurability for the auxiliary measure in the
    final-paragraph argument of 2.10.24, p. 188, by
    the metric criterion 2.3.2(9), p. 75, and Borel
    generation 2.2.1, p. 60. No measurability of the
    original nonnegative input is required. *)
Theorem weighted_restriction_borel_measurable (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (f : X -> \bar R) :
  is_caratheodory_limit S c psi -> (forall j, 0<=c j) -> (forall x, 0<=f x) ->
  forall A, borel_set A -> measure_measurable (weighted_restriction_measure S c psi f) A.
Proof.
move=> hpsi hc hf0.
have hm := weighted_restriction_is_measure hpsi hc hf0.
apply: (@open_measurable_implies_borel_measurable R X _ hm).
apply: (caratheodory_metric_open_measurability_iff hm).2.
exact: weighted_restriction_metric_separated hpsi hc.
Qed.
