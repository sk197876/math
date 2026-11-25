(** Federer (1969), 2.3.8, p. 78: the zero-distance equivalence. Source
    editions and domain convention: PartialDifferenceZeroLocus.v. The
    conull-domain premises are necessary: empty graphs alone have zero gauge
    even on a source of positive measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP PartialFunctionUP PartialNormedArithmetic
  PartialDifferenceZeroLocus MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureGauge MeasureGaugeComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_null_difference_iff_almost_equal]: supporting
    null exceptional-set equivalence for Federer 2.3.8, p. 78,
    with the missing-domain exceptions made explicit. *)
Lemma measure_null_difference_iff_almost_equal (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : partial_function X V) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  measure_almost_everywhere mu (partial_function_domain g) ->
  (mu (partial_norm_superlevel N (partial_vector_subtract f g) 0) = 0 <->
    measure_almost_equal mu f g).
Proof.
move=> hf hg; rewrite (partial_difference_positive_locus hN).
pose D := partial_function_domain f `&` partial_function_domain g.
have hd : mu (~` D) = 0 := @measure_almost_everywhere_and R X mu hm _ _ hf hg.
split.
- move=> hz; apply: (@measure_null_subset R X mu hm
    _ ((~` D) `|` (D `\` partial_function_agreement f g))).
  + move=> x hn; case: (pselect (D x))=> hx; [right|left]=> //; by split.
  + exact (@measure_null_union R X mu hm _ _ hd hz).
- move=> hz; apply: (@measure_null_subset R X mu hm _ (~` partial_function_agreement f g))=> //.
Qed.

(** Source for [measure_difference_gauge_zero_iff]: direct zero- distance
    assertion in Federer 2.3.8, p. 78 Superlevel measurability is sufficient
    for attainment; conull domains supply actual almost equality. *)
Theorem measure_difference_gauge_zero_iff (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : partial_function X V) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  measure_almost_everywhere mu (partial_function_domain g) ->
  (forall t : R, measure_measurable mu
    (partial_norm_superlevel N (partial_vector_subtract f g) t%:E)) ->
  (measure_gauge mu N (partial_vector_subtract f g) = 0 <-> measure_almost_equal mu f g).
Proof.
move=> hf hg hme; rewrite (@measure_gauge_zero_iff R X V mu hm N _ hme).
exact (@measure_null_difference_iff_almost_equal R X V N hN mu hm f g hf hg).
Qed.
