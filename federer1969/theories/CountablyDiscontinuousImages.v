(** Supporting the upper-integral formula in Federer (1969), 2.10.14, p.
    177: a curve continuous off a countable set has measurable Borel images
    for H1, even when the target metric space is neither complete nor
    separable. Restrict to the Borel continuity set and apply 2.2.10, p. 65;
    the remaining image is countable. Then use 2.2.13, pp. 69–70, and the
    actual 2.10.10 multiplicity integral. The unrestricted theorem 2.10.14
    still uses the upper integral as corrected in erratum p. 3, book p. 177
    line 23. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealMetricCompleteness RealLineSeparability
  CompleteMetricUP MetricSubsetBackground BVCurveBorel TopologicalBorel BorelFamilyBasic
  SuslinSetUP SuslinContinuousImages SuslinSequenceClosure BorelClosedProjection
  SuslinMeasurability BorelRegularMeasureUP BorelImageCoverCost BorelCaratheodoryMeasure
  BorelMultiplicityIntegral MappingMultiplicity ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countably_discontinuous_borel_image_suslin]: supporting
    image regularity in the finite-jump-budget case of 2.10.14,
    p. 177. Continuous images of the Borel continuity part
    are Suslin; countable exceptional images are Borel and Suslin.
    No completeness or separability of the target is assumed. *)
Theorem countably_discontinuous_borel_image_suslin (R : realType)
    (X Y : metricType R) (g : X -> Y) (D A : set X) :
  is_complete_metric_space X -> (exists E : set X, countable E /\ dense E) ->
  countable D -> (forall x, ~ D x -> g @ x --> g x) ->
  borel_set A -> is_suslin_set R (g @` A).
Proof.
move=> hX hsep hD hc hA.
pose S := A `\` D.
pose C := A `&` D.
have hS : borel_set S := borel_set_difference hA (countable_metric_set_borel hD).
have hC : countable C.
  apply: sub_countable _ hD; apply: subset_card_le; by move=> x [].
pose f (x : metric_subset S) := g (val x).
have hf : continuous f.
  move=> x; apply: continuous_comp _ (hc (val x) (set_valP x).2).
  exact: metric_subset_inclusion_continuous.
have hIm : f @` setT=g @` S.
  apply/seteqP; split=> y.
  - move=> [x _ <-]; exists (val x)=> //; exact: set_valP.
  - move=> [x hx <-]; exists (Sub x (mem_set hx))=> //.
have hGS : is_suslin_set R (g @` S).
  rewrite -hIm; exact: (@continuous_suslin_subspace_image R X Y S f
    hX hsep (metric_borel_suslin hS) (@metric_hausdorff R Y) hf).
have hGCcount : countable (g @` C) := sub_countable (card_image_le g C) hC.
have hGC : is_suslin_set R (g @` C) := metric_borel_suslin (countable_metric_set_borel hGCcount).
have he : g @` A=\bigcup_n (if n==0%N then g @` S else g @` C).
  apply/seteqP; split=> y.
  - move=> [x hx <-]; case: (pselect (D x))=> hxD.
    + exists 1%N=> //=; exists x=> //; by split.
    + exists 0%N=> //=; exists x=> //; by split.
  - move=> [n _]; case: ifP=> hn [x [hx _] <-]; by exists x.
rewrite he; apply: suslin_sequence_union=> n; by case: ifP.
Qed.

(** Source for [countably_discontinuous_multiplicity_integral]: supporting
    actual-integral case of the upper integral in 2.10.14,
    p. 177. When countable discontinuities are proved from
    finite jump budget, 2.10.10 applies and the upper integral
    agrees with its value. Closed-measurable target measures suffice. *)
Theorem countably_discontinuous_multiplicity_integral (R : realType)
    (Y : metricType R) (g : R -> Y) (beta : set Y -> \bar R)
    (D A : set (real_line_metric R)) :
  is_measure beta -> (forall C, closed C -> measure_measurable beta C) ->
  countable D -> (forall x, ~ D x -> g @ x --> g x) -> borel_set A ->
  is_measure_integral beta
    (partial_function_total (fun y => (@mapping_multiplicity R
      [the choiceType of real_line_metric R] Y g A y : extended_real_line R)))
    (@borel_caratheodory_measure R [the metricType R of real_line_metric R]
      (borel_image_cover_cost g beta) A).
Proof.
move=> hb hclosed hD hc hA.
have [E [hE hden]] := real_line_countable_dense R.
apply: (@borel_multiplicity_integral R [the metricType R of real_line_metric R] Y g beta hb E A hE hden _ hA).
move=> B hB; apply: (@suslin_set_measurable R Y beta hb (g @` B) hclosed).
exact: (@countably_discontinuous_borel_image_suslin R [the metricType R of real_line_metric R]
  Y g D B (@real_line_metric_complete R) (ex_intro _ E (conj hE hden)) hD hc hB).
Qed.
