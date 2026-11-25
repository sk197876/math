(** Federer (1969), 2.10.26, pp. 189–190: compact-source case of the two
    measurability conclusions. Closed fibre-mass sublevels are countable
    intersections of the open finite-cover loci displayed on p. 190. Every
    individual fibre is compact and hence Hausdorff measurable. This compact
    case needs ordinary continuity only and gives Borel sublevels on every
    metric target. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation RealPowerCoverVariants MetricRealPowerCost
  RealHausdorffFibreCutoffs ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  HausdorffMeasure HausdorffClosedCoverAgreement HausdorffFibreCutoffs CompactRealFibreOpenCovers CompactRealFibreMassLevels
  TopologicalBorel GeneratedBorel BorelRegularMeasureUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableExtendedRationalRays.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_real_fibre_mass_closed_level_borel]:
    direct Borel consequence of the sublevel formula
    and openness assertion in 2.10.26, p. 190.
    Infinite fibre mass is allowed, and t can
    be any real rather than only positive. *)
Theorem compact_real_fibre_mass_closed_level_borel (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) (k : R) (hk : (0<=k)%R) (t : R) :
  continuous f -> compact A ->
  borel_set [set y | real_hausdorff_fibre_mass f A hk y<=t%:E].
Proof.
move=> hf hA; rewrite (compact_real_fibre_mass_closed_level_formula hk t hf hA).
apply: (@borel_set_countable_intersection Y [the choiceType of (nat : Type)] setT _
  (countableP _) (ex_intro _ 0%N Logic.I))=> n _.
apply: open_borel_set; exact: compact_real_fibre_open_cover_locus_open hf hA.
Qed.

(** Source for [compact_real_fibre_mass_measurable_for_borel_measure]:
    supporting general-target form of the first conclusion
    of 2.10.26, pp. 189–190. A measure which
    measures Borel subsets of Y measures the compact
    source's fibre-mass integrand. No finiteness or
    properness hypothesis is needed in this compact case. *)
Theorem compact_real_fibre_mass_measurable_for_borel_measure (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) (k : R) (hk : (0<=k)%R) (mu : set Y -> \bar R) (hMu : is_measure mu) :
  continuous f -> compact A ->
  (forall B, borel_set B -> measure_measurable mu B) ->
  is_measure_measurable_function mu (partial_function_total (real_hausdorff_fibre_mass f A hk)).
Proof.
move=> hf hA hB.
have hd : measure_almost_everywhere mu (partial_function_domain
    (partial_function_total (real_hausdorff_fibre_mass f A hk))).
  rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hMu.
apply/(measurable_extended_rational_closed_lower_rays_iff hMu hd)=> q.
rewrite partial_function_total_preimage; apply: hB.
exact: compact_real_fibre_mass_closed_level_borel hf hA.
Qed.

(** Source for [compact_real_hausdorff_fibre_mass_measurable]:
    direct compact-source case of the first conclusion
    of 2.10.26, pp. 189–190, for the actual
    target Hausdorff measure. Both degrees range over all nonnegative reals with the actual
    Gamma normalization. *)
Corollary compact_real_hausdorff_fibre_mass_measurable (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) :
  continuous f -> compact A ->
  is_measure_measurable_function (@real_hausdorff_measure R Y m hm)
    (partial_function_total (real_hausdorff_fibre_mass f A hk)).
Proof.
move=> hf hA.
apply: compact_real_fibre_mass_measurable_for_borel_measure (@real_hausdorff_measure_is_measure R Y m hm) hf hA _.
exact: borel_regular_borel_measurable (@real_hausdorff_measure_is_measure R Y m hm)
  (@real_hausdorff_measure_borel_regular R Y m hm).
Qed.

(** Source for [compact_real_hausdorff_fibres_measurable]:
    compact-source case of the second conclusion of
    2.10.26, pp. 189–190. Every fibre is
    compact and therefore measurable, which strengthens
    the printed almost-everywhere conclusion in this case. *)
Theorem compact_real_hausdorff_fibres_measurable (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) (k : R) (hk : (0<=k)%R) :
  continuous f -> compact A -> forall y,
  measure_measurable (@real_hausdorff_measure R X k hk) (A `&` f @^-1` [set y]).
Proof.
move=> hf hA y.
have hpre : closed (f @^-1` [set y]).
  exact: (continuous_closedP f).1 hf _ (compact_closed (@metric_hausdorff R Y) (@compact_set1 Y y)).
apply: (@borel_regular_borel_measurable R X (@real_hausdorff_measure R X k hk)
  (@real_hausdorff_measure_is_measure R X k hk) (@real_hausdorff_measure_borel_regular R X k hk)).
apply: closed_borel_set.
exact: compact_closed (@metric_hausdorff R X) (compact_closedI hA hpre).
Qed.
