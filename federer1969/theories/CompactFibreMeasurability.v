(** Federer (1969), 2.10.26, pp. 189–190: compact-source case of the two
    measurability conclusions. Closed fibre-mass sublevels are countable
    intersections of the open finite-cover loci displayed on p. 190. Every
    individual fibre is compact and hence Hausdorff measurable. This compact
    case needs ordinary continuity only and gives Borel sublevels on every
    metric target. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  HausdorffMeasure HausdorffClosedCoverAgreement HausdorffFibreCutoffs CompactFibreOpenCovers CompactFibreMassLevels
  TopologicalBorel GeneratedBorel BorelRegularMeasureUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableExtendedRationalRays.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_fibre_mass_closed_level_borel]:
    direct Borel consequence of the sublevel formula
    and openness assertion in 2.10.26, p. 190.
    Infinite fibre mass is allowed, and t can
    be any real rather than only positive. *)
Theorem compact_fibre_mass_closed_level_borel (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) k (t : R) :
  continuous f -> compact A ->
  borel_set [set y | hausdorff_fibre_mass f A k y<=t%:E].
Proof.
move=> hf hA; rewrite (compact_fibre_mass_closed_level_formula k t hf hA).
apply: (@borel_set_countable_intersection Y [the choiceType of (nat : Type)] setT _
  (countableP _) (ex_intro _ 0%N Logic.I))=> n _.
apply: open_borel_set; exact: compact_fibre_open_cover_locus_open hf hA.
Qed.

(** Source for [compact_fibre_mass_measurable_for_borel_measure]:
    supporting general-target form of the first conclusion
    of 2.10.26, pp. 189–190. A measure which
    measures Borel subsets of Y measures the compact
    source's fibre-mass integrand. No finiteness or
    properness hypothesis is needed in this compact case. *)
Theorem compact_fibre_mass_measurable_for_borel_measure (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) k (mu : set Y -> \bar R) (hm : is_measure mu) :
  continuous f -> compact A ->
  (forall B, borel_set B -> measure_measurable mu B) ->
  is_measure_measurable_function mu (partial_function_total (hausdorff_fibre_mass f A k)).
Proof.
move=> hf hA hB.
have hd : measure_almost_everywhere mu (partial_function_domain
    (partial_function_total (hausdorff_fibre_mass f A k))).
  rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
apply/(measurable_extended_rational_closed_lower_rays_iff hm hd)=> q.
rewrite partial_function_total_preimage; apply: hB.
exact: compact_fibre_mass_closed_level_borel hf hA.
Qed.

(** Source for [compact_hausdorff_fibre_mass_measurable]:
    direct compact-source case of the first conclusion
    of 2.10.26, pp. 189–190, for the actual
    target Hausdorff measure. Natural degrees retain
    the existing integer-degree scope. *)
Corollary compact_hausdorff_fibre_mass_measurable (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) k m :
  continuous f -> compact A ->
  is_measure_measurable_function (@hausdorff_measure R Y m)
    (partial_function_total (hausdorff_fibre_mass f A k)).
Proof.
move=> hf hA.
apply: compact_fibre_mass_measurable_for_borel_measure (@hausdorff_measure_is_measure R Y m) hf hA _.
exact: borel_regular_borel_measurable (@hausdorff_measure_is_measure R Y m)
  (@hausdorff_measure_borel_regular R Y m).
Qed.

(** Source for [compact_hausdorff_fibres_measurable]:
    compact-source case of the second conclusion of
    2.10.26, pp. 189–190. Every fibre is
    compact and therefore measurable, which strengthens
    the printed almost-everywhere conclusion in this case. *)
Theorem compact_hausdorff_fibres_measurable (R : realType) (X Y : metricType R)
    (f : X -> Y) (A : set X) k :
  continuous f -> compact A -> forall y,
  measure_measurable (@hausdorff_measure R X k) (A `&` f @^-1` [set y]).
Proof.
move=> hf hA y.
have hpre : closed (f @^-1` [set y]).
  exact: (continuous_closedP f).1 hf _ (compact_closed (@metric_hausdorff R Y) (@compact_set1 Y y)).
apply: (@borel_regular_borel_measurable R X (@hausdorff_measure R X k)
  (@hausdorff_measure_is_measure R X k) (@hausdorff_measure_borel_regular R X k)).
apply: closed_borel_set.
exact: compact_closed (@metric_hausdorff R X) (compact_closedI hA hpre).
Qed.
