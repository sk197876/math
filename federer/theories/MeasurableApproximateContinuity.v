(** Federer (1969), 2.9.13, p. 159: measurability and almost-everywhere
    approximate continuity. The erratum p. 3, book p. 159 line 19, corrects
    the order of the pair to (phi,V). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialContinuityUP MeasureUP MeasureSplit
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP BorelRegularMeasureUP TopologicalBorel
  MeasureDerivationContext DerivationCountableMeasurability LusinMetric LusinClosedExhaustion
  MeasureDensityPoints DensityMeasurableSets MeasureApproximateLimitUP
  ApproximateContinuityPiece ApproximateContinuityMeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_almost_approximately_continuous]: direct forward
    direction of Federer 2.9.13, p. 159 Lusin's theorem gives countably many
    closed continuity pieces covering almost all of X. Apply 2.9.11
    simultaneously to their complements and use relative continuity at the
    resulting density points. *)
Theorem measurable_almost_approximately_continuous (R : realType) (X Y : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (D : set Y)
    (f : partial_function X Y) :
  is_measure_derivation_context phi V -> countable D -> dense D ->
  is_measure_measurable_function phi f ->
  measure_almost_everywhere phi [set x | is_measure_approximately_continuous_at phi V f x].
Proof.
move=> hc hDc hDd hf; have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
have hr := derivation_measure_borel_regular hphi.
have hcnt := @derivation_measure_measurable_countably_measurable R X phi setT
  hphi (measure_measurable_whole hm).
have happ (A : set X) (hA : measure_measurable phi A)
    (hfin : phi A < +oo) (e : R) (he : (0<e)%R) : exists C, closed C /\ C `<=` A /\
    phi (A `\` C)<e%:E /\ partial_function_continuous_on C f.
  exact (@lusin_borel_regular R X Y phi hm hr D A f e hDc hDd hf hA hfin he).
have [C [hclosed [hcont hcover]]] := @lusin_closed_exhaustion R X Y phi hm f hcnt happ.
have hQ j : measure_almost_everywhere phi
    [set x | C j x -> measure_density_complement_zero_points phi V (C j) x].
  have hCm := @borel_regular_borel_measurable R X phi hm hr (C j) (closed_borel_set (hclosed j)).
  have hz := (density_complement_zero_points_conclusions (C j) hc).2.2.2.1 hCm.
  exact: (@measure_almost_everywhere_on_implication R X phi (C j)
    (measure_density_complement_zero_points phi V (C j))).1 hz.
have hall := @measure_almost_everywhere_countable R X (nat*nat)%type phi hm setT
  (fun j => [set x | C j x -> measure_density_complement_zero_points phi V (C j) x])
  (countableP _) (fun j _ => hQ j).
have hboth := measure_almost_everywhere_and hm hcover hall.
apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ hboth)=> x [[j _ hxC] hx].
exact: continuous_piece_approximate_continuity hc (hcont j) hxC (hx j Logic.I hxC).
Qed.

(** Source for [federer_2_9_13]: complete theorem of Federer 2.9.13, p. 159
    A countable dense subset expresses separability. The original
    conull-domain hypothesis is retained explicitly. The erratum p. 3, book
    p. 159 line 19, fixes the pair to (phi,V). *)
Theorem federer_2_9_13 (R : realType) (X Y : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (D : set Y)
    (f : partial_function X Y) :
  is_measure_derivation_context phi V -> countable D -> dense D ->
  measure_almost_everywhere phi (partial_function_domain f) ->
  (is_measure_measurable_function phi f <->
    measure_almost_everywhere phi [set x | is_measure_approximately_continuous_at phi V f x]).
Proof.
move=> hc hDc hDd _; split.
- exact: measurable_almost_approximately_continuous hc hDc hDd.
- exact: almost_approximate_continuity_measurable hc.
Qed.
