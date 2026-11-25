(** Federer (1969), 3.2.7, p. 246:
    in the first example, infinite multiplicity removes
    the nonmeasurable information in a strictly positive
    real weight, and the target integral is infinity. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ScalarAbsoluteContinuousArea
  MappingMultiplicity PartialFunctionUP PartialFunctionBasic CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureExtendedCharacteristicIntegral
  LebesgueScalarMeasure IntervalBumpFunctions TopologicalBorel BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_weight_infinite_multiplicity_integral]:
    the right integral equals infinity in the first
    example of Federer 3.2.7, p. 246.
    The two fibre-count hypotheses are helper facts
    proved for the sine separately. No measurability
    of g is assumed or needed after multiplication. *)
Theorem positive_weight_infinite_multiplicity_integral (R:realType) (f g:R->R):
  (forall y,(-1<=y)%R -> (y<=1)%R ->
    @mapping_multiplicity R [the choiceType of real_line_metric R] R f setT y=(+oo : \bar R)%E) ->
  (forall y,~(`[(-1)%R,1%R]:set (real_line_metric R)) y ->
    @mapping_multiplicity R [the choiceType of real_line_metric R] R f setT y=0%E) ->
  (forall y,(-1<=y)%R -> (y<=1)%R -> (0<g y)%R) ->
  is_measure_integral (@lebesgue_scalar_measure R)
    (scalar_curve_area_target_integrand f setT g) (+oo)%E.
Proof.
move=>hInf hZero hPos; have hm:=lebesgue_scalar_is_measure R.
pose I:=(`[(-1)%R,1%R]:set (real_line_metric R)).
pose chi:=@CharacteristicFunction.value R [the choiceType of real_line_metric R] I.
have hChi:is_characteristic_function I chi:=@CharacteristicFunction.laws R [the choiceType of real_line_metric R] I.
have hI:measure_measurable (@lebesgue_scalar_measure R) I.
  exact (borel_regular_borel_measurable hm (lebesgue_scalar_borel_regular R)
    (closed_borel_set (@segment_closed_real R (-1) 1))).
have hMass:lebesgue_scalar_measure I=(2:R)%:E.
  rewrite /I lebesgue_scalar_segment; first by congr (_%:E); lra.
  lra.
have hi:=@measure_nonnegative_extended_characteristic_integral R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) hm I chi (+oo)%E hChi hI le0y.
have hMassPos:(0%E<lebesgue_scalar_measure I)%E by rewrite hMass lte_fin ltr0n.
rewrite (gt0_mulye hMassPos) in hi.
apply:(measure_integral_graph_equivalent _ hi)=>y z.
change (((+oo)%E * (chi y)%:E)%E=z <->
  (((g y)%:E * @mapping_multiplicity R [the choiceType of real_line_metric R] R f setT y)%E=z)).
case:(pselect (I y))=>hy.
- have hy':=hy; move:hy'; rewrite /I /= in_itv /= =>/andP[hyl hyu].
  have hg:(0%E<(g y)%:E)%E by rewrite lte_fin; exact:hPos.
  by rewrite (characteristic_on_set hChi hy) mule1 (hInf y hyl hyu) (gt0_muley hg).
- by rewrite (characteristic_off_set hChi hy) mule0 (hZero y hy) mule0.
Qed.
