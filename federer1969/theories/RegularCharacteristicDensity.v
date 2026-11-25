(** Federer (1969), 4.1.8, p. 362: the
    measure of the original restricted Euclidean current.
    The characteristic density is exactly the original
    restriction on every set, by 2.4.5, p. 84,
    and 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology MeasureUP MeasureRestriction RegularMeasureUP
  MeasureDensityUP MeasureDensity MeasureSubsetIntegral MeasureIntegralUP MeasureBoundGraphEquivalence
  MeasureCharacteristicRegular CharacteristicFunctionUP CharacteristicFunctionSealed
  RealSubsetIntegralGraph SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [regular_characteristic_density]: the original
    characteristic density of A has measure mu
    restricted to A on every target set, supporting
    Federer 4.1.8, p. 362, by the regular
    characteristic upper integral of 2.4.5, p. 84.
    No finiteness or measurability premise on the
    target set is imposed. *)
Lemma regular_characteristic_density (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_regular_measure mu)
    (A:set X) (s:X->R):is_characteristic_function A s->
  is_measure_density mu (real_total_integrand s) (measure_restrict mu A).
Proof.
move=>hs E.
pose c:=@CharacteristicFunction.value R X (A `&` E).
have hc:=@CharacteristicFunction.laws R X (A `&` E).
have hOn x:E x->c x=s x.
  move=>hE;rewrite /c;case:(pselect (A x))=>hA.
  - by rewrite (characteristic_on_set hc (conj hA hE)) (characteristic_on_set hs hA).
  - by rewrite (characteristic_off_set hc (fun h=>hA h.1)) (characteristic_off_set hs hA).
have hOff x:~E x->c x=0%R.
  move=>hE;exact:(characteristic_off_set hc (fun h=>hE h.2)).
have hGraph:=@real_subset_total_graph R X E s c hOn hOff.
rewrite /measure_restrict /measure_subset_upper_integral
  (@measure_upper_integral_graph_equivalent R X mu _ _ hGraph).
exact:esym (@regular_measure_characteristic_upper_integral R X mu hm (A `&` E) c hc hr).
Qed.

(** Source for [regular_characteristic_measure_with_density]: the
    actual original density-measure operation on chi_A
    equals the original measure restriction, supporting
    Federer 4.1.8, p. 362. *)
Theorem regular_characteristic_measure_with_density (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_regular_measure mu)
    (A:set X) (s:X->R):is_characteristic_function A s->
  measure_with_density mu (real_total_integrand s)=measure_restrict mu A.
Proof.
move=>hs;apply:funext=>E.
exact:(@measure_density_unique R X mu (real_total_integrand s)
  (measure_with_density mu (real_total_integrand s)) (measure_restrict mu A)
  (measure_with_density_laws mu (real_total_integrand s))
  (@regular_characteristic_density R X mu hm hr A s hs) E).
Qed.
