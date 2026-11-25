(** Federer (1969), 4.1.23, p. 379:
    changing a constant-vector measurable cell to
    its rectangular approximant has exactly the
    symmetric-difference L1 cost times the coefficient
    mass. Both one-sided errors are actual original
    measure values, including null and empty cells. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric MeasureUP MeasureBasic
  MeasureFiniteClosure MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP SummableRealArithmetic MeasureCharacteristicIntegral
  CharacteristicFunctionUP CharacteristicFunctionSealed
  CompactSummableFieldSealed CompactSummableFieldLaws CompactSummableFieldIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_summable_field_value_difference]:
    the original pointwise difference field
    used in the L1 cell errors
    of Federer 4.1.23, p. 379.
    This uses only the preceding
    opaque field's linear inclusion laws. *)
Lemma compact_summable_field_value_difference (R : realType)
    (X : topologicalType) (V : lmodType R) (N : V -> R)
    (hN : is_real_norm N) (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : @CompactSummableField.space R X V N hN mu hm) :
  @compact_summable_field_value R X V N hN mu hm (f-g)=
    (fun x => @compact_summable_field_value R X V N hN mu hm f x-
      @compact_summable_field_value R X V N hN mu hm g x).
Proof.
have hIdentity : f-g=(-1)*:g+f by rewrite scaleN1r addrC.
rewrite hIdentity compact_summable_field_value_add compact_summable_field_value_scale.
apply: funext=> x; by rewrite scaleN1r addrC.
Qed.

(** Source for [characteristic_absolute_set_difference]:
    the exact symmetric-difference error used
    for the rectangular approximation in Federer
    4.1.23, p. 379, by the
    original characteristic-function laws of 2.4.5. *)
Lemma characteristic_absolute_set_difference (R : realType) (X : choiceType)
    (A B : set X) x :
  `|@CharacteristicFunction.value R X A x-@CharacteristicFunction.value R X B x|=
    @CharacteristicFunction.value R X (A `\` B) x+
    @CharacteristicFunction.value R X (B `\` A) x.
Proof.
pose ca := @CharacteristicFunction.value R X A.
pose cb := @CharacteristicFunction.value R X B.
pose cd := @CharacteristicFunction.value R X (A `\` B).
pose ce := @CharacteristicFunction.value R X (B `\` A).
pose hA := @CharacteristicFunction.laws R X A.
pose hB := @CharacteristicFunction.laws R X B.
pose hD := @CharacteristicFunction.laws R X (A `\` B).
pose hE := @CharacteristicFunction.laws R X (B `\` A).
case: (pselect (A x))=> hAx; case: (pselect (B x))=> hBx.
- have hNotD : ~(A `\` B) x by move=> h; exact: h.2 hBx.
  have hNotE : ~(B `\` A) x by move=> h; exact: h.2 hAx.
  by rewrite (characteristic_on_set hA hAx) (characteristic_on_set hB hBx)
    (characteristic_off_set hD hNotD) (characteristic_off_set hE hNotE)
    subrr normr0 add0r.
- have hDPoint : (A `\` B) x := conj hAx hBx.
  have hNotE : ~(B `\` A) x by move=> h; exact: hBx h.1.
  by rewrite (characteristic_on_set hA hAx) (characteristic_off_set hB hBx)
    (characteristic_on_set hD hDPoint) (characteristic_off_set hE hNotE)
    subr0 normr1 addr0.
- have hNotD : ~(A `\` B) x by move=> h; exact: hAx h.1.
  have hEPoint : (B `\` A) x := conj hBx hAx.
  by rewrite (characteristic_off_set hA hAx) (characteristic_on_set hB hBx)
    (characteristic_off_set hD hNotD) (characteristic_on_set hE hEPoint)
    sub0r normrN normr1 add0r.
- have hNotD : ~(A `\` B) x by move=> h; exact: hAx h.1.
  have hNotE : ~(B `\` A) x by move=> h; exact: hBx h.1.
  by rewrite (characteristic_off_set hA hAx) (characteristic_off_set hB hBx)
    (characteristic_off_set hD hNotD) (characteristic_off_set hE hNotE)
    subrr normr0 add0r.
Qed.

(** Source for [compact_characteristic_set_difference_cost]:
    the constant-vector step current's original
    L1 error equals its coefficient mass
    times the two one-sided set errors,
    supporting Federer 4.1.23, p. 379.
    The representatives are actual compact fields;
    no almost-equality quotient or additional regularity
    of either cell is assumed. *)
Theorem compact_characteristic_set_difference_cost (R : realType)
    (X : topologicalType) (V : lmodType R) (N : V -> R)
    (hN : is_real_norm N) (mu : set X -> \bar R) (hm : is_measure mu)
    (A B : set X) (z : V)
    (f g : @CompactSummableField.space R X V N hN mu hm) :
  measure_measurable mu A -> measure_measurable mu B ->
  (mu A< +oo)%E -> (mu B< +oo)%E ->
  (forall x, @compact_summable_field_value R X V N hN mu hm f x=
    @CharacteristicFunction.value R X A x*:z) ->
  (forall x, @compact_summable_field_value R X V N hN mu hm g x=
    @CharacteristicFunction.value R X B x*:z) ->
  (@compact_summable_field_size R X V N hN mu hm (f-g))%:E=
    ((N z)%:E*(mu (A `\` B)+mu (B `\` A)))%E.
Proof.
move=> hA hB hAFinite hBFinite hF hG.
pose value := @compact_summable_field_value R X V N hN mu hm.
pose size := @compact_summable_field_size R X V N hN mu hm.
pose D := A `\` B.
pose E := B `\` A.
pose cd := @CharacteristicFunction.value R X D.
pose ce := @CharacteristicFunction.value R X E.
have hDMeas := measure_measurable_difference hm hA hB.
have hEMeas := measure_measurable_difference hm hB hA.
have hDFinite : (mu D< +oo)%E.
  apply: (le_lt_trans _ hAFinite).
  apply: (@measure_mono R X mu hm D A)=> x hx; exact: hx.1.
have hEFinite : (mu E< +oo)%E.
  apply: (le_lt_trans _ hBFinite).
  apply: (@measure_mono R X mu hm E B)=> x hx; exact: hx.1.
have hDValue : mu D \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm D)).
have hEValue : mu E \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm E)).
pose a := fine (mu D).
pose b := fine (mu E).
have hDI := @measure_characteristic_integral R X mu hm D cd
  (@CharacteristicFunction.laws R X D) hDMeas.
have hEI := @measure_characteristic_integral R X mu hm E ce
  (@CharacteristicFunction.laws R X E) hEMeas.
rewrite -(fineK hDValue) in hDI; rewrite -(fineK hEValue) in hEI.
have hSum := @real_total_integral_add R X mu hm cd ce a b hDI hEI.
have hScale := @real_total_integral_scale R X mu hm
  (fun x => cd x+ce x) (a+b) (N z) hSum.
have hValues x : value (f-g) x=
    (@CharacteristicFunction.value R X A x-@CharacteristicFunction.value R X B x)*:z.
  by rewrite /value compact_summable_field_value_difference (@hF x) (@hG x) scalerBl.
have hFunction : (fun x => N (value (f-g) x))=(fun x => N z*(cd x+ce x)).
  apply: funext=> x; rewrite hValues (real_seminorm_scale hN.1)
    characteristic_absolute_set_difference mulrC.
  reflexivity.
have hIntegral := @compact_summable_field_size_integral R X V N hN mu hm (f-g).
rewrite hFunction in hIntegral.
have hCost : (size (f-g))%:E=(N z*(a+b))%:E := measure_integral_unique hIntegral hScale.
rewrite -(fineK hDValue) -(fineK hEValue) -EFinD -EFinM.
exact: hCost.
Qed.
