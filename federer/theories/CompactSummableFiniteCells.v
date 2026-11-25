(** Federer (1969), 4.1.23, p. 379: the
    finite step-field reduction preserves the exact
    integral mass cost. Represent every actual measurable
    cell by its original constant multivector field,
    without identifying distinct almost-equal fields. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric PartialFunctionBasic
  RealMetricBackground MeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP FiniteSignedRealIntegral CharacteristicFunctionUP
  CharacteristicFunctionSealed CompactSummableFieldSealed
  CompactSummableFieldLaws CompactSummableFieldIntegral
  CompactSummableFieldExtensionality CompactCharacteristicSummableField
  FiniteImageMeasurableCells.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactFiniteCells.
Variable R : realType.
Variable X : topologicalType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Local Notation W := (@CompactSummableField.space R X V N hN mu hm).
Local Notation value := (@compact_summable_field_value R X V N hN mu hm).
Local Notation size := (@compact_summable_field_size R X V N hN mu hm).

(** Source for [compact_summable_field_value_zero]: the
    actual zero field in the step-field reduction
    of Federer 4.1.23, p. 379, is
    pointwise zero, including on a null carrier. *)
Lemma compact_summable_field_value_zero : value (0 : W)=(fun _ => 0).
Proof. by rewrite /compact_summable_field_value !linear0. Qed.

(** Source for [compact_summable_field_value_finite_sum]:
    the original actual finite step-field sum
    in Federer 4.1.23, p. 379,
    retains its literal point values. *)
Lemma compact_summable_field_value_finite_sum (I : finType) (f : I -> W) x :
  value (\sum_i f i) x=\sum_i value (f i) x.
Proof.
elim/big_rec2: _=> [|i a b hI hA].
- by rewrite compact_summable_field_value_zero.
- by rewrite compact_summable_field_value_add hA.
Qed.

(** Source for [compact_summable_finite_cell_decomposition]:
    the finite-image reduction in Federer 4.1.23,
    p. 379, is a finite sum of
    original constant-vector measurable cells. The sum
    of their original L1 sizes equals the
    original size exactly. No coordinatewise triangle
    estimate or nonzero-cell assumption is used. *)
Theorem compact_summable_finite_cell_decomposition (f : W) (K : set X) :
  compact K -> measure_measurable mu K -> (mu K< +oo)%E ->
  finite_set (value f @` setT) -> (forall x, ~K x -> value f x=0) ->
  exists (I : finType) (v : I -> V) (A : I -> set X) (w : I -> W),
    (forall i, measure_measurable mu (A i) /\ (mu (A i)< +oo)%E /\ A i `<=` K) /\
    (forall i j, i!=j -> forall x, A i x -> A j x -> False) /\
    (forall x, K x <-> exists i, A i x) /\
    (forall i x, value (w i) x=@CharacteristicFunction.value R X (A i) x*:v i) /\
    (forall i, (size (w i))%:E=((N (v i))%:E*mu (A i))%E) /\
    f=\sum_i w i /\ size f=\sum_i size (w i).
Proof.
move=> hK hKMeas hKFinite hImage hOff.
have [I [v [A [hCell [hDisjoint [hCover [hValue hNorm]]]]]]] :=
  @finite_image_measurable_cell_decomposition R X V N hN mu hm
    (value f) K (@compact_summable_field_measurable R X V N hN mu hm f)
    hImage hKMeas hKFinite hOff.
have hPieces i : exists a : W,
    (forall x, value a x=@CharacteristicFunction.value R X (A i) x*:v i) /\
    (size a)%:E=((N (v i))%:E*mu (A i))%E /\
    forall x, ~K x -> value a x=0.
  exact: (@compact_characteristic_summable_field_exists R X V N hN mu hm
    (A i) (hCell i).1 (hCell i).2.1 K hK (hCell i).2.2 (v i)).
have [w hW] := choice hPieces.
have hSum : f=\sum_i w i.
  apply: (@compact_summable_field_value_injective R X V N hN mu hm).
  apply: funext=> x; rewrite compact_summable_field_value_finite_sum.
  rewrite (@hValue x); apply: eq_bigr=> i _; symmetry.
  exact: (hW i).1.
have hNormSum : (fun x => N (value f x))=
    (fun x => \sum_i N (value (w i) x)).
  apply: funext=> x; rewrite (@hNorm x); apply: eq_bigr=> i _.
  rewrite (hW i).1.
  case: (pselect (A i x))=> hx.
  - by rewrite (characteristic_on_set (@CharacteristicFunction.laws R X (A i)) hx)
      scale1r mul1r.
  - by rewrite (characteristic_off_set (@CharacteristicFunction.laws R X (A i)) hx)
      scale0r (real_seminorm_zero hN.1) mul0r.
have hIntegrals i : is_measure_integral mu
    (real_total_integrand (fun x => N (value (w i) x))) (size (w i))%:E.
  exact: (@compact_summable_field_size_integral R X V N hN mu hm (w i)).
have hIntegralSum := @finite_signed_real_sum_integral R X I mu hm (enum I)
  (fun i x => (N (value (w i) x) : real_line_metric R)) (fun i => size (w i))
  (fun i _ => hIntegrals i).
have hSumFunction : (fun x : X => (\sum_(i <- enum I) N (value (w i) x)
    : real_line_metric R))=(fun x => (N (value f x) : real_line_metric R)).
  apply: funext=> x; rewrite big_enum; exact: esym (congr1 (fun q => q x) hNormSum).
rewrite hSumFunction big_enum in hIntegralSum.
have hSize : (size f)%:E=(\sum_i size (w i))%:E :=
  measure_integral_unique
    (@compact_summable_field_size_integral R X V N hN mu hm f) hIntegralSum.
exists I,v,A,w; split; first exact: hCell.
split; first exact: hDisjoint.
split; first exact: hCover.
split; first by move=> i x; exact: (hW i).1.
split; first by move=> i; exact: (hW i).2.1.
split; first exact: hSum.
exact: EFin_inj hSize.
Qed.
End CompactFiniteCells.
