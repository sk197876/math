(** Federer (1969), 4.1.23, p. 379: approximate
    the smooth compact coefficient by actual finite-image
    fields in L1. A characteristic restriction keeps
    the original compact carrier pointwise, without
    increasing the approximation error or replacing
    the raw Omega space by an almost-equality quotient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasurableNormedFunctionUP CharacteristicFunctionUP
  CharacteristicFunctionSealed CharacteristicVectorPiece MeasureLpNorm
  MeasureLpMembershipUP MeasureLpConvergence MeasureLpTotalFiniteApproximation
  ExtendedRealOrderLimit CompactSummableFieldSealed CompactSummableFieldLaws
  CompactSummableFieldIntegral CompactSummableFieldRepresentation MeasurableLoneNormComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactFiniteImageApproximation.
Variable R : realType.
Variable X : topologicalType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Local Notation VN := (real_norm_metric_space hN).
Local Notation W := (@CompactSummableField.space R X V N hN mu hm).
Local Notation value := (@compact_summable_field_value R X V N hN mu hm).
Local Notation size := (@compact_summable_field_size R X V N hN mu hm).

(** Source for [compact_summable_finite_image_approximation]:
    the original mass-L1 step approximation in
    Federer 4.1.23, p. 379, preserves
    the same compact carrier K at every point.
    The approximant is an actual Omega member
    with finite image and arbitrarily small
    original difference cost. Empty K is allowed. *)
Theorem compact_summable_finite_image_approximation
    (f : W) (K : set X) (epsilon : R) :
  compact K -> measure_measurable mu K ->
  (forall x, ~K x -> value f x=0) -> 0<epsilon ->
  exists g : W,
    finite_set (value g @` setT) /\
    (forall x, ~K x -> value g x=0) /\
    size (f-g)%R<epsilon.
Proof.
move=> hK hKMeas hOff hEpsilon.
have hFLp := @compact_summable_field_lone R X V N hN mu hm f.
have [a [hALp [hFiniteImage hLimit]]]:=@measure_lp_total_finite_image_approximation
  R X V N hN mu hm 1 (value f) hFLp.
have hPositive : (0<epsilon%:E)%E by rewrite lte_fin.
have [i hNear] := hLimit.2 epsilon%:E hPositive.
pose raw := a i.
have hRawLp := hALp i.
have hRawMeas := hRawLp.2.1.
have hRawError := @hNear i (leqnn i).
pose chi := @CharacteristicFunction.value R X K.
pose hChi := @CharacteristicFunction.laws R X K.
pose cut := fun x : X => (chi x*:raw x : VN).
have hCutMeas := @measurable_normed_characteristic_piece R X V N hN mu hm
  K chi raw hChi hKMeas hRawMeas.
have hCutBound (x : X) : N (cut x)<=N (raw x).
  rewrite /cut /chi; case: (pselect (K x))=> hx.
  - by rewrite (characteristic_on_set hChi hx) scale1r.
  - rewrite (characteristic_off_set hChi hx) scale0r (real_seminorm_zero hN.1).
    exact: real_seminorm_nonnegative hN.1 (raw x).
have hCutNorm := @measurable_lone_total_norm_monotone R X V N hN mu hm
  cut raw hCutMeas hRawMeas hCutBound.
have hCutFinite : (measure_lp_norm mu N 1 (partial_function_total cut)< +oo)%E :=
  le_lt_trans hCutNorm hRawLp.2.2.1.
have hCutOff (x : X) (hx : ~K x) : cut x=0.
  by rewrite /cut /chi (characteristic_off_set hChi hx) scale0r.
have [g [hGValue [_ [hGOff [_ hGSize]]]]] :=
  @compact_summable_partial_field_representative R X V N hN mu hm
    (partial_function_total cut) hCutMeas hCutFinite K hK
    (fun x y hValue hx => eq_trans (esym hValue) (@hCutOff x hx)).
have hValues : value g=cut.
  apply: funext=> x; exact: (@hGValue x (cut x) (erefl (cut x))).
have hFMeas := hFLp.2.1.
have hFirstDifference := @measurable_lone_total_difference R X V N hN mu hm
  (value f) cut hFMeas hCutMeas.
have hSecondDifference := @measurable_lone_total_difference R X V N hN mu hm
  (value f) raw hFMeas hRawMeas.
have hPointwise (x : X) : N (value f x-cut x)<=N (value f x-raw x).
  case: (pselect (K x))=> hx.
  - by rewrite /cut /chi (characteristic_on_set hChi hx) scale1r.
  - rewrite (@hOff x hx) (@hCutOff x hx) subrr (real_seminorm_zero hN.1).
    exact: real_seminorm_nonnegative hN.1 _.
have hErrorBound := @measurable_lone_total_norm_monotone R X V N hN mu hm
  (fun x => (value f x-cut x)%R) (fun x => (value f x-raw x)%R)
  hFirstDifference.1 hSecondDifference.1 hPointwise.
rewrite hFirstDifference.2 hSecondDifference.2 in hErrorBound.
have hError : (measure_lp_distance mu N 1 (partial_function_total (value f))
    (partial_function_total (value g))<epsilon%:E)%E.
  rewrite hValues; exact: le_lt_trans hErrorBound hRawError.
have hCost := @compact_summable_field_lp_difference R X V N hN mu hm f g.
rewrite -hCost lte_fin in hError.
have hFiniteUnion : finite_set ((raw @` setT) `|` [set (0:VN)]).
  rewrite finite_setU; split; [exact: hFiniteImage i | exact: finite_set1].
have hImageSubset : (cut @` setT) `<=` ((raw @` setT) `|` [set (0:VN)]).
  move=> y [x _ <-]; rewrite /cut /chi; case: (pselect (K x))=> hx.
  - rewrite (characteristic_on_set hChi hx) scale1r; left; by exists x.
  - rewrite (characteristic_off_set hChi hx) scale0r; right; exact: erefl.
exists g; split.
- rewrite hValues; exact: sub_finite_set hImageSubset hFiniteUnion.
- by split.
Qed.
End CompactFiniteImageApproximation.
