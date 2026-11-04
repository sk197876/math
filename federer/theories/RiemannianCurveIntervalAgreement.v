(** Federer (1969), 3.2.46, p. 281: localization of the
    actual curve integral to its compact parameter interval.
    Neighbourhood agreement preserves interior derivatives; only
    the two proved null endpoints are discarded. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealMetricBackground
  ExtendedRealOrderTopology NormedCurveDerivativeUP NormedCurveLocalAgreement
  EuclideanCurveDifferentiability LocallyAbsolutelyContinuousCurve
  RiemannianTensorUP RiemannianCurveCost PartialFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_two_endpoints_conull]: the two endpoints
    may be removed from a curve integral in Federer 3.2.46,
    p. 281, by scalar singleton nullity from 2.5.17, p. 111.
    Equal endpoints are included. *)
Lemma scalar_two_endpoints_conull (R : realType) (a b : R) :
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set t : real_line_metric R | t <> a /\ t <> b].
Proof.
rewrite /measure_almost_everywhere.
have he : ~` [set t : real_line_metric R | t <> a /\ t <> b] =
    [set a] `|` [set b].
  apply/seteqP; split=> t.
  - move=> hn; case: (pselect (t=a))=> ha; first by left; exact: ha.
    right; apply: contrapT=> hb; exact: hn (conj ha hb).
  - move=> [<-|<-] [ha hb]; [exact: ha erefl | exact: hb erefl].
rewrite he; exact (@measure_null_union R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) [set a] [set b]
  (@lebesgue_scalar_singleton R a) (@lebesgue_scalar_singleton R b)).
Qed.

(** Source for [riemannian_interval_speed_almost_agreement]:
    genuine interval values determine the integral in Federer
    3.2.46, p. 281. The representative's actual derivative supplies
    common graph values almost everywhere on the interval, even
    when either endpoint has no derivative. *)
Lemma riemannian_interval_speed_almost_agreement (R : realType) n g
    (C D : R -> inner_metric_space (@euclidean_inner_productP R n)) a b :
  (forall t, a <= t <= b -> C t = D t) ->
  is_locally_absolutely_continuous_curve D ->
  measure_almost_everywhere_on (@lebesgue_scalar_measure R) `[a,b]
    (partial_function_agreement (riemannian_curve_speed g D) (riemannian_curve_speed g C)).
Proof.
move=> hEq hD.
apply: (measure_almost_everywhere_on_implication _ _ _).2.
apply: (measure_almost_everywhere_mono (lebesgue_scalar_is_measure R) _
  (measure_almost_everywhere_and (lebesgue_scalar_is_measure R)
    (euclidean_absolute_continuous_derivative_almost hD)
    (scalar_two_endpoints_conull a b))).
move=> t [[v hv] [hta htb]] ht.
have ht' : a <= t <= b by move: ht; rewrite /mkset in_itv /=.
have htInterior : a < t < b.
  have /andP [hat htb'] := ht'.
  apply/andP; split; rewrite lt_neqAle; apply/andP; split=> //;
    apply/eqP=> hBad; [exact: hta (esym hBad) | exact: htb hBad].
have hCv := (@normed_curve_derivative_interval_agreement R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) C D a b t v htInterior hEq).2 hv.
exists (riemannian_tensor_speed g (D t) v)%:E; split.
- exists v; by split.
- exists v; split=> //; by rewrite (hEq t ht').
Qed.
