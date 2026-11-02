(** Federer (1969), 3.2.36, p. 273: transport closed
    convex covers only at finite cutoffs, with local witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import CoveringFamilyUP MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope
  MetricScaleCutoffCost MetricScaleWeightedBound MetricScaleMeasureBound CaratheodoryLimitUP
  CaratheodoryBorelRegular MeasureUP MeasureBasic MeasureIndexedCover MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_finite_generator_image_bound]: the forward
    cover transport in the Q_1 invariance consequence of Federer
    3.2.36, p. 273, through the construction of 2.10.1,
    pp. 169--170. Only generators of finite diameter need local
    transported witnesses; every global auxiliary measure is already
    supplied by an opaque envelope. No global generator map is chosen,
    and arbitrary source sets and infinite measure values are retained. *)
Theorem caratheodory_finite_generator_image_bound (R:realType) (X Y:metricType R)
    (J K:choiceType) (S:J->set X) (T:K->set Y) (c:J->\bar R) (d:K->\bar R)
    (f:X->Y) (mu:set X->\bar R) (rho:set Y->\bar R):
  is_caratheodory_limit S c mu ->is_caratheodory_limit T d rho ->
  (forall k,0<=d k) ->
  (forall j,metric_set_bounded (S j) ->exists k,
    f @` S j `<=` T k /\extended_metric_diameter (T k)<=extended_metric_diameter (S j) /\d k<=c j) ->
  forall A,rho (f @` A)<=mu A.
Proof.
move=>hMu hRho hD hTransport A.
apply:(caratheodory_limit_least hRho)=>delta xi hDelta hXi.
have [ell hCutoff]:=reciprocal_metric_cutoffs_cofinal hDelta.
pose e:R:=(((ell.+1)%:R)^-1)%R.
have he:(0<e)%R by rewrite /e invr_gt0 ltr0n.
pose nu:=metric_scale_envelope S c e%:E.
have hNu:=metric_scale_envelope_specification S c e%:E.
have hXiMeasure:=metric_scale_envelope_is_measure hXi hD.
pose q (B:set X): \bar R:=xi (f @` B).
have hQ:is_measure q.
  constructor; first by move=>B; exact:(@measure_nonnegative R Y xi hXiMeasure (f @` B)).
  move=>B G hG hCover.
  apply:(@measure_indexed_cover R Y [the choiceType of set X] xi hXiMeasure
    (f @` B) G (fun C=>f @` C) hG).
  move=>y [x hx <-]; have [C hC hxC]:=hCover x hx; exists C=>//; by exists x.
have hGenerator j:extended_metric_diameter (S j)<=e%:E ->q (S j)<=c j.
  move=>hSize.
  have hBound:metric_set_bounded (S j):=le_lt_trans hSize (ltry e).
  have [k [hCover [hDiameter hCost]]]:=hTransport j hBound.
  have hTargetSize:extended_metric_diameter (T k)<=delta:=le_trans hDiameter (le_trans hSize hCutoff).
  apply:le_trans (@measure_mono R Y xi hXiMeasure _ _ hCover) _.
  exact:le_trans (@metric_scale_generator_bound R Y K T d delta xi k hXi (hD k) hTargetSize) hCost.
have hBound:=@measure_bounded_by_metric_scale_envelope R X J S c e%:E nu q hNu hQ hGenerator A.
apply:le_trans hBound _.
exact:(@caratheodory_limit_upper R X J S c mu hMu A e%:E nu he hNu).
Qed.

(** Source for [caratheodory_finite_generator_preimage_bound]: the
    reverse closed-cover transport for Q_1 in Federer 3.2.36,
    p. 273. At each finite cutoff a target generator has either
    empty original preimage or a locally specified covering generator
    with no larger diameter or cost. The empty branch contributes
    zero directly, preserving empty cover slots. Injectivity identifies
    the preimage of the original image; no measurability of A is added. *)
Theorem caratheodory_finite_generator_preimage_bound (R:realType) (X Y:metricType R)
    (J K:choiceType) (S:J->set X) (T:K->set Y) (c:J->\bar R) (d:K->\bar R)
    (f:X->Y) (mu:set X->\bar R) (rho:set Y->\bar R):
  is_caratheodory_limit S c mu ->is_caratheodory_limit T d rho ->
  (forall j,0<=c j) ->(forall k,0<=d k) ->injective f ->
  (forall k,metric_set_bounded (T k) ->
    f @^-1` T k=set0 \/exists j,
      f @^-1` T k `<=` S j /\extended_metric_diameter (S j)<=extended_metric_diameter (T k) /\c j<=d k) ->
  forall A,mu A<=rho (f @` A).
Proof.
move=>hMu hRho hC hD hInjective hTransport A.
apply:(caratheodory_limit_least hMu)=>delta xi hDelta hXi.
have [ell hCutoff]:=reciprocal_metric_cutoffs_cofinal hDelta.
pose e:R:=(((ell.+1)%:R)^-1)%R.
have he:(0<e)%R by rewrite /e invr_gt0 ltr0n.
pose nu:=metric_scale_envelope T d e%:E.
have hNu:=metric_scale_envelope_specification T d e%:E.
have hXiMeasure:=metric_scale_envelope_is_measure hXi hC.
pose q:=measure_pushforward f xi.
have hQ:is_measure q:=measure_pushforward_is_measure f hXiMeasure.
have hGenerator k:extended_metric_diameter (T k)<=e%:E ->q (T k)<=d k.
  move=>hSize.
  have hBound:metric_set_bounded (T k):=le_lt_trans hSize (ltry e).
  have [hEmpty|[j [hCover [hDiameter hCost]]]]:=hTransport k hBound.
  - rewrite /q /measure_pushforward hEmpty (measure_empty hXiMeasure); exact:hD.
  - have hSourceSize:extended_metric_diameter (S j)<=delta:=le_trans hDiameter (le_trans hSize hCutoff).
    apply:le_trans (@measure_mono R X xi hXiMeasure _ _ hCover) _.
    exact:le_trans (@metric_scale_generator_bound R X J S c delta xi j hXi (hC j) hSourceSize) hCost.
have hBound:=@measure_bounded_by_metric_scale_envelope R Y K T d e%:E nu q hNu hQ hGenerator (f @` A).
have hPreimage:f @^-1` (f @` A)=A.
  apply/seteqP; split=>x.
  - move=>[a ha h]; have hEq:a=x:=hInjective a x h; by rewrite -hEq.
  - move=>hx; by exists x.
rewrite /q /measure_pushforward hPreimage in hBound.
apply:le_trans hBound _.
exact:(@caratheodory_limit_upper R Y K T d rho hRho (f @` A) e%:E nu he hNu).
Qed.
