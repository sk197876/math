(** Federer (1969), 3.2.48, p. 284: the actual
    fibre similarity transports full restricted measures and
    signed partial integrals. Supporting laws from 2.10.11,
    p. 176, and 2.4.18, pp. 90–91;
    completions and arbitrary original source sets are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import LipschitzUP HausdorffMeasure HausdorffSimilarityEmbedding
  MeasureUP MeasureRestriction MeasurePushforward MeasureScaleIntegral
  PushforwardMeasurabilityTransfer PartialFunctionUP PartialFunctionPrecomposition
  MeasureIntegralUP InjectivePushforwardIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_similarity_restricted_measure]: supporting
    the first fibre-integral equality of 3.2.48,
    p. 284. Equality is between full restricted
    outer measures, for every original source A. *)
Lemma hausdorff_similarity_restricted_measure (R:realType) (X Y:metricType R)
    (f:X->Y) (g:Y->X) c:
  0<c ->cancel f g ->(forall x y,mdist (f x) (f y)=c*mdist x y) ->
  forall q A,measure_restrict (@hausdorff_measure R Y q) (f @` A)=
    measure_scale (c^+q) (measure_pushforward f (measure_restrict (@hausdorff_measure R X q) A)).
Proof.
move=>hc hLeft hDistance q A; apply:funext=>T.
have hImage:f @` (A `&` (f @^-1` T))=(f @` A) `&` T.
  apply/seteqP; split=>y.
  - move=>[x [hx ht] <-]; split; first by exists x.
    exact ht.
  - move=>[[x hx <-] ht]; exists x; by split.
rewrite /measure_restrict -hImage.
exact (@hausdorff_similarity_embedding_invariance R X Y f g c hc hLeft hDistance q _).
Qed.

(** Source for [hausdorff_similarity_preimage_measurable]: a completed
    measurable actual fibre has a completed measurable parameter
    set, supporting 3.2.48, p. 284. Only the
    similarity's actual left inverse is used; its image
    need not be the whole target ambient space. *)
Lemma hausdorff_similarity_preimage_measurable (R:realType) (X Y:metricType R)
    (f:X->Y) (g:Y->X) c:
  0<c ->cancel f g ->(forall x y,mdist (f x) (f y)=c*mdist x y) ->
  forall q T,measure_measurable (@hausdorff_measure R Y q) T ->
    measure_measurable (@hausdorff_measure R X q) (f @^-1` T).
Proof.
move=>hc hLeft hDistance q T hT.
pose rho:=measure_restrict (@hausdorff_measure R Y q) (f @` setT).
pose beta:=@hausdorff_measure R X q.
have hPower:0<c^+q:=exprn_gt0 q hc.
have hIdentity:=@hausdorff_similarity_restricted_measure R X Y f g c hc hLeft hDistance q setT.
have hRestrict:measure_restrict beta setT=beta by apply:funext=>A; rewrite /measure_restrict setTI.
rewrite -/beta hRestrict in hIdentity.
have hInverse:measure_scale (c^+q)^-1 rho=measure_pushforward f beta.
  rewrite /rho hIdentity; exact (measure_scale_inverse _ hPower).
have hRho:=measure_restrict_is_measure (@hausdorff_measure_is_measure R Y q) (f @` setT).
have hTRho:measure_measurable rho T:=measure_restrict_measurable _ hT.
have hTScaled:=@measure_scale_measurable R Y rho hRho (c^+q)^-1
  T hTRho.
rewrite hInverse in hTScaled.
exact (measure_pushforward_preimage_measurable (can_inj hLeft) hTScaled).
Qed.

(** Source for [hausdorff_similarity_subset_integral]: supporting
    signed fibre-integral transport in 3.2.48, p. 284.
    The integrand is an original partial graph; its composite
    retains precisely the original domain and every defined
    finite or infinite signed value. No separate composition
    measurability assumption is added. *)
Lemma hausdorff_similarity_subset_integral (R:realType) (X Y:metricType R)
    (f:X->Y) (g:Y->X) c:
  0<c ->cancel f g ->(forall x y,mdist (f x) (f y)=c*mdist x y) ->
  forall q A (u:partial_function Y (extended_real_line R)) a,
    is_measure_integral (measure_restrict (@hausdorff_measure R X q) A)
      (partial_function_precompose f u) a ->
    is_measure_integral (measure_restrict (@hausdorff_measure R Y q) (f @` A)) u
      (((c^+q)%:E)*a)%E.
Proof.
move=>hc hLeft hDistance q A u a hI.
have hPush:=(@injective_pushforward_integral_iff R X Y
  (measure_restrict (@hausdorff_measure R X q) A)
  (measure_restrict_is_measure (@hausdorff_measure_is_measure R X q) A)
  f u (can_inj hLeft) a).1 hI.
rewrite (@hausdorff_similarity_restricted_measure R X Y f g c hc hLeft hDistance q A).
exact (@measure_scale_integral R Y _
  (measure_pushforward_is_measure f (measure_restrict_is_measure (@hausdorff_measure_is_measure R X q) A))
  (c^+q) (exprn_gt0 q hc) u a hPush).
Qed.


(** Source for [hausdorff_similarity_subset_integral_iff]: the
    signed fibre similarity in 3.2.48, p. 284,
    preserves integral definedness in both directions. Its
    positive finite scale is cancelled through actual measure
    laws; no value is supplied to an undefined signed difference. *)
Lemma hausdorff_similarity_subset_integral_iff (R:realType) (X Y:metricType R)
    (f:X->Y) (g:Y->X) c:
  0<c ->cancel f g ->(forall x y,mdist (f x) (f y)=c*mdist x y) ->
  forall q A (u:partial_function Y (extended_real_line R)) a,
    is_measure_integral (measure_restrict (@hausdorff_measure R X q) A)
      (partial_function_precompose f u) a <->
    is_measure_integral (measure_restrict (@hausdorff_measure R Y q) (f @` A)) u
      (((c^+q)%:E)*a)%E.
Proof.
move=>hc hLeft hDistance q A u a; split.
- exact (@hausdorff_similarity_subset_integral R X Y f g c hc hLeft hDistance q A u a).
- move=>hI.
  pose beta:=measure_restrict (@hausdorff_measure R X q) A.
  pose nu:=measure_pushforward f beta.
  pose C:=c^+q.
  have hC:0<C:=exprn_gt0 q hc.
  have hCInverse:0<C^-1 by rewrite invr_gt0.
  have hBeta:=measure_restrict_is_measure (@hausdorff_measure_is_measure R X q) A.
  have hNu:=measure_pushforward_is_measure f hBeta.
  rewrite (@hausdorff_similarity_restricted_measure R X Y f g c hc hLeft hDistance q A) in hI.
  have hRestore:=@measure_scale_integral R Y (measure_scale C nu)
    (measure_scale_is_measure hNu hC) C^-1 hCInverse u (C%:E*a)%E hI.
  rewrite (measure_scale_inverse nu hC) in hRestore.
  have hValue:(C^-1%:E*(C%:E*a)=a)%E.
    by rewrite muleA -EFinM mulVf ?gt_eqF // mul1e.
  rewrite hValue in hRestore.
  exact ((@injective_pushforward_integral_iff R X Y beta hBeta f u (can_inj hLeft) a).2 hRestore).
Qed.
