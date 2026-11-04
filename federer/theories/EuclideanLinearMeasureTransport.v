(** Federer (1969), 2.7.16, pp. 134–135:
    invertible linear coordinates scale actual Lebesgue
    measure by the absolute determinant. These exact outer
    and completed-measurability laws support the frozen
    coarea calculation of 3.2.46, p. 282. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLinearMaps EuclideanLebesgueDimensions EuclideanLebesgueDeterminant
  MeasureUP MeasurePushforward MeasureRestriction MeasureScaleIntegral
  PushforwardMeasurabilityTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_linear_inverse_pushforward]:
    the inverse of an actual linear isomorphism pushes
    Lebesgue measure forward to |det L| times Lebesgue
    measure, 2.7.16, pp. 134–135. The inverse
    is supplied only as a local witness; dimension zero
    retains determinant one and its positive atom. *)
Lemma euclidean_linear_inverse_pushforward (R : realType) n
    (L I : {linear R_n R n -> R_n R n}) :
  cancel L I -> cancel I L ->
  measure_pushforward (I : inner_metric_space (@euclidean_inner_productP R n) ->
    inner_metric_space (@euclidean_inner_productP R n)) (@euclidean_lebesgue_measure R n)=
    measure_scale `|euclidean_det L| (@euclidean_lebesgue_measure R n).
Proof.
move=> hLI hIL.
have hDet := euclidean_det_inverse hLI.
have hLne := (euclidean_det_injective L).2 (can_inj hLI).
have hIne := (euclidean_det_injective I).2 (can_inj hIL).
have hNorm : `|euclidean_det I|*`|euclidean_det L|= 1.
  by have hh := congr1 (fun t : R=>`|t|) hDet; rewrite /= normrM normr1 in hh.
have hAbsI : `|euclidean_det I|!=0 by rewrite normr_eq0.
have hInverse : `|euclidean_det I|^-1=`|euclidean_det L|.
  have hh := congr1 (fun t : R=>`|euclidean_det I|^-1*t) hNorm.
  rewrite /= mulrA (mulVf hAbsI) mul1r mulr1 in hh; exact:esym hh.
apply:funext=> S; rewrite /measure_pushforward /measure_scale.
by rewrite (euclidean_lebesgue_linear_pushforward hIne) hInverse.
Qed.

(** Source for [euclidean_linear_image_measurable]:
    completed Lebesgue measurability is preserved by actual
    invertible linear coordinates, 2.7.16, pp. 134–135,
    supporting 3.2.46, p. 282. No Borelness or
    finite measure of the original subset is assumed. *)
Lemma euclidean_linear_image_measurable (R : realType) n
    (L : {linear R_n R n -> R_n R n})
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  injective L -> measure_measurable (@euclidean_lebesgue_measure R n) S ->
  measure_measurable (@euclidean_lebesgue_measure R n) (L @` S).
Proof.
move=> hInj hS.
have [I [hLI hIL]] := euclidean_linear_inverse hInj.
have hDet : 0<`|euclidean_det L| by rewrite normr_gt0; exact:(euclidean_det_injective L).2 hInj.
have hScaled := @measure_scale_measurable R _ (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) `|euclidean_det L| S hS.
rewrite -(euclidean_linear_inverse_pushforward hLI hIL) in hScaled.
have hPre := @measure_pushforward_preimage_measurable R _ _ I
  (@euclidean_lebesgue_measure R n) S (can_inj hIL) hScaled.
have hImage : I @^-1` S=L @` S.
  apply/seteqP; split=> z.
  - move=> hz; exists (I z); first exact hz; exact:hIL.
  - move=> [x hx <-]; change (S (I (L x))); by rewrite hLI.
by rewrite -hImage.
Qed.

(** Source for [euclidean_linear_restricted_pushforward]:
    exact determinant transport after restricting to the
    original source S, supporting 3.2.46, p. 282,
    from 2.7.16, pp. 134–135. Equality holds
    on every target test set, even for nonmeasurable S. *)
Lemma euclidean_linear_restricted_pushforward (R : realType) n
    (L : {linear R_n R n -> R_n R n})
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  injective L ->
  measure_pushforward L (measure_restrict (@euclidean_lebesgue_measure R n) S)=
    measure_scale (`|euclidean_det L|^-1)
      (measure_restrict (@euclidean_lebesgue_measure R n) (L @` S)).
Proof.
move=> hInj; apply:funext=> T.
rewrite /measure_pushforward /measure_restrict /measure_scale.
have hSets : S `&` (L @^-1` T)=L @^-1` ((L @` S) `&` T).
  apply/seteqP; split=> x.
  - move=> [hx hT]; split; last exact hT; by exists x.
  - move=> [[z hz hEq] hT]; split; last exact hT.
    by rewrite -(hInj _ _ hEq).
rewrite hSets.
exact (@euclidean_lebesgue_linear_pushforward R n L
  ((euclidean_det_injective L).2 hInj) ((L @` S) `&` T)).
Qed.
