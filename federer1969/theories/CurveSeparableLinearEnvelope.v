(** Federer (1969), 2.9.22, p. 167: since im(g) is separable, pass to its
    closed separable linear span. Separability of the image follows from
    2.5.16, p. 110, already proved in CurveImageSeparable.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets cardinality
  reals topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric CurveArcLength CurveImageSeparable
  ClosedLinearSpanUP ClosedLinearSpanSealed MetricSubsetBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [curve_separable_linear_envelope]: direct
    supporting closed separable-span reduction in Federer
    2.9.22, p. 167. A curve of locally finite variation
    has its entire image in a closed separable linear
    subspace. The proof uses only the sealed closed-span
    laws and the already proved image-separability estimate. *)
Theorem curve_separable_linear_envelope (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> real_norm_metric_space hN) :
  curve_locally_finite_variation g ->
  exists Z : subspace E, is_separable_linear_envelope (range g) Z.
Proof.
move=> hg.
have [D [hDc [hDi hnear]]] := @curve_image_separable R
  [the metricType R of real_norm_metric_space hN] g hg.
pose Z := ClosedLinearSpan.value D.
have hZ := ClosedLinearSpan.laws D.
exists Z; split; first exact: closed_linear_span_closed hZ.
split; last exact: ClosedLinearSpan.countable_separable hDc.
move=> y hy.
apply (closed_linear_span_closed hZ).
move=> U /metricType_numDomainType.nbhs_mdistP [e he hball].
have [z [hz hdist]] := hnear y hy e he.
exists z; split; first exact: closed_linear_span_contains hZ z hz.
exact: hball z hdist.
Qed.
