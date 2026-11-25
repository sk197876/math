(** Federer (1969), 2.4.14, p. 88: transporting signed-power dependence to
    the positively normalised functions. This supporting rescaling preserves
    the global coefficient and exact partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  RealPower SignedRealPower PartialSignedPower MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_scale_signed_dependence_normalise]: supporting
    normalisation of the equality hypothesis in Federer 2.4.14, p. 88 The
    transformed coefficient is a single real number, independent of the
    point in the domain. *)
Lemma positive_scale_signed_dependence_normalise (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q A B c : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  0 < A -> 0 < B ->
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q c f g) ->
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q
    (real_power A p*c/real_power B q) (partial_vector_scale A f) (partial_vector_scale B g)).
Proof.
move=> hA hB he.
have hPB := @real_power_strictly_positive R B q hB.
have hPB0 : real_power B q != 0 by rewrite (gt_eqF hPB).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
move=> x [a [b [ha [hb hab]]]].
exists (A*a),(B*b); split; first by exists a; split.
split; first by exists b; split.
rewrite !signed_real_power_positive_scale // hab mulrA.
by rewrite mulrA mulfVK.
Qed.
