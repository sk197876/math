(** Federer (1969), 2.4.14, p. 88: undoing the positive normalisations in
    the signed-power equality criterion. The supporting coefficient
    transformation is global and preserves exact partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  RealPower SignedRealPower PartialSignedPower MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_scale_signed_dependence_transfer]: supporting
    rescaling of the dependence coefficient in Federer 2.4.14, proof p. 88
    The coefficient may be negative or zero; only the two normalising
    scalars must be positive. *)
Lemma positive_scale_signed_dependence_transfer (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q A B c : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  0 < A -> 0 < B ->
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q c
    (partial_vector_scale A f) (partial_vector_scale B g)) ->
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q
    ((real_power A p)^-1*c*real_power B q) f g).
Proof.
move=> hA hB he.
have hPA := @real_power_strictly_positive R A p hA.
have hPA0 : real_power A p != 0 by rewrite (gt_eqF hPA).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
move=> x [a [b [[u [hu hua]] [[v [hv hvb]] hab]]]].
change (A*u=a) in hua.
change (B*v=b) in hvb.
have hnum : real_power A p * signed_real_power p u =
    c * (real_power B q * signed_real_power q v).
  rewrite -!signed_real_power_positive_scale //; by rewrite hua hvb.
have hcancel := congr1 (fun t => (real_power A p)^-1*t) hnum.
rewrite !mulrA mulVf // mul1r in hcancel.
exists u,v; split=> //; split=> //.
by rewrite /signed_real_power !mulrA.
Qed.
