(** Federer (1969), 3.4.12, p. 339: original holomorphic
    finite varieties are closed relative to their open domains.
    Reuse their actual real squared-modulus equation systems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed NormMetric
  FiniteHolomorphicVarietyUP HolomorphicVarietyReal FiniteAnalyticVarietyRelativeClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
(** Source for [finite_holomorphic_variety_relative_closed_form]: the
    relative closedness implicit in 3.4.10, p. 337, under
    3.4.12, p. 339. No extension outside the domain is assumed. *)
Theorem finite_holomorphic_variety_relative_closed_form (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (U S:set X):
  @is_finite_holomorphic_variety R X NX hNX U S ->
  exists C:set X,@closed (real_norm_metric_space hNX) C /\S=U `&` C.
Proof. move=>h;exact:finite_analytic_variety_relative_closed_form (holomorphic_variety_real_analytic h). Qed.
