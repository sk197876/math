(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), pp. 334–335:
    local containment in a holomorphic variety
    persists under closure inside the chosen open
    neighbourhood. Use the proved relatively closed
    representative of the original finite equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicUP RealNormUP NormMetric FiniteHolomorphicVarietyUP
  HolomorphicVarietyReal FiniteAnalyticVarietyClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_holomorphic_variety_local_closure]:
    the original containment of the regular closure
    in its holomorphic variety, used before choosing
    the nested radii, 3.4.12, p. 339, extending 3.4.8(11), p. 334.
    Containment is needed only on the original
    open neighbourhood, not on the whole ambient space. *)
Theorem finite_holomorphic_variety_local_closure (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (U S W Z:set X):
  @is_finite_holomorphic_variety R X NX hNX U S ->
  @open (real_norm_metric_space hNX) W ->W `<=` U ->
  (forall x,Z x ->W x ->S x) ->
  W `&` @closure (real_norm_metric_space hNX) Z `<=` S.
Proof.
move=>hVariety hW hWU hZS.
exact:(@finite_analytic_variety_local_closure R (restricted_space (ComplexScalars.embed R) X)
  NX hNX U S W Z (holomorphic_variety_real_analytic hVariety) hW hWU hZS).
Qed.
