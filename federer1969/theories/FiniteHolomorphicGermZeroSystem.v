(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: original
    finite analytic equations determine a variety germ whose
    ideal contains every defining germ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import HolomorphicUP FiniteAnalyticVarietyUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric HolomorphicGermRepresentatives HolomorphicGermUP
  SetGermUP FiniteHolomorphicVarietyUP FiniteZeroSetSealed HolomorphicVarietyGermUP
  HolomorphicGermVanishingUP HolomorphicGermVanishingSealed HolomorphicGermVanishingRepresentative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ZeroSystem.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation P:=(@holomorphic_representative_type R X NX hNX a).
Local Notation value:=(@holomorphic_representative_value R X NX hNX a).
Local Notation germ:=(@holomorphic_germ R X NX hNX a).
Local Notation sgerm:=(@set_germ T a).

(** Source for [finite_holomorphic_germ_zero_system_variety]: the
    actual finite analytic zero set has an analytic variety
    germ at every point of its domain, 3.4.5, p. 320. *)
Lemma finite_holomorphic_germ_zero_system_variety (I:finType) (f:I->P) (U:set X):
  U a ->@open T U ->
  (forall i,@is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) U (value (f i))) ->
  @is_holomorphic_variety_germ R X NX hNX a
    (sgerm (@FiniteZeroSet.value [the zmodType of (ComplexScalars.C R)^o] X U I (fun i=>value (f i)))).
Proof.
move=>ha hU hf.
exists U,(@FiniteZeroSet.value [the zmodType of (ComplexScalars.C R)^o] X U I (fun i=>value (f i))).
split;first exact:ha.
split;last reflexivity.
split;first exact:hU.
exists I,(fun i=>value (f i));split;first exact:hf.
exact:(original_zero_set_membership (FiniteZeroSet.laws U _)).
Qed.

(** Source for [finite_holomorphic_germ_zero_system_generators_vanish]:
    every original defining germ vanishes on the original
    zero-system germ, 3.4.5, p. 320. *)
Lemma finite_holomorphic_germ_zero_system_generators_vanish (I:finType) (f:I->P) (U:set X):
  U a ->@open T U ->forall i,
  @HolomorphicSetIdeal.value R X NX hNX a
    (sgerm (@FiniteZeroSet.value [the zmodType of (ComplexScalars.C R)^o] X U I (fun i=>value (f i)))) (germ (f i)).
Proof.
move=>ha hU i;apply/(holomorphic_set_ideal_representative_equation _ _).
exists U;split;first exact:hU.
split;first exact:ha.
move=>x hZero hx.
have [_ hAll]:=(original_zero_set_membership (FiniteZeroSet.laws U (fun i=>value (f i))) x).1 hZero.
exact:hAll i.
Qed.
End ZeroSystem.
