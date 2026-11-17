(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: var(I)
    is specified by every original finite analytic generator
    family on every admissible neighbourhood. No particular
    finite generator list or representative is selected here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import HolomorphicUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric NormAnalyticUP
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing SetGermUP
  CommutativeIdealUP HolomorphicVarietyGermUP FiniteZeroSetSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_holomorphic_ideal_variety_germ]: the original
    characterization of var(I) in V_a(X), 3.4.5,
    p. 320. Existence and generator independence are
    proved separately from this specification. *)
Record is_holomorphic_ideal_variety_germ (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (I:set [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)])
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):Prop:={
  (** Source for [holomorphic_ideal_variety_germ_is_variety]: var(I)
      is an analytic variety germ, 3.4.5, p. 320. *)
  holomorphic_ideal_variety_germ_is_variety:@is_holomorphic_variety_germ R X NX hNX a alpha;
  (** Source for [holomorphic_ideal_variety_germ_original_equation]:
      every original finite generator system gives this
      same zero-set germ, 3.4.5, p. 320. *)
  holomorphic_ideal_variety_germ_original_equation:forall (J:finType)
    (f:J->@holomorphic_representative_type R X NX hNX a) (U:set X),
    U a ->@open (real_norm_metric_space hNX) U ->
    (forall j,@is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)
      U (holomorphic_representative_value (f j))) ->
    @is_generated_commutative_ideal
      [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]
      [set beta|exists j,holomorphic_germ (f j)=beta] I ->
    alpha=@set_germ (Topological.clone (real_norm_metric_space hNX) _) a
      (@FiniteZeroSet.value [the zmodType of (ComplexScalars.C R)^o] X U J (fun j=>holomorphic_representative_value (f j)))
}.
