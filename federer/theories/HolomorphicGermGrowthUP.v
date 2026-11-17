(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: factorial
    derivative-growth classes, specified by their exact membership law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermOperationsUP RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  HolomorphicGermUP HolomorphicGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_jet_norm]: the actual norm
    of D^m(alpha) in the metric and growth classes of
    3.4.5, p. 319; degree zero is included. *)
Definition holomorphic_germ_jet_norm (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) m (alpha:holomorphic_germ_space hNX a):R:=
  @ContinuousMultilinear.norm R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)
    (@HolomorphicGermJets.value R X NX hNX a m alpha).
Arguments holomorphic_germ_jet_norm {R X NX hNX a} m alpha.

(** Source for [is_holomorphic_germ_growth_class]: the exact
    subset defined by all bounds ||D^m(alpha)||<=s*t^m*m!
    in 3.4.5, p. 319. The membership specification
    precedes existence; it asserts no closedness or compactness.
    The book uses positive integer s and t in its covering theorem. *)
Record is_holomorphic_germ_growth_class (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) (s t:nat)
    (C:set (holomorphic_germ_space hNX a)):Prop:={
  (** Source for [holomorphic_germ_growth_membership]: the original
      all-order factorial bounds, 3.4.5, p. 319. *)
  holomorphic_germ_growth_membership:forall alpha,C alpha <->
    forall m,holomorphic_germ_jet_norm m alpha<=s%:R*t%:R^+m*(m`!)%:R
}.
