(** Federer (1969), 3.4.12, p. 339, extending 3.4.11, p. 338:
    independent laws for the first nonzero homogeneous
    Taylor polynomial of an original holomorphic germ.
    No tangent vanishing or dimension conclusion is
    included in the specification. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  HolomorphicGermUP HolomorphicGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_initial_holomorphic_germ_polynomial]: the
    least positive nonzero derivative order and its exact
    factorial-normalized homogeneous Taylor polynomial in 3.4.11,
    p. 338, stated using the original opaque jets. *)
Definition is_initial_holomorphic_germ_polynomial (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    (alpha:holomorphic_germ_space hNX (0:X)) k (P:X->ComplexScalars.C R):Prop:=
  (0<k)%N /\@HolomorphicGermJets.value R X NX hNX 0 k alpha<>0 /\
  (forall i,(i<k)%N ->@HolomorphicGermJets.value R X NX hNX 0 i alpha=0) /\
  forall v,P v=((k`!)%:R:R)^-1*:@ContinuousMultilinear.evaluation R k
    (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX
    (@complex_modulus R) hNX (@complex_modulus_real_norm R) [ffun _=>v]
    (@HolomorphicGermJets.value R X NX hNX 0 k alpha).
