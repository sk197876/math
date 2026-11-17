(** Federer (1969), 3.4.12, p. 339, extending 3.4.7,
    p. 325: original centre-value vanishing equals zeroth-jet
    vanishing for every actual holomorphic germ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermRingLaws HolomorphicGermValueSealed HolomorphicGermJetsSealed HolomorphicGermZerothVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_value_zeroth_jet]: the original
    value criterion, including source dimension zero, 3.4.12, p. 339. *)
Lemma holomorphic_germ_value_zeroth_jet (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a
    (alpha:@holomorphic_germ_ring R X NX hNX a):
  @HolomorphicGermValue.map R X NX hNX a alpha=0 <->
  @HolomorphicGermJets.value R X NX hNX a 0%N alpha=0.
Proof.
have [f <-]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
rewrite (@HolomorphicGermValue.laws R X NX hNX a f).
exact:holomorphic_germ_zeroth_vanishing.
Qed.
