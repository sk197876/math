(** Federer (1969), 3.4.12, p. 339, extending the ideal-closedness proof for Federer
    (1969), 3.4.8(5), p. 328: the maximal ideal
    consists of original germs whose centre value is
    zero. These membership laws precede existence. The
    centre-value criterion for units was proved in
    3.4.7, p. 325. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm RealNormUP HolomorphicGermRing HolomorphicGermValueSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_holomorphic_vanishing_ideal]: membership is
    exactly vanishing at the original centre, the
    local ideal underlying 3.4.7, p. 325, and
    the expanded closedness argument for 3.4.8(5), p. 328.
    Neither closedness nor an adic description is included. *)
Definition is_holomorphic_vanishing_ideal (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a
  (I:set (@holomorphic_germ_ring R X NX hNX a)):Prop:=
  forall alpha,I alpha <->@HolomorphicGermValue.map R X NX hNX a alpha = 0%R.
