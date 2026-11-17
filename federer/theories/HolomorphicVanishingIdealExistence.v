(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    existence and uniqueness of the original vanishing
    ideal, specified independently by centre-value laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm RealNormUP HolomorphicGermRing HolomorphicGermValueSealed HolomorphicVanishingIdealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_vanishing_ideal_exists]: the centre
    value supplies an existence witness for the
    original local ideal used in 3.4.7, p. 325,
    and the closedness proof for 3.4.8(5), p. 328. *)
Theorem holomorphic_vanishing_ideal_exists (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a:
  exists I:set (@holomorphic_germ_ring R X NX hNX a),is_holomorphic_vanishing_ideal I.
Proof.
exists (fun alpha=>@HolomorphicGermValue.map R X NX hNX a alpha = 0%R).
by move=>alpha;split.
Qed.

(** Source for [holomorphic_vanishing_ideal_unique]: the original
    centre-value laws uniquely determine the local ideal,
    supporting the same arguments, pp. 325, 328. *)
Lemma holomorphic_vanishing_ideal_unique (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a (I J:set (@holomorphic_germ_ring R X NX hNX a)):
  is_holomorphic_vanishing_ideal I ->is_holomorphic_vanishing_ideal J ->I = J.
Proof. move=>hI hJ;apply/seteqP;split=>alpha ha;[apply/(hJ alpha);apply/(hI alpha)|apply/(hI alpha);apply/(hJ alpha)];exact:ha. Qed.
