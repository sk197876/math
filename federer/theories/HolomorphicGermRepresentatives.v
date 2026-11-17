(** Federer (1969), 3.4.12, p. 339:
    holomorphic germs use original complex-valued functions
    on neighbourhoods of the original centre. Total values
    outside such a neighbourhood have no mathematical role. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed
  ComplexModulus ComplexScalarNorm HolomorphicUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Representatives.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Variable NX:XR->R.
Variable hNX:is_real_norm NX.
Variable a:X.
Local Notation C:=(ComplexScalars.C R).

(** Source for [holomorphic_germ_representative]: original
    complex-valued holomorphic functions near a, in the
    replacement of 3.4.5 specified by 3.4.12,
    p. 339. Neighbourhood openness follows from
    actual analyticity, rather than being assumed for a
    chosen formal power series. *)
Definition holomorphic_germ_representative:=
  {f:X->C | exists U:X->Prop,U a /\
    @is_holomorphic R X C^o NX (@complex_modulus R) hNX
      (@complex_modulus_real_norm R) U f}.

(** Source for [holomorphic_representative_type]: the
    background choice carrier of original representatives,
    supporting the local quotient in 3.4.12, p. 339. *)
Definition holomorphic_representative_type:choiceType:=
  [the choiceType of {classic holomorphic_germ_representative}].

(** Source for [holomorphic_representative_value]: retain
    the actual original represented complex-valued function,
    3.4.12, p. 339. *)
Definition holomorphic_representative_value (f:holomorphic_representative_type):X->C:=proj1_sig f.

(** Source for [holomorphic_representative_holomorphic]: every
    representative is actually holomorphic on a neighbourhood
    of the original centre, 3.4.12, p. 339. *)
Lemma holomorphic_representative_holomorphic (f:holomorphic_representative_type):
  exists U:X->Prop,U a /\
    @is_holomorphic R X C^o NX (@complex_modulus R) hNX
      (@complex_modulus_real_norm R) U (holomorphic_representative_value f).
Proof. exact:proj2_sig f. Qed.

(** Source for [holomorphic_representative_from_domain]: an
    original holomorphic function at a domain point supplies
    a representative without choosing any Taylor coefficients,
    3.4.12, p. 339. *)
Theorem holomorphic_representative_from_domain (A:X->Prop) (f:X->C):
  A a ->@is_holomorphic R X C^o NX (@complex_modulus R) hNX
    (@complex_modulus_real_norm R) A f ->
  exists p:holomorphic_representative_type,holomorphic_representative_value p=f.
Proof.
move=>ha hF;have hLocal:exists U:X->Prop,U a /\
    @is_holomorphic R X C^o NX (@complex_modulus R) hNX
      (@complex_modulus_real_norm R) U f.
  by exists A.
by exists (exist _ f hLocal).
Qed.
End Representatives.
