(** Sealed harmonic-prefix witness supporting Federer (1969),
    2.8.20, p. 152, through Cesari1939 Lemma III,
    p. 306. Reuse the already proved private harmonic
    construction supporting 2.4.10, without exposing it to
    downstream proofs. The specification is HarmonicPrefixUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import HarmonicPrefixUP HarmonicWeightsConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type HarmonicPrefixSignature.
(** Source for [value]: abstract finite harmonic sums for
    the cutoff supporting Federer 2.8.20, p. 152;
    Cesari1939 Lemma III, p. 306. *)
Parameter value : forall R : realType, nat -> R.
(** Source for [laws]: proved harmonic-prefix laws supporting
    Federer 2.8.20, p. 152; HarmonicPrefixUP.v. *)
Parameter laws : forall R : realType, is_harmonic_prefix (@value R).
End HarmonicPrefixSignature.
Module HarmonicPrefix : HarmonicPrefixSignature.
(** Source for [value]: reuse of the existing proved harmonic
    witness for the cutoff supporting Federer 2.8.20,
    p. 152; Cesari1939 Lemma III, p. 306. *)
Definition value (R : realType) := @harmonic_prefix R.
(** Source for [laws]: the reused witness satisfies the
    abstract specification supporting Federer 2.8.20, p. 152.
    The dyadic estimate was proved by elementary finite sums. *)
Lemma laws (R : realType) : is_harmonic_prefix (@value R).
Proof.
constructor; first by move=> N.
exact: harmonic_power_prefix_bound.
Qed.
End HarmonicPrefix.
