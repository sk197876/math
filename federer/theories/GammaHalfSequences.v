(** Federer (1969), 3.2.13, p. 251: positive Gamma
    factors indexed by half-integers and their real exponent shifts,
    for the finite product formula for projection constants. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra.
From Federer Require Import EulerGamma EulerGammaHalfParameters ProjectionBetaOneGamma
  SphereCoordinateParameters SphereCoordinateMoment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euler_gamma_equal_parameters]: identical positive
    parameters give identical Gamma values, supporting reindexing of
    the Gamma factors in Federer 3.2.13, p. 251. *)
Lemma euler_gamma_equal_parameters (R:realType) (s t:R) (hs:0<s) (ht:0<t):
  s=t ->euler_gamma hs=euler_gamma ht.
Proof.
move=>he; move:ht; rewrite -he=>ht; exact:euler_gamma_proof_irrelevant.
Qed.

(** Source for [gamma_half_sequence]: Gamma((j+1)/2),
    the positive half-integer factors in Federer 3.2.13, p. 251. *)
Definition gamma_half_sequence (R:realType) (j:nat):R:=
  euler_gamma (@positive_dimension_half R j.+1 (ltn0Sn j)).

(** Source for [gamma_shifted_half_sequence]: Gamma((t+j+1)/2),
    the shifted factors in the beta_t product of Federer
    3.2.13, p. 251, evaluated only in the printed range t>=1. *)
Definition gamma_shifted_half_sequence (R:realType) (t:R) (ht:1<=t) (j:nat):R:=
  euler_gamma (@positive_coordinate_moment_denominator R j.+1 t (ltn0Sn j) (projection_moment_range ht)).

(** Source for [gamma_half_sequence_positive]: all unshifted
    Gamma factors in the projection product are strictly positive,
    Federer 3.2.13, p. 251. *)
Lemma gamma_half_sequence_positive (R:realType) j:0<gamma_half_sequence R j.
Proof. exact:euler_gamma_positive. Qed.

(** Source for [gamma_shifted_half_sequence_positive]: all shifted
    Gamma factors are positive for finite t>=1,
    Federer 3.2.13, p. 251. *)
Lemma gamma_shifted_half_sequence_positive (R:realType) (t:R) (ht:1<=t) j:
  0<gamma_shifted_half_sequence ht j.
Proof. exact:euler_gamma_positive. Qed.

(** Source for [gamma_half_sequence_zero]: the first unshifted
    factor is Gamma(1/2), Federer 3.2.13, p. 251. *)
Lemma gamma_half_sequence_zero (R:realType):gamma_half_sequence R 0=euler_gamma_half R.
Proof. exact:euler_gamma_proof_irrelevant. Qed.

(** Source for [gamma_shifted_half_sequence_zero]: the first shifted
    factor is Gamma((t+1)/2), Federer 3.2.13, p. 251. *)
Lemma gamma_shifted_half_sequence_zero (R:realType) (t:R) (ht:1<=t):
  gamma_shifted_half_sequence ht 0=euler_gamma (positive_coordinate_moment_parameter (projection_moment_range ht)).
Proof. exact:euler_gamma_proof_irrelevant. Qed.

(** Source for [gamma_shifted_half_sequence_one]: at exponent
    t=1, shifted factors advance by one index,
    giving the final telescoping formula in Federer 3.2.13, p. 251. *)
Lemma gamma_shifted_half_sequence_one (R:realType) (ht:(1:R)<=1) j:
  gamma_shifted_half_sequence ht j=gamma_half_sequence R j.+1.
Proof.
apply:euler_gamma_equal_parameters.
have hCast:((j.+1%:R:R)+1)=j.+2%:R by rewrite natr1.
by rewrite addrC hCast.
Qed.
