(** Federer (1969), 3.1.11, pp. 219–221:
    the last-vector contraction with successor arities. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  NormBoundedBilinearUP MultilinearSuccessorArguments MultilinearArgumentTransport
  ContinuousMultilinearLastContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [continuous_multilinear_successor_contraction_exists]:
    the bilinear contraction from degree k+1
    to degree k, supporting the polynomial
    assertions in Federer 3.1.11, p. 221.
    Only equality transport of the arity
    relates this formulation to the grouping
    convention on p. 219. *)
Theorem continuous_multilinear_successor_contraction_exists (R : realType) k
    (X Y P T : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX)
    (ep : {ffun 'I_k->X}->Hom P Y) (PN : P->R)
    (et : {ffun 'I_k.+1->X}->Hom T Y) (TN : T->R)
    (hP : is_continuous_multilinear_space NX NY ep PN)
    (hT : is_continuous_multilinear_space NX NY et TN) :
  exists C : T->X->P,
    norm_bounded_bilinear TN NX PN C /\
    forall z x u, ep u (C z x)=et (multilinear_successor_arguments u x) z.
Proof.
have hT' := continuous_multilinear_argument_transport (addn1 k) hT.
have [C [hC he]] := continuous_multilinear_last_contraction_exists hNX hP hT'.
exists C; split; first exact hC; exact he.
Qed.
