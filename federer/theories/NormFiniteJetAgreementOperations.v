(** Federer (1969), 3.4.5, pp. 318–321: finite
    actual jet agreement is local, symmetric, transitive and
    retained at lower orders. These supporting laws use
    the exact higher differential graphs of 3.1.11, p. 219. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP NormDifferentialUP
  NormHigherDifferentialUP NormHigherDifferentialLocal NormFiniteJetAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Operations.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable Z:nat->lmodType R.
Variable ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y.
Variable NZ:forall i,Z i->R.
Hypothesis hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@NZ i).
Local Notation Agree:=(@norm_finite_jet_agreement R X Y NX Z ev NZ).

(** Source for [norm_finite_jet_agreement_symmetric]: symmetry
    of equality of actual jets, supporting 3.4.5, pp. 318–321. *)
Lemma norm_finite_jet_agreement_symmetric (A B:X->Prop) (f g:X->Y) k a:
  Agree A B f g k a ->Agree B A g f k a.
Proof. by move=>h i hi z;exact:iff_sym (h i hi z). Qed.

(** Source for [norm_finite_jet_agreement_transitive]: transitivity
    of actual jet agreement, supporting 3.4.5, pp. 318–321. *)
Lemma norm_finite_jet_agreement_transitive (A B C:X->Prop) (f g h:X->Y) k a:
  Agree A B f g k a ->Agree B C g h k a ->Agree A C f h k a.
Proof.
move=>hFG hGH i hi z;split=>hz.
- exact:(hGH i hi z).1 ((hFG i hi z).1 hz).
- exact:(hFG i hi z).2 ((hGH i hi z).2 hz).
Qed.

(** Source for [norm_finite_jet_agreement_lower]: agreement
    at every smaller finite order, supporting 3.4.5, pp. 318–321. *)
Lemma norm_finite_jet_agreement_lower (A B:X->Prop) (f g:X->Y) k l a:
  (l<=k)%N ->Agree A B f g k a ->Agree A B f g l a.
Proof. by move=>hLK h i hi;exact:(h i (leq_trans hi hLK)). Qed.

(** Source for [norm_finite_jet_agreement_local]: actual
    local equality on an original open neighbourhood gives
    equality of every finite jet, supporting 3.4.5, pp. 318–321. *)
Lemma norm_finite_jet_agreement_local (A B O:X->Prop) (f g:X->Y) k a:
  (forall x,O x ->norm_domain_interior NX O x) ->
  (forall x,O x ->(A x <->B x)) ->
  (forall x,O x ->A x ->f x=g x) ->O a ->Agree A B f g k a.
Proof.
move=>hOpen hDomains hValues ha i hi z.
exact:(@norm_higher_differential_local_agreement R X Y NX NY hNX hNY Z ev NZ hZ
  i A B O f g hOpen hDomains hValues a ha z).
Qed.
End Operations.
