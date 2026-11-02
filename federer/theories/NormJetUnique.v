(** Federer (1969), 3.1.11, p. 221:
    the exact higher-differential laws uniquely
    determine the kth jet polynomial. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  PolynomialFunctions NormHigherDifferentialUnique NormTaylorRemainderBound NormJetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_jet_polynomial_unique]:
    the polynomial F_a defined by the
    Taylor sum is unique, supporting the
    jet definition in Federer 3.1.11, p. 221.
    Equality follows from the actual coefficient
    graphs, not from any implementation of the jet. *)
Theorem norm_jet_polynomial_unique (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) k a (P Q : PolynomialFunction X Y) :
  is_norm_jet_polynomial NX ev ZN A f k a P ->
  is_norm_jet_polynomial NX ev ZN A f k a Q -> P=Q.
Proof.
move=>hP hQ.
have [D [hD hPe]] := norm_jet_polynomial_expansion hP.
have [E [hE hQe]] := norm_jet_polynomial_expansion hQ.
apply: polynomial_function_ext=>x.
rewrite hPe hQe /norm_taylor_value.
apply: eq_bigr=>i _.
have hi : (i<=k)%N by move:(ltn_ord i); rewrite ltnS.
have he := norm_higher_differential_unique hNX hNY hZ (hD i hi) (hE i hi).
by rewrite he.
Qed.
