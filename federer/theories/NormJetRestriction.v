(** Federer (1969), 3.1.11, p. 221:
    jet laws are local on the original domain.
    These consequences use only the abstract jet
    specification and exact higher-differential graphs. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP PolynomialFunctions
  ContinuousMultilinearUP ContinuousMultilinearZero
  NormHigherDifferentialUP NormHigherDifferentialLocal
  NormTaylorRemainderBound NormJetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_zero_jet_value]:
    the zeroth jet is the constant polynomial
    with value f(a), Federer 3.1.11,
    p. 221, with D^0 f=f. *)
Lemma norm_zero_jet_value (R : realType)
    (X Y : lmodType R) (NX : X->R)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (A : X->Prop) (f : X->Y) a (P : PolynomialFunction X Y) :
  is_norm_jet_polynomial NX ev ZN A f 0%N a P ->
  forall x, P x=f a.
Proof.
move=>hP x; have [D [hD he]] := norm_jet_polynomial_expansion hP.
rewrite he /norm_taylor_value big_ord1 /= invr1 scale1r.
rewrite (zero_arity_arguments_unique [ffun i : 'I_0=>x-a] [ffun i : 'I_0=>(0:X)]).
exact: (hD 0%N (leqnn _)).2.
Qed.

(** Source for [norm_jet_open_restriction]:
    a jet is unchanged on passing to
    an open restriction containing its base point,
    supporting the derivative-jet identity and uniform
    remainder in Federer 3.1.11, p. 221. *)
Theorem norm_jet_open_restriction (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A O : X->Prop) (f : X->Y) k a (P : PolynomialFunction X Y) :
  (forall x, O x -> A x) ->
  (forall x, O x -> norm_domain_interior NX O x) ->
  O a ->
  (is_norm_jet_polynomial NX ev ZN A f k a P <->
   is_norm_jet_polynomial NX ev ZN O f k a P).
Proof.
move=>hOA hopen ha.
split=>hP; constructor; try exact: norm_jet_polynomial_degree hP;
  have [D [hD he]] := norm_jet_polynomial_expansion hP;
  exists D; split; try exact he; move=>i hi.
- exact: (@norm_higher_differential_open_restriction R X Y NX NY hNX hNY
    Z ev ZN hZ i A O f hOA hopen a ha (D i)).1 (hD i hi).
- exact: (@norm_higher_differential_open_restriction R X Y NX NY hNX hNY
    Z ev ZN hZ i A O f hOA hopen a ha (D i)).2 (hD i hi).
Qed.
