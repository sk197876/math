(** Federer (1969), 3.1.11, p. 222: the actual differentials
    of a composite agree through order k with those of the composed
    jets. This is the analytic step before the multinomial calculation. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP SymmetricForms PolynomialFunctions PolynomialTaylor
  PolynomialCompositionMap ContinuousMultilinearUP NormHigherDifferentialUP
  NormClassHigherUP NormClassHigherComposition NormJetUP NormLittleOPower
  NormJetCompositionRemainder NormPolynomialApproximationDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_composition_jet_differential_coefficients]:
    D^i(g composed with f)(a)=D^i(Q composed with P)(a) for i<=k,
    the coefficient comparison in Federer 3.1.11, p. 222.
    The domain is exactly A intersect f inverse(B). *)
Theorem norm_composition_jet_differential_coefficients (R : realType)
    (X Y T : lmodType R) (NX : X->R) (NY : Y->R) (NT : T->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) (hNT : is_real_norm NT)
    (Z W U : nat->lmodType R)
    (ez : forall i, {ffun 'I_i->X}->Hom (Z i) Y) (ZN : forall i, Z i->R)
    (ew : forall i, {ffun 'I_i->Y}->Hom (W i) T) (WN : forall i, W i->R)
    (eu : forall i, {ffun 'I_i->X}->Hom (U i) T) (UN : forall i, U i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ez i) (@ZN i))
    (hW : forall i, is_continuous_multilinear_space NY NT (@ew i) (@WN i))
    (hU : forall i, is_continuous_multilinear_space NX NT (@eu i) (@UN i))
    (A : X->Prop) (B : Y->Prop) (f : X->Y) (g : Y->T) k a
    (P : PolynomialFunction X Y) (Q : PolynomialFunction Y T) :
  (1<=k)%N -> A a -> B (f a) ->
  norm_class_higher NX NY ez ZN A f k ->
  norm_class_higher NY NT ew WN B g k ->
  is_norm_jet_polynomial NX ez ZN A f k a P ->
  is_norm_jet_polynomial NY ew WN B g k (f a) Q ->
  forall i, (i<=k)%N -> forall z : U i,
    has_norm_higher_differential NX eu UN
      (fun x=>A x /\ B (f x)) (fun x=>g (f x)) i a z ->
    forall u, @eu i u z=
      polynomial_taylor_coefficient (polynomial_composite (@pchar_num R) P Q)
        i a [tuple u j | j<i].
Proof.
move=>hk ha hb hf hg hP hQ i hi z hz.
have hc := @norm_class_higher_composition R X NX hNX k Y T NY NT hNY hNT
  Z W U ez ZN ew WN eu UN hZ hW hU A B f g hf hg.
have hrem v : norm_little_o_power NT
    (fun t=>g (f (a+t*:v))-polynomial_composite (@pchar_num R) P Q (a+t*:v)) k.
  exact (@norm_composition_jet_radial_remainder R X Y T NX NY NT hNX hNY hNT
    Z W ez ZN ew WN hZ hW A B f g k a P Q hk ha hb hf hg hP hQ v).
exact (@norm_polynomial_approximation_differentials R X T NX NT hNX hNT U eu UN hU
  (fun x=>A x /\ B (f x)) (fun x=>g (f x)) k a
  (polynomial_composite (@pchar_num R) P Q) (conj ha hb) hc hrem i hi z hz).
Qed.
