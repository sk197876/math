(** Federer (1969), 3.1.11, p. 222:
    replacing both factors by their jets preserves
    every product differential through the chosen order. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Hom Bilinear RealNormUP NormClassOneUP
  SymmetricForms PolynomialFunctions PolynomialTaylor SymmetricPolynomialProduct
  ContinuousMultilinearUP NormClassHigherUP NormClassHigherBilinear
  NormHigherDifferentialUP NormBoundedBilinearUP NormJetUP NormJet
  NormLittleOPower NormLittleOBilinear NormJetLineRemainder
  NormPolynomialApproximationDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ProductOfJets.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i).
Variable mu : Y->Y->Y.
Hypothesis hmu : bilinear mu.
Hypothesis hM : forall x y, NY (mu x y)<=NY x*NY y.
Variables (A : X->Prop) (f g : X->Y) (k : nat) (a : X).
Variables P Q : PolynomialFunction X Y.
Hypothesis ha : A a.
Hypothesis hf : norm_class_higher NX NY ev ZN A f k.
Hypothesis hg : norm_class_higher NX NY ev ZN A g k.
Hypothesis hP : is_norm_jet_polynomial NX ev ZN A f k a P.
Hypothesis hQ : is_norm_jet_polynomial NX ev ZN A g k a Q.

(** Source for [norm_product_jet_radial_remainder]:
    the first displayed limit in Federer
    3.1.11, p. 222, along
    each fixed line. The local bounds
    used in multiplying the remainders follow
    from continuity and the proved jet smoothness. *)
Lemma norm_product_jet_radial_remainder v :
  norm_little_o_power NY
    (fun t=>mu (f (a+t*:v)) (g (a+t*:v))-
      polynomial_product hmu P Q (a+t*:v)) k.
Proof.
have [M [r [hM0 [hr hgb]]]] := norm_class_zero_line_bounded hNX hNY v ha hg.1.
have hPc := (norm_jet_class_infinity hNX hNY hZ hP 0%N).1.
have [L [s [hL [hs hPb]]]] := @norm_class_zero_line_bounded R X Y NX NY hNX hNY (fun _=>True) P a v I hPc.
have hfO := norm_jet_line_little_o hNX hNY hZ ha hf hP v.
have hgO := norm_jet_line_little_o hNX hNY hZ ha hg hQ v.
have hprod : forall x y, NY (mu x y)<= 1*NY x*NY y.
  by move=>x y; rewrite mul1r; exact: hM.
have hh := @norm_product_of_approximations_remainder R Y Y Y NY NY NY hNY hNY hNY
  mu hmu 1 (fun t=>f (a+t*:v)) (fun t=>P (a+t*:v))
  (fun t=>g (a+t*:v)) (fun t=>Q (a+t*:v)) k M L r s
  ler01 hprod hM0 hr (fun t ht=>(hgb t ht).2)
  hL hs (fun t ht=>(hPb t ht).2) hfO hgO.
move=>e he; have [d [hd hb]] := hh e he.
exists d; split=> // t ht.
rewrite (@polynomial_productE R (@pchar_num R) X Y mu hmu).
exact: hb.
Qed.

(** Source for [norm_product_jet_differential_coefficients]:
    the differentials of f g through
    order k equal the polynomial product
    coefficients of their jets, Federer 3.1.11,
    p. 222. This is the
    analytic step of the general Leibniz formula. *)
Theorem norm_product_jet_differential_coefficients i (z : Z i) :
  (i<=k)%N ->
  has_norm_higher_differential NX ev ZN A (fun x=>mu (f x) (g x)) i a z ->
  forall u, @ev i u z=
    polynomial_taylor_coefficient (polynomial_product hmu P Q) i a [tuple u j | j<i].
Proof.
move=>hi hz.
have hB : norm_bounded_bilinear NY NY NY mu.
  split; first exact hmu.
  exists 1; split; first exact: ler01.
  by move=>x y; rewrite mul1r; exact: hM.
have hc := @norm_class_higher_bilinear R X NX hNX k Y Y Y NY NY NY
  hNY hNY hNY Z Z Z ev ZN ev ZN ev ZN hZ hZ hZ A f g mu hB hf hg.
exact: (@norm_polynomial_approximation_differentials R X Y NX NY hNX hNY
  Z ev ZN hZ A (fun x=>mu (f x) (g x)) k a (polynomial_product hmu P Q)
  ha hc norm_product_jet_radial_remainder i hi z hz).
Qed.
End ProductOfJets.
