(** Federer (1969), 3.1.24, p. 238: the
    actual differentials of the homogeneous polynomial coefficients.
    Their algebraic contractions are those of 1.10.4, p. 46;
    their differentiability follows from 3.1.11, p. 221. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearNorm
  SymmetricForms HomogeneousPolynomialFunctions PolynomialDiagonalNorm PolynomialTaylorTerms
  PolynomialTaylorTermContinuity HomogeneousTaylorHigherOrder
  ContinuousSymmetricFormAdapter FiniteArgumentPermutation NormHigherDifferentialUP
  NormHigherDifferentialUnique NormClassOneUP NormClassHigherUP NormClassHigherDerivative
  NormClassInfinityPolynomial NormTaylorRemainderBound NormLittleOPower
  NormHigherDifferentialRadialIdentification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [homogeneous_polynomial_differential_fields]: supporting
    the displayed series of D^i p_m in Federer 3.1.24,
    p. 238. Each coefficient has actual higher differential
    fields whose evaluations are precisely its Taylor contraction
    forms. Radial Taylor uniqueness proves this identification;
    the candidate forms are never assumed to be derivatives. *)
Theorem homogeneous_polynomial_differential_fields (R:realType)
    (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A:X->Prop) (hA:forall x,A x -> norm_domain_interior NX A x)
    m (phi:S_m X Y m) :
  norm_bounded_symmetric_form NX NY phi ->
  exists D:forall i,X->Z i,
    (forall i x u,@ev i u (D i x)=
      symmetric_taylor_term i phi x [tuple u j | j<i]) /\
    (forall i x,A x -> has_norm_higher_differential NX ev ZN A
      (sform_polynomial_value phi) i x (D i x)) /\
    forall i,norm_class_zero NX (@ZN i) A (D i).
Proof.
move=>hphi.
have hex i x:=@continuous_symmetric_form_representation R i X Y (Z i) NX NY
  (@ev i) (@ZN i) (hZ i) (symmetric_taylor_term i phi x)
  (@symmetric_taylor_term_bounded R X Y NX NY hNX hNY m i phi x hphi).
pose D i x:=projT1 (cid (hex i x)).
have hD i x u:=projT2 (cid (hex i x)) u.
have hc:=@norm_class_infinity_sform_polynomial R X Y NX NY hNX hNY
  Z ev ZN hZ A hA m phi hphi.
have hd i a (ha:A a):has_norm_higher_differential NX ev ZN A
    (sform_polynomial_value phi) i a (D i a).
  pose k:=maxn m i.
  have hm:(m<=k)%N:=leq_maxl _ _.
  have hi:(i<=k)%N:=leq_maxr _ _.
  have hsym j (_:(j<=k)%N) s u:
      @ev j (finite_argument_permutation s u) (D j a)= @ev j u (D j a).
    rewrite !hD; exact: sform_finite_family_symmetric.
  have happrox v:norm_little_o_power NY
      (fun t=>sform_polynomial_value phi (a+t*:v)-
        norm_taylor_value ev (fun j _=>D j a) a (t*:v) k) k.
    have he t:norm_taylor_value ev (fun j _=>D j a) a (t*:v) k=
        sform_polynomial_value phi (a+t*:v).
      rewrite (@homogeneous_polynomial_taylor_any_higher_order R (@pchar_num R) X Y m phi
        k a (t*:v) hm) /norm_taylor_value.
      apply: eq_bigr=>j _.
      rewrite hD sform_polynomial_diagonal_value.
      congr (_*:symmetric_taylor_term j phi a _).
      apply: eq_from_tnth=>l; by rewrite !tnth_mktuple ffunE.
    move=>e heps; exists 1; split; first exact ltr01.
    move=>t ht; rewrite he subrr (real_seminorm_zero hNY.1).
    exact: mulr_ge0 (ltW heps) (exprn_ge0 _ (normr_ge0 t)).
  exact (@norm_higher_differential_from_radial_expansion R X Y NX NY hNX hNY
    Z ev ZN hZ A (sform_polynomial_value phi) k a (fun j=>D j a)
    ha (hc k) hsym happrox i hi).
exists D; split; first exact hD.
split; first exact hd.
move=>i.
have [_ [G [hG hCG]]]:=hc i.
apply: (@norm_class_zero_domain_agreement R X (Z i) NX (@ZN i) A G (D i) _ hCG).
move=>x hx; exact (@norm_higher_differential_unique R X Y NX NY hNX hNY
  Z ev ZN hZ A (sform_polynomial_value phi) i x (G x) (D i x) (hG x hx) (hd i x hx)).
Qed.
