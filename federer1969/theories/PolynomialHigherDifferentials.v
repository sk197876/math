(** Federer (1969), 3.1.11, p. 221:
    the actual higher differentials of a continuous
    polynomial are precisely the algebraic coefficient
    functions S_i defined in 1.10.4, p. 46. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  SymmetricForms SymmetricFormSum HomogeneousPolynomialFunctions PolynomialDiagonalNorm
  PolynomialFunctions PolynomialRepresentations PolynomialTaylor
  ContinuousMultilinearUP ContinuousSymmetricFormAdapter FiniteArgumentPermutation
  NormHigherDifferentialUP NormClassHigherUP NormClassInfinityPolynomial
  NormTaylorRemainderBound NormLittleOPower NormHigherDifferentialRadialIdentification
  PolynomialTaylorCoefficientContinuity PolynomialTaylorExactExpansion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section PolynomialDifferentials.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i).
Variable A : X->Prop.
Hypothesis hA : forall x, A x -> norm_domain_interior NX A x.
Variable P : PolynomialFunction X Y.
Hypothesis hP : forall m, (m<(polynomial_degree P).+1)%N ->
  norm_bounded_symmetric_form NX NY (sform_component m (polynomial_to_forms P)).

(** Source for [polynomial_higher_differential_taylor_coefficients]:
    Federer 3.1.11, p. 221:
    D^i P=S_i and all derivatives above
    the degree vanish. The supplied D is
    only an evaluation representative of the
    already defined S_i; its differentiability
    is proved using smoothness, the exact
    Chapter 1 expansion, and radial coefficient uniqueness. *)
Theorem polynomial_higher_differential_taylor_coefficients
    (D : forall i, X->Z i) :
  (forall i x u, @ev i u (D i x)=
    polynomial_taylor_coefficient P i x [tuple u j | j<i]) ->
  forall i a, A a -> has_norm_higher_differential NX ev ZN A P i a (D i a).
Proof.
move=>hD i a ha.
pose k := maxn (polynomial_degree P) i.
have hdeg : (polynomial_degree P<=k)%N := leq_maxl _ _.
have hi : (i<=k)%N := leq_maxr _ _.
have hc := @norm_class_infinity_polynomial_function R X Y NX NY hNX hNY
  Z ev ZN hZ A hA P hP.
have hsym j (_ : (j<=k)%N) s u :
    @ev j (finite_argument_permutation s u) (D j a)=@ev j u (D j a).
  rewrite !hD; exact: sform_finite_family_symmetric.
have happrox v : norm_little_o_power NY
    (fun t=>P (a+t*:v)-norm_taylor_value ev (fun j _=>D j a) a (t*:v) k) k.
  have he t : norm_taylor_value ev (fun j _=>D j a) a (t*:v) k = P (a+t*:v).
    rewrite (@polynomial_taylor_formula_any_higher_order R (@pchar_num R) X Y P k a (t*:v) hdeg)
      /norm_taylor_value.
    apply: eq_bigr=>j _.
    rewrite hD sform_polynomial_diagonal_value.
    congr (_*:polynomial_taylor_coefficient P j a _).
    apply: eq_from_tnth=>l; by rewrite !tnth_mktuple ffunE.
  move=>e heps; exists 1; split; first exact: ltr01.
  move=>t ht; rewrite he subrr (real_seminorm_zero hNY.1).
  exact: mulr_ge0 (ltW heps) (exprn_ge0 _ (normr_ge0 t)).
exact: (@norm_higher_differential_from_radial_expansion R X Y NX NY hNX hNY
  Z ev ZN hZ A P k a (fun j=>D j a) ha (hc k) hsym happrox i hi).
Qed.

(** Source for [polynomial_higher_differential_fields_exist]:
    every continuous polynomial has the complete
    family of actual higher differentials S_i,
    Federer 3.1.11, p. 221.
    Their exact evaluation laws are retained
    in the existing Chapter 1 symmetric forms. *)
Theorem polynomial_higher_differential_fields_exist :
  exists D : forall i, X->Z i,
    (forall i x u, @ev i u (D i x)=
      polynomial_taylor_coefficient P i x [tuple u j | j<i]) /\
    (forall i a, A a -> has_norm_higher_differential NX ev ZN A P i a (D i a)).
Proof.
have [D hD] := polynomial_taylor_continuous_representatives hNX hNY hZ hP.
exists D; split; first exact hD.
exact: polynomial_higher_differential_taylor_coefficients hD.
Qed.

(** Source for [polynomial_higher_differential_above_degree]:
    D^i P= 0 whenever i exceeds the
    polynomial degree, including D^(M+1) P= 0,
    Federer 3.1.11, p. 221. *)
Corollary polynomial_higher_differential_above_degree i a :
  (polynomial_degree P<i)%N -> A a ->
  has_norm_higher_differential NX ev ZN A P i a 0.
Proof.
move=>hi ha; have [D [hD hd]] := polynomial_higher_differential_fields_exist.
have he : D i a= 0.
  apply: (continuous_multilinear_extensional (@hZ i))=>u.
  by rewrite hD (@polynomial_taylor_coefficient_above_degree R (@pchar_num R) X Y P i a hi)
    sform_zeroE linear0.
by rewrite -he; exact: hd i a ha.
Qed.
End PolynomialDifferentials.
