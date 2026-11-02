(** Federer (1969), 3.1.11, p. 221:
    public consequences of the abstract kth-jet
    laws. The private construction is not imported. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP SymmetricFormSum
  PolynomialFunctions PolynomialRepresentations
  ContinuousMultilinearUP ContinuousSymmetricFormAdapter FiniteArgumentPermutation
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialSymmetry
  NormClassHigherUP NormClassInfinityPolynomial NormTaylorRemainderBound
  NormLittleOPower NormHigherDifferentialRadialIdentification
  NormJetUP NormJetUnique NormJetSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section JetLaws.
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
Variable f : X->Y.
Variables k : nat.
Variable a : X.
Variable P : PolynomialFunction X Y.
Hypothesis hP : is_norm_jet_polynomial NX ev ZN A f k a P.

(** Source for [norm_jet_coefficients_bounded]:
    every jet satisfying the abstract laws has
    continuous coefficient forms, Federer 3.1.11,
    p. 221. Uniqueness transfers this
    property from the proved sealed witness. *)
Theorem norm_jet_coefficients_bounded i :
  norm_bounded_symmetric_form NX NY (sform_component i (polynomial_to_forms P)).
Proof.
have [D [hD he]] := norm_jet_polynomial_expansion hP.
pose hz := hD k (leqnn k).
pose Q := @NormJet.value R X Y NX NY hNX hNY Z ev ZN hZ A f k a (D k) hz.
have hQ := @NormJet.laws R X Y NX NY hNX hNY Z ev ZN hZ A f k a (D k) hz.
have hPQ := norm_jet_polynomial_unique hNX hNY hZ hP hQ.
rewrite hPQ.
exact: @NormJet.coefficient_bound R X Y NX NY hNX hNY Z ev ZN hZ A f k a (D k) hz i.
Qed.

(** Source for [norm_jet_class_infinity]:
    the kth jet is a smooth polynomial
    on the entire source space, Federer
    3.1.11, p. 221. Only
    the original function's kth differential at
    a is needed for the jet laws. *)
Theorem norm_jet_class_infinity :
  norm_class_infinity NX NY ev ZN (fun _=>True) P.
Proof.
have hopen x (_ : True) : norm_domain_interior NX (fun _=>True) x.
  exists 1; split; first exact: ltr01; by move=>v hv.
apply: (@norm_class_infinity_polynomial_function R X Y NX NY hNX hNY
  Z ev ZN hZ (fun _=>True) hopen P)=>i _.
exact: norm_jet_coefficients_bounded.
Qed.

(** Source for [norm_jet_differential_at_base]:
    the jet has exactly the original
    differentials through order k at its base
    point, Federer 3.1.11, p. 221.
    The conclusion is a statement about the
    actual recursive differential on the whole source space. *)
Theorem norm_jet_differential_at_base i (z : Z i) :
  (i<=k)%N ->
  has_norm_higher_differential NX ev ZN A f i a z ->
  has_norm_higher_differential NX ev ZN (fun _=>True) P i a z.
Proof.
move=>hi hz; have [D [hD hPe]] := norm_jet_polynomial_expansion hP.
have hsym j (hj : (j<=k)%N) s u :
    @ev j (finite_argument_permutation s u) (D j)=@ev j u (D j).
  exact (@norm_higher_differential_symmetric R X Y NX NY hNX hNY Z ev ZN hZ A f j a (D j) (hD j hj) s u).
have happrox v : norm_little_o_power NY
    (fun t=>P (a+t*:v)-norm_taylor_value ev (fun j _=>D j) a (t*:v) k) k.
  move=>e he; exists 1; split; first exact: ltr01.
  move=>t ht; rewrite hPe [a+t*:v-a]addrAC subrr add0r subrr (real_seminorm_zero hNY.1).
  exact: mulr_ge0 (ltW he) (exprn_ge0 _ (normr_ge0 t)).
have hd := @norm_higher_differential_from_radial_expansion R X Y NX NY hNX hNY
  Z ev ZN hZ (fun _=>True) P k a D I
  (norm_jet_class_infinity k) hsym happrox i hi.
have he := norm_higher_differential_unique hNX hNY hZ (hD i hi) hz.
by rewrite -he.
Qed.
End JetLaws.
