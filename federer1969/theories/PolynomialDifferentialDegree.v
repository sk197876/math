(** Federer (1969), 3.1.11, p. 221:
    differentiating a continuous polynomial p times
    lowers its degree by p. The polynomial
    representative is specified by equality with the
    actual differential field, not by an implementation. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  PolynomialFunctions PolynomialRepresentations SymmetricFormSum
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousSymmetricFormAdapter
  MultilinearArguments NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialLocal NormHigherDifferentialIterated
  NormClassHigherUP NormClassHigherDerivative NormClassInfinityPolynomial
  PolynomialHigherDifferentials NormTaylorRemainderBound NormFiniteOrderTaylorExact
  NormJetUP NormJetSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section PolynomialDerivative.
Variable R : realType.
Variables p q : nat.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable ez : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ez i) (@ZN i).
Variable W : nat->lmodType R.
Variable ew : forall i, {ffun 'I_i->X}->Hom (W i) (Z p).
Variable WN : forall i, W i->R.
Hypothesis hW : forall i, is_continuous_multilinear_space NX (@ZN p) (@ew i) (@WN i).
Variable P : PolynomialFunction X Y.
Hypothesis hP : forall i, (i<(polynomial_degree P).+1)%N ->
  norm_bounded_symmetric_form NX NY (sform_component i (polynomial_to_forms P)).
Variable G : X->Z p.
Hypothesis hG : forall x,
  has_norm_higher_differential NX ez ZN (fun _=>True) P p x (G x).

(** Source for [polynomial_differential_field_smooth]:
    all differentials of a continuous polynomial are
    smooth, Federer 3.1.11, p. 221.
    The theorem applies to any representative of
    the actual pth differential. *)
Theorem polynomial_differential_field_smooth :
  norm_class_infinity NX (@ZN p) ew WN (fun _=>True) G.
Proof.
have hopen x (_ : True) : norm_domain_interior NX (fun _=>True) x.
  exists 1; split; first exact: ltr01; by move=>v hv.
have hcP := @norm_class_infinity_polynomial_function R X Y NX NY hNX hNY
  Z ez ZN hZ (fun _=>True) hopen P hP.
move=>k.
apply: (@norm_class_higher_derivative_field R p k X Y NX NY hNX hNY
  Z ez ZN hZ W ew WN hW (fun _=>True) P G (hcP (p+k)%N)).
by move=>x _; exact: hG.
Qed.

(** Source for [polynomial_differential_field_above_degree]:
    D^(q+1)(D^p P)= 0 if degree P is
    at most p+q, Federer 3.1.11,
    p. 221. The grouping identity retains
    the exact recursive domains. *)
Theorem polynomial_differential_field_above_degree :
  (polynomial_degree P<=p+q)%N ->
  forall a, has_norm_higher_differential NX ew WN (fun _=>True) G q.+1 a 0.
Proof.
move=>hdeg a.
have hopen x (_ : True) : norm_domain_interior NX (fun _=>True) x.
  exists 1; split; first exact: ltr01; by move=>v hv.
have hlt : (polynomial_degree P<p+q.+1)%N by rewrite addnS ltnS.
have hz := @polynomial_higher_differential_above_degree R X Y NX NY hNX hNY
  Z ez ZN hZ (fun _=>True) hopen P hP (p+q.+1)%N a hlt I.
have hrep x z :
    has_norm_higher_differential NX ez ZN (fun _=>True) P p x z -> G x=z.
  move=>hz0; exact (norm_higher_differential_unique hNX hNY hZ (hG x) hz0).
have [w [hw he]] := (@norm_higher_differential_iterated R p q.+1
  X Y NX NY hNX hNY Z ez ZN hZ W ew WN hW
  (fun _=>True) P G a 0 hrep).1 hz.
have hw0 : w= 0.
  apply: (continuous_multilinear_extensional (@hW q.+1))=>v.
  rewrite linear0; apply: (continuous_multilinear_extensional (@hZ p))=>u.
  by rewrite he !linear0.
pose B x := exists z, has_norm_higher_differential NX ez ZN (fun _=>True) P p x z.
have hB x (_ : True) : B x by exists (G x); exact: hG.
have hr := @norm_higher_differential_open_restriction R X (Z p) NX (@ZN p)
  hNX (continuous_multilinear_norm_is_norm hNY (@hZ p)) W ew WN hW
  q.+1 B (fun _=>True) G hB hopen a I w.
by rewrite -hw0; exact: hr.1 hw.
Qed.

(** Source for [polynomial_differential_polynomial_exists]:
    D^p P is a continuous polynomial of
    degree at most q if degree P<=p+q,
    Federer 3.1.11, p. 221. Its
    polynomial representative is its q-jet at
    any prescribed point; uniqueness follows from
    the existing polynomial-function extensionality. *)
Theorem polynomial_differential_polynomial_exists a :
  (polynomial_degree P<=p+q)%N ->
  exists Q : PolynomialFunction X (Z p),
    is_norm_jet_polynomial NX ew WN (fun _=>True) G q a Q /\
    forall x, Q x=G x.
Proof.
move=>hdeg.
have hNp := continuous_multilinear_norm_is_norm hNY (@hZ p).
have hc := polynomial_differential_field_smooth.
have [_ [F [hF hFc]]] := hc q.
pose hz := hF a I.
pose Q := @NormJet.value R X (Z p) NX (@ZN p) hNX hNp
  W ew WN hW (fun _=>True) G q a (F a) hz.
have hQ := @NormJet.laws R X (Z p) NX (@ZN p) hNX hNp
  W ew WN hW (fun _=>True) G q a (F a) hz.
have [D [hD hT]] := @norm_finite_order_taylor_exact R X (Z p) NX (@ZN p)
  hNX hNp W ew WN hW G q (hc q.+1)
  (polynomial_differential_field_above_degree hdeg).
exists Q; split; first exact hQ.
have [E [hE he]] := norm_jet_polynomial_expansion hQ.
move=>x; rewrite he.
have htx := hT a (x-a).
have hax : a+(x-a)=x by rewrite addrC subrK.
rewrite hax in htx.
rewrite htx /norm_taylor_value.
apply: eq_bigr=>i _.
have hi : (i<=q)%N by move:(ltn_ord i); rewrite ltnS.
have hd := norm_higher_differential_unique hNX hNp hW (hE i hi) (hD i hi a).
by rewrite hd.
Qed.
End PolynomialDerivative.
