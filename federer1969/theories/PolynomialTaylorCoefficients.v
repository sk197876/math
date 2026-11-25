(** Federer (1969), 1.10.4, p. 46: the Taylor coefficient forms S_i and
    their polynomial nature. Bounds are explicit here; independence of the
    representing bound follows from polynomial uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded GradedSums Hom HomogeneousHom BoundedHom
  SymmetricForms SymmetricFormIsomorphism SymmetricFormSum
  HomogeneousPolynomialFunctions SymmetricPolynomialEvaluation PolynomialFunctions
  PolynomialRepresentations PolynomialTaylorTerms PolynomialTaylorTermPolynomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [taylor_triangular_sum]: Federer 1.10.4,
    p. 46, supporting interchange of the two finite sums
    in Taylor's formula. No convergence or ordering hypothesis is needed. *)
Lemma taylor_triangular_sum (R : zmodType) N (F : nat -> nat -> R) :
  \sum_(m < N) \sum_(i < m.+1) F m i =
    \sum_(i < N) \sum_(m < N | (i<=m)%N) F m i.
Proof.
transitivity (\sum_(m < N) \sum_(i < N) (if (i<=m)%N then F m i else 0)).
- apply: eq_bigr=> m _.
  rewrite (big_ord_widen N (fun i => F m i) (ltn_ord m)) big_mkcond.
  by apply: eq_bigr=> i _; rewrite ltnS.
- rewrite exchange_big; apply: eq_bigr=> i _; by rewrite [RHS]big_mkcond.
Qed.

Section Coefficients.
Variable K : fieldType.
Variables V W : lmodType K.
Variable N : nat.
Variable f : forall m, S_m V W m.

(** Source for [taylor_coefficient]: Federer 1.10.4,
    p. 46, the displayed definition S_i(x), summing
    contractions of phi_m with x^(m-i)/(m-i)! for i<=m<N. *)
Definition taylor_coefficient i (x : V) : S_m V W i :=
  \sum_(m < N | (i<=m)%N) symmetric_taylor_term i (f m) x.

(** Source for [taylor_coefficient_value]: Federer 1.10.4,
    p. 46, evaluating S_i on v^i/i! distributes
    over its finite contraction sum. *)
Lemma taylor_coefficient_value i x v :
  sform_polynomial_value (taylor_coefficient i x) v =
    \sum_(m < N | (i<=m)%N)
      sform_polynomial_value (symmetric_taylor_term i (f m) x) v.
Proof.
rewrite /taylor_coefficient.
elim/big_ind2: _=> [|a b c d ha hb|m hm].
- by rewrite (linear0 (@sform_polynomial_value K V W i)).
- rewrite linearD.
  change (sform_polynomial_value b v + sform_polynomial_value d v = a+c).
  by rewrite ha hb.
- by [].
Qed.

(** Source for [taylor_coefficient_representation]: Federer
    1.10.4, p. 46, a finite graded form representing
    S_i as a polynomial with values in the i-form space. *)
Definition taylor_coefficient_representation i : S_star V (S_m V W i) :=
  \sum_(m < N | (i<=m)%N) sform_include (taylor_term_representing_form i (f m)).

(** Source for [taylor_coefficient_representationE]: Federer
    1.10.4, p. 46, the representing polynomial has
    precisely the values S_i(x) specified by the contraction sum. *)
Lemma taylor_coefficient_representationE i x :
  symmetric_polynomial_value (taylor_coefficient_representation i) x = taylor_coefficient i x.
Proof.
rewrite /taylor_coefficient_representation /taylor_coefficient.
elim/big_ind2: _=> [|a b c d ha hb|m hm].
- by rewrite (linear0 (@symmetric_polynomial_value K V (S_m V W i))).
- rewrite linearD.
  change (symmetric_polynomial_value b x + symmetric_polynomial_value d x = a+c).
  by rewrite ha hb.
- rewrite symmetric_polynomial_value_include.
  exact: taylor_term_representing_formE.
Qed.

(** Source for [taylor_coefficient_polynomial]: Federer
    1.10.4, p. 46, the explicit assertion that S_i
    is a polynomial function from V to the space of symmetric i-forms. *)
Theorem taylor_coefficient_polynomial i : is_polynomial_function (taylor_coefficient i).
Proof.
exists (taylor_coefficient_representation i)=> x.
exact: esym (taylor_coefficient_representationE i x).
Qed.

(** Source for [polynomial_taylor_collected]: Federer
    1.10.4, p. 46, the last equality in the Taylor
    display: collect equal powers of v and use the coefficient forms S_i. *)
Theorem polynomial_taylor_collected (h0 : [pchar K] =i pred0) x v :
  \sum_(m < N) sform_polynomial_value (f m) (x+v) =
    \sum_(i < N) sform_polynomial_value (taylor_coefficient i x) v.
Proof.
under eq_bigr do rewrite (homogeneous_polynomial_taylor h0).
rewrite (@taylor_triangular_sum W N (fun m i =>
  sform_polynomial_value (symmetric_taylor_term i (f m) x) v)).
apply: eq_bigr=> i _; exact: esym (taylor_coefficient_value i x v).
Qed.
End Coefficients.
