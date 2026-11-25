(** Federer (1969), 2.6.5, p. 120, final induction on dimension. Taylor's
    formula from 1.10.4, p. 46, supplies polynomial coefficients after
    splitting off a line. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import SymmetricForms HomogeneousPolynomialFunctions PolynomialFunctions
  PolynomialRepresentations PolynomialTaylor PolynomialCoefficientUniqueness PolynomialLinearComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [sform_polynomial_evaluate]: supporting fixed-vector
    evaluation of the coefficient forms S_i in Federer 1.10.4,
    p. 46, used to extract the scalar-variable coefficients
    for 2.6.5, p. 120. *)
Definition sform_polynomial_evaluate (K : fieldType) (V W : lmodType K) m (e : V)
    (f : S_m V W m) := sform_polynomial_value f e.

(** Source for [sform_polynomial_evaluate_linear]: supporting
    linearity in the form of the same evaluation, Federer
    1.10.4, pp. 45–46; used in 2.6.5, p. 120. *)
Lemma sform_polynomial_evaluate_linear (K : fieldType) (V W : lmodType K) m (e : V) :
  linear (@sform_polynomial_evaluate K V W m e).
Proof. by move=> a f g; rewrite /sform_polynomial_evaluate linearP. Qed.
HB.instance Definition _ (K : fieldType) (V W : lmodType K) m (e : V) :=
  GRing.isLinear.Build K (S_m V W m) W *:%R
    (@sform_polynomial_evaluate K V W m e) (sform_polynomial_evaluate_linear e).

Section Slices.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variables U V W : lmodType K.
Variable P : PolynomialFunction V W.
Variable g : {linear U -> V}.
Variable e : V.

(** Source for [polynomial_slice_coefficient]: supporting
    coefficient of t^i in P(g(u)+t e), from Federer
    1.10.4, p. 46, for the induction in 2.6.5, p. 120. *)
Definition polynomial_slice_coefficient i (u : U) :=
  sform_polynomial_value (polynomial_taylor_coefficient P i (g u)) e.

(** Source for [polynomial_slice_coefficient_polynomial]:
    each slice coefficient is itself polynomial, by the
    polynomial nature of S_i in Federer 1.10.4, p. 46;
    this justifies the smaller-dimensional induction in
    2.6.5, p. 120, rather than assuming it. *)
Lemma polynomial_slice_coefficient_polynomial i :
  is_polynomial_function (polynomial_slice_coefficient i).
Proof.
apply: (@polynomial_linear_postcompose K U (S_m V W i) W
  (GRing.Linear.clone _ _ _ _ (@sform_polynomial_evaluate K V W i e) _)).
apply: polynomial_linear_precompose.
exact (@polynomial_taylor_coefficient_is_polynomial K h0 V W P i).
Qed.

(** Source for [polynomial_slice_expansion]: supporting
    one-variable expansion used by Federer 2.6.5, p. 120,
    obtained from the Taylor formula of 1.10.4, p. 46.
    The bound includes the constant term for every polynomial. *)
Lemma polynomial_slice_expansion u t :
  P (g u + t *: e) = \sum_(i < (polynomial_degree P).+1)
    t^+i *: polynomial_slice_coefficient i u.
Proof.
rewrite (polynomial_taylor_formula h0).
by apply: eq_bigr=> i _; rewrite sform_polynomial_scale_argument.
Qed.

(** Source for [polynomial_slice_list]: finite coefficient
    list for the local univariate root-count theorem, supporting
    Federer 2.6.5, p. 120, from 1.10.4, p. 46. *)
Definition polynomial_slice_list u :=
  [seq polynomial_slice_coefficient i u | i <- iota 0 (polynomial_degree P).+1].

(** Source for [polynomial_slice_horner]: the same finite
    expansion in Horner form for the project's root-count
    argument, supporting Federer 2.6.5, p. 120. *)
Lemma polynomial_slice_horner u t :
  coefficient_polynomial_value (polynomial_slice_list u) t = P (g u + t *: e).
Proof.
rewrite coefficient_polynomial_sum /polynomial_slice_list size_map size_iota polynomial_slice_expansion.
apply: eq_bigr=> i _.
by rewrite (nth_map 0) ?size_iota ?ltn_ord // nth_iota ?ltn_ord // add0n.
Qed.

(** Source for [polynomial_slice_nonzero_coefficient]: the
    nonzero coefficient needed to apply the dimension induction
    of Federer 2.6.5, p. 120. A nonzero value on a
    slice prevents every coefficient function from vanishing. *)
Lemma polynomial_slice_nonzero_coefficient :
  (exists u t, P (g u + t *: e) <> 0) ->
  exists i, (i < (polynomial_degree P).+1)%N /\ exists u, polynomial_slice_coefficient i u <> 0.
Proof.
move=> [u [t hP]]; apply: contrapT=> hn; apply: hP.
rewrite polynomial_slice_expansion; apply: big1=> i _.
have hz : polynomial_slice_coefficient i u = 0.
  apply: contrapT=> hz; apply: hn; exists i; split; first exact: ltn_ord.
  by exists u.
by rewrite hz scaler0.
Qed.
End Slices.
