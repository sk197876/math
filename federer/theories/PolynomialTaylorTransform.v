(** Federer (1969), 1.10.4, pp. 46-47: Taylor expansion and translation of
    its coefficients. The finite contraction formula constructs the
    translated form. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp functions.
From Federer Require Import Graded GradedSums Hom HomogeneousHom BoundedHom
  SymmetricForms SymmetricFormIsomorphism SymmetricFormSum
  HomogeneousPolynomialFunctions SymmetricPolynomialEvaluation
  SymmetricPolynomialInjectivity PolynomialRepresentations PolynomialTaylorTerms PolynomialTaylorCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Transform.
Variable K : fieldType.
Variables V W : lmodType K.
Local Notation A := (S_star V W).
Local Notation G := (S_star_grading V W).

(** Source for [sform_finite_sum_component]: Federer 1.10.4,
    p. 46, supporting extraction of a coefficient from a
    finite homogeneous representation. *)
Lemma sform_finite_sum_component N (f : forall i, S_m V W i) i :
  (i<N)%N -> sform_component i (\sum_(j < N) sform_include (f j)) = f i.
Proof.
move=> hi; apply: (can_inj (@sform_includeK K V W i)).
rewrite sform_componentK linear_sum.
under eq_bigr do rewrite sform_include_grade.
rewrite -big_mkcond.
rewrite (big_pred1 (Ordinal hi)); first by [].
move=> j.
change ((i == val j) = (j == (Ordinal hi : 'I_N))).
by rewrite -val_eqE /= eq_sym.
Qed.

(** Source for [sform_finite_sum_bound]: Federer 1.10.4,
    p. 46, a sum of forms of degrees less than N has
    no component of degree at least N. *)
Lemma sform_finite_sum_bound N (f : forall i, S_m V W i) :
  grade_bounded G (\sum_(j < N) sform_include (f j)) N.
Proof.
move=> i hi; rewrite linear_sum; apply: big1=> j _.
rewrite sform_include_grade.
have hij : i != j by rewrite neq_ltn (leq_trans (ltn_ord j) hi) orbT.
by rewrite (negbTE hij).
Qed.

(** Source for [symmetric_taylor_on]: Federer 1.10.4,
    p. 46, the graded form whose components are the displayed
    S_i(x), using an explicit upper support bound N. *)
Definition symmetric_taylor_on (f : A) N x : A :=
  \sum_(i < N) sform_include (taylor_coefficient N (fun m => sform_component m f) i x).

(** Source for [symmetric_taylor_on_component]: Federer 1.10.4,
    p. 46, the i-th component is exactly the finite
    contraction sum that defines S_i(x). *)
Lemma symmetric_taylor_on_component f N i x : (i<N)%N ->
  sform_component i (symmetric_taylor_on f N x) =
    taylor_coefficient N (fun m => sform_component m f) i x.
Proof.
exact: (@sform_finite_sum_component N
  (fun j => taylor_coefficient N (fun m => sform_component m f) j x) i).
Qed.

(** Source for [symmetric_taylor_on_bound]: Federer 1.10.4,
    p. 46, translation does not add terms above the given
    maximum degree in the Taylor representation. *)
Lemma symmetric_taylor_on_bound f N x : grade_bounded G (symmetric_taylor_on f N x) N.
Proof.
exact: (@sform_finite_sum_bound N
  (fun j => taylor_coefficient N (fun m => sform_component m f) j x)).
Qed.

(** Source for [symmetric_taylor_on_value]: Federer 1.10.4,
    p. 46, Taylor's formula: the polynomial of the
    contraction coefficients has value P(x+v) at v. *)
Theorem symmetric_taylor_on_value (h0 : [pchar K] =i pred0) f N x v :
  grade_bounded G f N ->
  symmetric_polynomial_value (symmetric_taylor_on f N x) v =
    symmetric_polynomial_value f (x+v).
Proof.
move=> hf; rewrite /symmetric_taylor_on symmetric_polynomial_value_sum.
under eq_bigr do rewrite symmetric_polynomial_value_include.
rewrite (symmetric_polynomial_value_bound _ hf).
exact: esym (@polynomial_taylor_collected K V W N
  (fun m => sform_component m f) h0 x v).
Qed.

(** Source for [symmetric_taylor_transform]: Federer 1.10.4,
    pp. 46-47, the translated graded coefficient form.
    Existence of a finite support bound has already been proved. *)
Definition symmetric_taylor_transform (f : A) x : A :=
  symmetric_taylor_on f (grade_bound G f) x.

(** Source for [symmetric_taylor_transform_value]: Federer
    1.10.4, p. 46, the defining translation identity
    for the polynomial represented by the new coefficient form. *)
Theorem symmetric_taylor_transform_value (h0 : [pchar K] =i pred0) f x v :
  symmetric_polynomial_value (symmetric_taylor_transform f x) v =
    symmetric_polynomial_value f (x+v).
Proof.
apply: (@symmetric_taylor_on_value h0 f (grade_bound G f) x v).
exact: (@grade_boundP K A G f).
Qed.

(** Source for [symmetric_taylor_bound_independent]: Federer
    1.10.4, p. 46, uniqueness of polynomial coefficients
    shows that the contraction construction does not depend on the
    chosen upper support bound. *)
Lemma symmetric_taylor_bound_independent (h0 : [pchar K] =i pred0) f N x :
  grade_bounded G f N -> symmetric_taylor_on f N x = symmetric_taylor_transform f x.
Proof.
move=> hf; apply: (@symmetric_polynomial_injective K h0 V W); apply: funext=> v.
by rewrite (@symmetric_taylor_on_value h0 f N x v hf) (symmetric_taylor_transform_value h0).
Qed.

(** Source for [symmetric_taylor_transform_bound]: Federer
    1.10.4, p. 46, the translated representation retains
    every valid upper bound for the original coefficient degrees. *)
Lemma symmetric_taylor_transform_bound (h0 : [pchar K] =i pred0) f N x :
  grade_bounded G f N -> grade_bounded G (symmetric_taylor_transform f x) N.
Proof.
move=> hf; rewrite -(@symmetric_taylor_bound_independent h0 f N x hf).
exact: symmetric_taylor_on_bound.
Qed.

(** Source for [symmetric_taylor_transform_component]: Federer
    1.10.4, p. 46, the contraction formula for every
    coefficient, with both sides zero above the finite degree bound. *)
Lemma symmetric_taylor_transform_component (h0 : [pchar K] =i pred0) f N i x :
  grade_bounded G f N ->
  sform_component i (symmetric_taylor_transform f x) =
    taylor_coefficient N (fun m => sform_component m f) i x.
Proof.
move=> hf; case hi: (i<N)%N.
- rewrite -(@symmetric_taylor_bound_independent h0 f N x hf).
  exact: symmetric_taylor_on_component hi.
- have hNi : (N<=i)%N by rewrite leqNgt hi.
  have hz : sform_component i (symmetric_taylor_transform f x)=0.
    apply: (can_inj (@sform_includeK K V W i)).
    rewrite linear0 sform_componentK.
    exact: (@symmetric_taylor_transform_bound h0 f N x hf) i hNi.
  rewrite hz /taylor_coefficient; symmetry; apply: big1=> m hm.
  have him : (i<N)%N := leq_ltn_trans hm (ltn_ord m).
  by move: him; rewrite hi.
Qed.

(** Source for [symmetric_taylor_transform_add]: Federer
    1.10.4, pp. 46-47, the coefficient translation
    identity. Translating first by x and then by v equals translation
    by x+v; uniqueness proves the identity without infinite sums. *)
Theorem symmetric_taylor_transform_add (h0 : [pchar K] =i pred0) f x v :
  symmetric_taylor_transform (symmetric_taylor_transform f x) v =
    symmetric_taylor_transform f (x+v).
Proof.
apply: (@symmetric_polynomial_injective K h0 V W); apply: funext=> w.
by rewrite !(symmetric_taylor_transform_value h0) addrA.
Qed.

(** Source for [symmetric_taylor_coefficient_translation]:
    Federer 1.10.4, pp. 46-47, the displayed equation
    expressing S_i(x+v) as the sum of contractions of S_m(x)
    with v^(m-i)/(m-i)!, for i<=m<N. *)
Theorem symmetric_taylor_coefficient_translation (h0 : [pchar K] =i pred0)
    f N i x v : grade_bounded G f N -> (i<N)%N ->
  sform_component i (symmetric_taylor_transform f (x+v)) =
    taylor_coefficient N
      (fun m => sform_component m (symmetric_taylor_transform f x)) i v.
Proof.
move=> hf hi; rewrite -(symmetric_taylor_transform_add h0).
have hb := symmetric_taylor_transform_bound h0 x hf.
rewrite -(symmetric_taylor_bound_independent h0 v hb).
exact: symmetric_taylor_on_component hi.
Qed.
End Transform.
