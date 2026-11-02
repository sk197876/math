(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import Exterior.
From Federer Require Import SimpleVectors SimpleCovectors DualityBoundary
  AnnihilatorIntersection IntersectionDuality SimplePairingDeterminant.
From Federer Require Import ProductSpaceIdentity ProductContractionAlgebra
  ProductAdaptedWords ProductMissingCovector ProductSpaceMaps.
From FedererTests Require Import Examples.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Regression test for Federer 1.3.1: an alternating coordinate pairing
    detects a nonzero exterior product. This tests the quotient itself,
    including that imposing all generating squares does not collapse it. *)
Section AlternatingPairing.
Variable K : fieldType.
Variable V : lmodType K.
Variable b : V -> V -> K^o.
Hypotheses (hb : bilinear b) (hs : forall v, b v v = 0).

(** Source for [alternating_two_word]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Local regression example for this passage; the
    example itself is not stated in the book. *)
Definition alternating_two_word (s : seq V) : K^o :=
  if s is [:: v; w] then b v w else 0.
(** Source for [alternating_two_word_multilinear]: Federer (1969), 1.3.1, p.
    13, polarisation identity and the concluding signed-interchange formula.
    In words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Local regression example for this passage; the
    example itself is not stated in the book. *)
Lemma alternating_two_word_multilinear : multilinear_words alternating_two_word.
Proof.
move=> s t a v w; case: s => [|u [|u' [|u'' s]]]; case: t => [|r [|r' t]];
  rewrite /alternating_two_word /=; try by rewrite scaler0 add0r.
- exact: (proj1 hb r).
- exact: (proj2 hb u).
Qed.
(** Source for [alternating_two_tensor]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Local regression example for this passage; the
    example itself is not stated in the book. *)
Definition alternating_two_tensor : {linear tensor_algebra_space V -> K^o} :=
  multilinear_extension alternating_two_word_multilinear.
(** Source for [alternating_two_tensorE]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Local regression example for this passage; the
    example itself is not stated in the book. *)
Lemma alternating_two_tensorE s :
  alternating_two_tensor (tensor_word s) = alternating_two_word s.
Proof. exact: multilinear_extensionE. Qed.

(** Source for [alternating_two_killed]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Local regression example for this passage; the
    example itself is not stated in the book. *)
Lemma alternating_two_killed x : mV V x -> alternating_two_tensor x = 0.
Proof.
elim=> [|u v hu ihu hv ihv|a u hu ihu|s t v].
- exact: linear0.
- by rewrite linearD ihu ihv add0r.
- rewrite linearZ ihu; change (a * (0 : K) = 0); exact: mulr0.
rewrite alternating_two_tensorE /alternating_two_word.
by case: s => [|u [|u' [|u'' s]]]; case: t => [|r t] => //; exact: hs.
Qed.
(** Source for [alternating_two_word_alternating]: Federer (1969), 1.3.1, p.
    13, polarisation identity and the concluding signed-interchange formula.
    In words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Local regression example for this passage; the
    example itself is not stated in the book. *)
Lemma alternating_two_word_alternating s : ~~ uniq s -> alternating_two_word s = 0.
Proof.
case: s => [|u [|u' [|u'' s]]] //=; rewrite /alternating_two_word.
by rewrite inE andbT negbK => /eqP ->; exact: hs.
Qed.
(** Source for [alternating_two_exterior]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Local regression example for this passage; the
    example itself is not stated in the book. *)
Definition alternating_two_exterior : {linear exterior_space V -> K^o} :=
  exterior_word_extension alternating_two_word_multilinear
    alternating_two_word_alternating.
(** Source for [alternating_two_exteriorE]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Local regression example for this passage; the
    example itself is not stated in the book. *)
Lemma alternating_two_exteriorE v w :
  alternating_two_exterior (exterior_word [:: v; w]) = b v w.
Proof. exact: exterior_word_extensionE. Qed.
End AlternatingPairing.

Section TwoIndependentVectors.
Variable K : fieldType.
Local Notation C := (Choice.clone bool _).
Local Notation V := (GRing.Lmodule.clone K (free_vector K C) _).
Local Notation c := (@coordinate_pairing K C C false true).
Local Notation cb := (@coordinate_pairing_bilinear K C C false true).

(** Source for [alternating_coordinates]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Local regression example for this passage; the
    example itself is not stated in the book. *)
Definition alternating_coordinates (u v : V) : K^o := c u v - c v u.
(** Source for [alternating_coordinates_bilinear]: Federer (1969), 1.3.1, p.
    13, polarisation identity and the concluding signed-interchange formula.
    In words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Local regression example for this passage; the
    example itself is not stated in the book. *)
Lemma alternating_coordinates_bilinear : bilinear alternating_coordinates.
Proof.
split=> [v a u u'|u a v v']; rewrite /alternating_coordinates
  (bilDl cb) (bilDr cb) (bilZl cb) (bilZr cb) scalerBr opprD addrACA;
  by [].
Qed.
(** Source for [alternating_coordinates_square]: Federer (1969), 1.3.1, p.
    13, polarisation identity and the concluding signed-interchange formula.
    In words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Local regression example for this passage; the
    example itself is not stated in the book. *)
Lemma alternating_coordinates_square v : alternating_coordinates v v = 0.
Proof. exact: subrr. Qed.
(** Source for [exterior_coordinate]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Local regression example for this passage; the
    example itself is not stated in the book. *)
Definition exterior_coordinate : {linear exterior_space V -> K^o} :=
  alternating_two_exterior alternating_coordinates_bilinear alternating_coordinates_square.
(** Source for [exterior_coordinate_basis]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Local regression example for this passage; the
    example itself is not stated in the book. *)
Lemma exterior_coordinate_basis :
  exterior_coordinate (exterior_word [:: delta K false; delta K true]) = 1.
Proof.
rewrite /exterior_coordinate alternating_two_exteriorE
  /alternating_coordinates /coordinate_pairing !deltaE /=.
by rewrite mulr1 mulr0 subr0.
Qed.

(** Source for [exterior_two_vector_nonzero]: Federer (1969), 1.3.1, p. 13,
    polarisation identity and the concluding signed-interchange formula. In
    words: Expanding the square of x+y gives y wedge x = -x wedge y;
    interchanging blocks of p and q vectors gives the sign (-1)^(pq), hence
    graded anticommutativity. Local regression example for this passage; the
    example itself is not stated in the book. *)
Example exterior_two_vector_nonzero :
  exterior_word [:: delta K false; delta K true] != 0.
Proof.
apply/eqP=> h; have e := exterior_coordinate_basis.
rewrite h linear0 in e.
by move: e; apply/eqP; rewrite eq_sym oner_eq0.
Qed.
End TwoIndependentVectors.

Section SimpleCovectorBoundaries.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.

(** Source for [empty_intersection_basis]: Federer 1.6.3, p. 25,
    intersection corollary. Regression fixture: the empty products
    have the zero associated subspace, whose intersection has an
    empty basis. This does not depend on the ambient dimension. *)
Definition empty_intersection_basis (V : lmodType K) (_ : 'I_0) :
  subspace_space (subspace_intersection
    (FedererSimple.T (exterior_zeroth_inclusion V 1))
    (FedererSimple.T (exterior_zeroth_inclusion V 1))) := 0.

(** Source for [empty_intersection_basisP]: Federer 1.6.3, p. 25,
    intersection corollary. Supporting proof that the regression
    fixture is a basis of the actual intersection, not a dimension
    assumed as an extra hypothesis. *)
Lemma empty_intersection_basisP (V : lmodType K) : is_basis (empty_intersection_basis V).
Proof.
apply: finite_basis_criterion.
- move=> c hc i; by have := ltn_ord i; rewrite ltn0.
- move=> v; exists (fun _ => 0); rewrite big_ord0.
  apply: val_inj; change (subspace_val v = 0).
  have hs := proj1 (subspace_valP v).
  exact: (proj1 (@scalar_associated_zero K V 1 (oner_neq0 K) (subspace_val v)) hs).
Qed.

(** Source for [intersection_negative_expected_dimension]: Federer
    1.6.3, p. 25, dimension equation. Regression with n=1 and p=r=0:
    the intersection has dimension zero but the dual product vanishes.
    This detects the incorrect use of truncated natural subtraction
    in place of the book's integer p+r-n. *)
Example intersection_negative_expected_dimension :
  let V := coordinate_space K 1 in
  let e := @coordinate_basis K 1 in
  let he := coordinate_basisP K 1 in
  let ot := omega_lambda h2 (fun i => one_form (dual_basis he i)) (Lambda_top 1) in
  let xi := exterior_zeroth_inclusion V 1 in
  form_wedge h2 (scalar_bilinear K)
    (D_p ot (leq0n 1) xi) (D_p ot (leq0n 1) xi) = 0.
Proof.
move=> V e he ot xi; apply/eqP; apply/negPn/negP=> hz.
have hx : xi != 0 := @scalar_mvector_nonzero K V 1 (oner_neq0 K).
have hs : simple xi by apply/simple_zero_iff.
have hh := proj2 (@intersection_dimension_iff_dual_product K h2 V 1 e he
  0 0 (leq0n 1) (leq0n 1) xi xi hx hx hs hs 0
  (empty_intersection_basis V) (empty_intersection_basisP V)) hz.
by [].
Qed.

(** Source for [intersection_zero_dimensional]: Federer 1.6.3,
    p. 25, intersection corollary. Regression for n=p=r=0: the
    product of the duals of the empty products is nonzero. *)
Example intersection_zero_dimensional :
  let V := coordinate_space K 0 in
  let e := @coordinate_basis K 0 in
  let he := coordinate_basisP K 0 in
  let ot := omega_lambda h2 (fun i => one_form (dual_basis he i)) (Lambda_top 0) in
  let xi := exterior_zeroth_inclusion V 1 in
  form_wedge h2 (scalar_bilinear K)
    (D_p ot (leq0n 0) xi) (D_p ot (leq0n 0) xi) != 0.
Proof.
pose V := coordinate_space K 0.
pose e := @coordinate_basis K 0.
pose he := coordinate_basisP K 0.
pose xi := exterior_zeroth_inclusion V 1.
have hx : xi != 0 := @scalar_mvector_nonzero K V 1 (oner_neq0 K).
have hs : simple xi by apply/simple_zero_iff.
apply: (proj1 (@intersection_dimension_iff_dual_product K h2 V 0 e he
  0 0 (leq0n 0) (leq0n 0) xi xi hx hx hs hs 0
  (empty_intersection_basis V) (empty_intersection_basisP V))).
by [].
Qed.
End SimpleCovectorBoundaries.

Section SimplePairingBoundary.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable e : 'I_0 -> V.
Variable alpha : 'I_0 -> A_m V K^o 1.

(** Source for [simple_pairing_empty_determinant]: Federer 1.6.4,
    p. 25, pairing/determinant identity. Regression for the empty
    product in any ambient space: the associated endomorphism has
    determinant one, although its carrier is the zero subspace. *)
Example simple_pairing_empty_determinant (hx : e_lambda e (ord_tuple 0) != 0) :
  det h2 (@product_basisP K h2 V 0 e hx) (pairing_endomorphism e alpha) = 1.
Proof.
rewrite (det_ext h2 (@product_basisP K h2 V 0 e hx)
  (g := linear_id _)); last first.
  apply: (basis_linear_ext (@product_basisP K h2 V 0 e hx)) => i.
  by have := ltn_ord i; rewrite ltn0.
exact: det_id.
Qed.
End SimplePairingBoundary.


Section ProductSpaceBoundaries.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.

(** Source for [product_space_empty_products]: Federer 1.6.5,
    pp. 25-26, empty-product boundary of the adapted computation.
    Regression: contracting the two empty products by the empty
    volume produces the exterior unit, even in an arbitrary ambient
    space. It includes the zero-dimensional instance of the theorem. *)
Example product_space_empty_products (V : lmodType K) :
  product_contraction_hom h2
    (form_homogeneous (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o)
      (fun _ : 'I_0 => (0 : A_m V K^o 1))))
    (exterior_unit V) (exterior_unit V) =
  exterior_unit (GRing.Lmodule.clone K (V * V)%type _).
Proof.
pose z (_ : 'I_0) : V := 0.
pose omega (_ : 'I_0) : A_m V K^o 1 := 0.
have hd : forall i j, omega i [tuple concatenate_family z (concatenate_family z z) j] =
    if i == j then 1 else 0.
  by move=> i; have := ltn_ord i; rewrite ltn0.
have h := @adapted_product_contraction K h2 V 0 0 0 z z z omega hd.
rewrite /product_contraction_hom -form_pullback_hom !algebra_map_one.
by move: h; rewrite /z /omega !enum_ord0 /= scale1r.
Qed.

(** Source for [product_space_nontransverse_lines]: Federer 1.6.5,
    pp. 25-26, supporting nontransverse case. Regression in dimension
    two with k=l=1 and both factors equal to the first basis vector:
    the contraction is zero although k+l=n. *)
Example product_space_nontransverse_lines :
  let V := coordinate_space K 2 in
  let e := @coordinate_basis K 2 in
  let he := coordinate_basisP K 2 in
  let omega := fun i => one_form (dual_basis he i) in
  product_contraction_hom h2
    (form_homogeneous (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) omega))
    (exterior_word [:: e ord0]) (exterior_word [:: e ord0]) = 0.
Proof.
move=> V e he omega.
have hn : one_hom (omega ord_max) (e ord_max) = 1.
  by rewrite /omega one_homE one_formE dual_basisE eqxx.
have hz v : v \in [:: e ord0] -> one_hom (omega ord_max) v = 0.
  rewrite inE => /eqP ->.
  by rewrite /omega one_homE one_formE dual_basisE.
rewrite /product_contraction_hom -form_pullback_hom !exterior_algebra_map_word.
exact: (@product_missing_volume_factor K h2 V 2 omega ord_max (e ord_max) hn
  [:: e ord0] [:: e ord0] hz hz).
Qed.
End ProductSpaceBoundaries.

(** Federer 1.6.6 regressions: complex scalar restriction, the literal empty
    product, and orientation signs. The scalar implementation is accessed
    only through the sealed laws. see ComplexScalarUP.v. *)
From Federer Require Import ComplexScalarUP ComplexScalarSealed ComplexScalarLaws
  ComplexCharacteristic ScalarRestriction ComplexCoefficientAlgebra ComplexPairedVectors
  ComplexPairedPlanes ComplexSimpleVectors ComplexOrientation ComplexOrderedBases
  ComplexDeterminant ExteriorDeterminant.
Import Num.Theory ComplexScalarTheory.

Section ComplexRegression.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation ii := (ComplexScalars.ii R).
Variable V : lmodType C.
Local Notation VR := (restricted_space (ComplexScalars.embed R) V).

(** Source for [complex_empty_pair]: Federer 1.6.6, p. 27,
    paired representation. Regression: the empty paired product is
    the exterior unit, without assuming the ambient space is zero. *)
Example complex_empty_pair (v : 'I_0 -> V) :
  component_val (paired_complex_vector v) = exterior_unit VR.
Proof. by rewrite paired_complex_vector_word enum_ord0 /= exterior_word_nil. Qed.

(** Source for [complex_empty_pair_positive]: Federer 1.6.6,
    p. 27, positivity of a complex vector. Regression: the literal
    empty paired product has positive orientation. *)
Example complex_empty_pair_positive (v : 'I_0 -> V) :
  positive_complex_vector (paired_complex_vector v).
Proof.
have hn : paired_complex_vector v != 0.
  apply: independent_paired_vector_nonzero => c hc j.
  by have := ltn_ord j; rewrite ltn0.
split.
- split=> //; split; [exact: paired_complex_vector_simple | exact: paired_vector_complex].
- exists 0%N, v, (1:R); split=> //; split; [exact: ltr01 | by rewrite scale1r].
Qed.

(** Source for [complex_phase_rotation]: Federer 1.6.6,
    p. 27, independence of the orientation from the complex basis.
    Regression: replacing v by i v preserves the real paired area,
    because i(i v)=-v and the interchange contributes the other minus sign. *)
Example complex_phase_rotation (v : V) :
  @exterior_word R VR [:: ii *: v; ii *: (ii *: v)] =
  @exterior_word R VR [:: v; ii *: v].
Proof.
have hi : ii *: (ii *: v) = -v.
  by rewrite scalerA (complex_i_square (ComplexScalars.laws R)) scaleN1r.
rewrite hi !exterior_word_cons exterior_word_nil !wedge_unitr linearN.
rewrite -[X in wedge _ X]scaleN1r (bilZr (wedge_bilinear VR)) scaleN1r.
exact: esym (@exterior_generator_skew R VR v (ii *: v)).
Qed.

(** Source for [complex_negative_pair]: Federer 1.6.6,
    p. 27, positive versus negative complex orientation. Regression:
    negating a nonzero paired product in positive degree reverses
    positivity, while preserving complex simplicity. *)
Example complex_negative_pair p (v : 'I_p -> V) :
  (0 < p)%N -> paired_complex_vector v != 0 ->
  ~ positive_complex_vector (- paired_complex_vector v).
Proof.
move=> hp hn.
have hz : -paired_complex_vector v != 0 by rewrite oppr_eq0.
have hs : simple (-paired_complex_vector v).
  rewrite -scaleN1r; apply: simple_scale; [by rewrite addn_gt0 hp | exact: paired_complex_vector_simple].
have hr : (-1:R) != 0 by rewrite oppr_eq0 oner_neq0.
have he : component_val (-paired_complex_vector v) = (-1:R) *: component_val (paired_complex_vector v).
  by rewrite linearN scaleN1r.
have hc := paired_representation_complex hz hs (erefl (p+p)%N) hr he.
move/(positive_complex_vector_iff hc (erefl (p+p)%N) he).
by rewrite ltr0N1.
Qed.

(** Source for [complex_empty_determinant]: Federer 1.6.6,
    p. 27, real determinant equals squared complex modulus. Regression:
    in dimension zero even the zero endomorphism has determinant one,
    as required by the empty top product. *)
Example complex_empty_determinant (e : 'I_0 -> V) (he : is_basis e) (f : {linear V -> V}) :
  det (real_two_nonzero R) (ordered_real_basisP he)
    (restrict_linear (ComplexScalars.embed R) f) = 1.
Proof.
rewrite complex_real_determinant.
have hf : f =1 linear_id V.
  apply: (basis_linear_ext he f (linear_id V)) => j.
  by have := ltn_ord j; rewrite ltn0.
rewrite (det_ext (complex_two_nonzero R) he hf) det_id /norm_square
  (complex_re_one (ComplexScalars.laws R)) (complex_im_one (ComplexScalars.laws R)).
by rewrite expr1n expr0n addr0.
Qed.
End ComplexRegression.


From mathcomp Require Import reals.
From Federer Require Import InnerProductUP InnerNorm EuclideanInnerProduct
  InnerCompactness InnerBoundedness FiniteBasisCriterion FiniteSpans GrassmannAbbreviations
  OrthonormalisationUP GramSchmidt.

Section InnerProductBoundaryExamples.
Variable R : realType.
Local Notation E0 := (R_n R 0).

(** Source for [inner_empty_coordinate_basis]: Federer 1.7.1,
    p. 28, regression for the zero-dimensional case of the finite-basis
    and compactness assertions. The empty family spans R^0. *)
Lemma inner_empty_coordinate_basis : is_basis (fun _ : 'I_0 => (0 : E0)).
Proof.
apply: finite_basis_criterion.
- move=> c hc i; by have := ltn_ord i; rewrite ltn0.
- move=> x; have hx : x = 0 by apply/ffunP=> i; have := ltn_ord i; rewrite ltn0.
  rewrite hx; exact: in_finite_span_zero.
Qed.

(** Source for [inner_empty_space_compact]: Federer 1.7.1,
    p. 28, regression: the compactness equivalence includes dimension zero
    and the empty orthonormal basis, without a positive dimension assumption. *)
Example inner_empty_space_compact :
  inner_boundedly_compact (@euclidean_inner_productP R 0).
Proof.
apply: (proj2 (inner_boundedly_compact_iff_finite_basis
  (@euclidean_inner_productP R 0))).
exists 0%N, (fun _ : 'I_0 => (0 : E0)); exact: inner_empty_coordinate_basis.
Qed.

(** Source for [inner_empty_orthonormalisation]: Federer 1.7.1,
    p. 28, regression: Gram-Schmidt also accepts the empty input family
    and preserves its (empty) prefix span. *)
Example inner_empty_orthonormalisation : exists e,
  is_orthonormalisation (@euclidean_inner_product R 0)
    (fun _ : 'I_0 => (0 : E0)) e.
Proof.
apply: (@gram_schmidt_exists R E0 _ (@euclidean_inner_productP R 0)
  0 (fun _ : 'I_0 => (0 : E0))).
move=> c hc i; by have := ltn_ord i; rewrite ltn0.
Qed.
End InnerProductBoundaryExamples.


From Federer Require Import OrthogonalMaps OrthogonalEuclidean InnerDual
  InnerDualNorm InnerDualSupremum.

Section DualNormBoundaryExamples.
Variable R : realType.
Local Notation E0 := (R_n R 0).
Local Notation hB0 := (@euclidean_inner_productP R 0).
Local Notation he0 := (inner_empty_coordinate_basis R).

(** Source for [inner_zero_dual_supremum]: Federer 1.7.2,
    pp. 28-29, regression: the supremum formula for the zero covector
    in dimension zero has value zero, without a nonempty unit sphere. *)
Example inner_zero_dual_supremum :
  sup (@inner_dual_unit_values R E0 _ hB0 (0 : A_m E0 R^o 1)) = 0.
Proof.
rewrite -(@inner_dual_norm_supremum R E0 _ hB0 0 _ he0 (0 : A_m E0 R^o 1)).
exact: inner_norm0.
Qed.

(** Source for [orthogonal_empty_group_inverse]: Federer 1.7.2,
    p. 28, regression: O(0) satisfies the inverse assertion with the
    same definition as positive dimensions. *)
Example orthogonal_empty_group_inverse :
  exists g : {linear E0 -> E0},
    @FedererOrthogonal.O_group R 0 g /\
    cancel (linear_id E0) g /\ cancel g (linear_id E0).
Proof.
apply: FedererOrthogonal.O_inverse.
exact: FedererOrthogonal.O_identity.
Qed.
End DualNormBoundaryExamples.

From Federer Require Import PrincipalAxes PrincipalAxesUP TensorUP
  SkewPairUP BilinearNegation PolarInjection PolarFactorisationUP OrthonormalFamilies
  AlternatingTwoNormalForm SkewNormalFormUP.

Section PrincipalAxesRegression.
Variable R : realType.
Local Notation E0 := (R_n R 0).

(** Source for [principal_axes_empty_space]: Federer 1.7.3,
    p. 29, regression: principal axes in dimension zero use the
    empty basis, with no maximiser required on an empty unit sphere. *)
Example principal_axes_empty_space (S : E0 -> E0 -> R)
    (hS : @bilinear R E0 E0 R^o S) (hs : forall x y, S x y = S y x) :
  exists e : 'I_0 -> E0, is_principal_axes (@euclidean_inner_product R 0) S e.
Proof.
exact (@principal_axes_exists R E0 _ S (@euclidean_inner_productP R 0)
  hS hs 0 _ (inner_empty_coordinate_basis R)).
Qed.

(** Source for [skew_negative_block_orientation]: Federer
    1.7.3, pp. 29-30, regression for the sign choice: the block
    f(x)=-y, f(y)=x has coefficient one after replacing y by -y. *)
Example skew_negative_block_orientation (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) (f : {linear V -> V}) x y
    (hx : B x x = 1) (hy : B y y = 1) (hxy : B x y = 0)
    (hfx : f x = -y) (hfy : f y = x) : is_skew_pair B f x (-y) 1.
Proof.
constructor.
- exact: ler01.
- exact hx.
- by rewrite (bilNl (inner_bilinear hB)) (bilNr (inner_bilinear hB)) opprK.
- by rewrite (bilNr (inner_bilinear hB)) hxy oppr0.
- by rewrite hfx scale1r.
- by rewrite linearN hfy scaleN1r.
Qed.

(** Source for [polar_zero_map_kernel_completion]: Federer
    1.7.3, p. 30, regression for a full kernel: the factorisation
    still supplies an orthogonal injection, and its symmetric factor
    is zero on the whole source. The target need not have a finite basis. *)
Example polar_zero_map_kernel_completion (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e)
    (u : 'I_n -> U) (hu : finite_independent u)
    (f : {linear V -> U}) (hf : forall x, f x = 0) :
  exists (g : {linear V -> V}) (h : {linear V -> U}),
    is_injection_factorisation B C f g h /\ forall x, g x = 0.
Proof.
have hfo i j : i != j -> C (f (e i)) (f (e j)) = 0.
  by move=> _; rewrite !hf (bil0l (inner_bilinear hC)).
have [g [h [hgh [hg hh]]]] := @polar_injection_prescribed_basis R V U B C
  hB hC n e he ho u hu f hfo.
exists g, h; split; first exact hgh.
apply: (basis_induction he) => [|x y hx hy|a x hx|i].
- exact: linear0.
- by rewrite linearD hx hy addr0.
- rewrite linearZ hx; change (a *: (0 : V) = 0); exact: scaler0.
- rewrite hg hf inner_norm0; change ((0 : R) *: e i = 0); exact: scale0r.
Qed.

(** Source for [alternating_empty_space_normal_form]: Federer
    1.7.3, pp. 29-30, regression: the normal-form existence
    theorem applies to every two-form in dimension zero, using the
    same dual-product and wedge definitions as in positive dimension. *)
Example alternating_empty_space_normal_form (phi : A_m E0 R^o 2) :
  exists m (a b : 'I_m -> A_m E0 R^o 1) (lambda : 'I_m -> R),
    orthonormal_family
      (inner_dual_product (@euclidean_inner_productP R 0) (inner_empty_coordinate_basis R))
      (paired_family a b) /\
    (forall i, 0 <= lambda i) /\
    phi = \sum_i lambda i *: form_wedge (real_two_nonzero R) (scalar_bilinear R) (a i) (b i).
Proof.
exact (@alternating_two_form_normal_form R (real_two_nonzero R) E0 _
  (@euclidean_inner_productP R 0) 0 _ (inner_empty_coordinate_basis R) phi).
Qed.
End PrincipalAxesRegression.

From Federer Require Import CoordinateProjection InitialIndices.

Section CoordinateProjectionRegression.
Variable R : realFieldType.

(** Source for [coordinate_projection_empty_target]: Federer
    1.7.4, p. 31, regression: selecting no coordinates gives
    the unique vector in R^0, for every source dimension. *)
Example coordinate_projection_empty_target n (x : R_n R n) :
  coordinate_projection (Lambda_initial (leq0n n)) x = 0.
Proof. apply/ffunP=> i; by have := ltn_ord i; rewrite ltn0. Qed.

(** Source for [first_third_coordinates]: Federer 1.7.4,
    p. 31, regression index selecting the first and third coordinates
    in R^3, leaving out the middle coordinate. *)
Definition first_third_coordinates : Lambda 3 2.
Proof. exists [tuple (ord0 : 'I_3); (ord_max : 'I_3)]; by []. Defined.

(** Source for [coordinate_projection_skips_middle]: Federer
    1.7.4, p. 31, regression: the concrete selection (1,3)
    sends (x1,x2,x3) to (x1,x3), checking order and omitted indices. *)
Example coordinate_projection_skips_middle (x : R_n R 3) :
  coordinate_projection first_third_coordinates x =
    [ffun i : 'I_2 => if i == ord0 then x ord0 else x ord_max].
Proof.
apply/ffunP=> i.
case: i => i hi.
rewrite coordinate_projectionE /first_third_coordinates !ffunE.
case: i hi => [|[|i]] hi //=; congr (x _); exact: val_inj.
Qed.
End CoordinateProjectionRegression.

From Federer Require Import InnerExterior InnerExteriorLowDegrees ExteriorNorm
  ExteriorHadamardCorrection ExteriorProductFactors.

Section ExteriorMetricRegression.
Variable R : rcfType.
Local Notation h2 := (real_two_nonzero R).

(** Source for [exterior_empty_space_unit_norm]: Federer 1.7.5, p. 32,
    regression for the empty product in the zero-dimensional space. Its
    induced norm is one, although the underlying space has only the zero
    vector. *)
Example exterior_empty_space_unit_norm :
  exterior_norm h2 (@euclidean_inner_productP R 0)
    (e_lambda (fun _ : 'I_0 => (0 : R_n R 0)) (ord_tuple 0)) = 1.
Proof.
apply: orthonormal_product_unit_norm => i.
by have := ltn_ord i; rewrite ltn0.
Qed.

(** Source for [exterior_empty_space_scalar_sign]: Federer 1.7.5, pp. 31-32,
    regression: the induced degree-zero product of the scalar inclusions of
    -1 and 1 is -1, also in dimension zero. *)
Example exterior_empty_space_scalar_sign :
  exterior_inner_form h2 (@euclidean_inner_productP R 0)
    (exterior_zeroth_inclusion (R_n R 0) (-1))
    (exterior_zeroth_inclusion (R_n R 0) 1) = -1.
Proof. by rewrite exterior_inner_zeroth mulr1. Qed.

(** Source for [exterior_norm_above_dimension_regression]: Federer 1.7.5, p.
    32, positive definiteness together with 1.3.2, p. 15: in dimension one
    every two-vector has norm zero. This checks that no nonempty basis is
    assumed for the induced inner product. *)
Example exterior_norm_above_dimension_regression
    (x : exterior_power (R_n R 1) 2) :
  exterior_norm h2 (@euclidean_inner_productP R 1) x = 0.
Proof.
have hx := @exterior_power_above_dimension R 1 (R_n R 1)
  (@coordinate_basis R 1) (@coordinate_basisP R 1) h2 2 (erefl true) x.
by rewrite hx exterior_norm_zero.
Qed.

(** Source for [hadamard_one_dimensional_counterexample]: Federer 1.7.5, p.
    32, concrete regression for the local correction: the family (0,1,1) in
    R has equality in the product estimate without pairwise orthogonality.
    This is not an erratum entry. *)
Example hadamard_one_dimensional_counterexample :
  let u := @coordinate_basis R 1 ord0 in
  exterior_norm h2 (@euclidean_inner_productP R 1)
    (e_lambda (@idfun (R_n R 1)) [tuple 0; u; u]) = 0 /\
  ~ (forall i j : 'I_3, i != j ->
    euclidean_inner_product (tnth [tuple 0; u; u] i)
      (tnth [tuple 0; u; u] j) = 0).
Proof.
move=> u.
have hu : euclidean_inner_product u u = 1.
  by rewrite /u euclidean_inner_basis /coordinate_basis ffunE eqxx.
have [he hn] := hadamard_zero_factor_counterexample h2
  (@euclidean_inner_productP R 1) hu.
split; last exact hn.
by rewrite he inner_norm0 !mul0r.
Qed.
End ExteriorMetricRegression.

From Federer Require Import OperatorNorm OperatorNormUP OperatorNormLaws
  ExteriorOperatorNorm TopExteriorNorm TopTargetExteriorNorm TensorUP ExteriorDeterminant.

Section OperatorNormRegression.
Variable R : realType.
Local Notation h2 := (real_two_nonzero R).
Local Notation E0 := (R_n R 0).
Local Notation h0 := (@euclidean_inner_productP R 0).
Local Notation hb0 := (inner_empty_coordinate_basis R).

(** Source for [empty_source_operator_norm_zero]: Federer 1.7.6, p. 33,
    regression for the unit-ball definition: every linear map from dimension
    zero has norm zero, including the identity. *)
Example empty_source_operator_norm_zero (U : lmodType R)
    (C : U -> U -> R) (hC : is_inner_product C) (f : {linear E0 -> U}) :
  linear_operator_norm h0 hC hb0 f = 0.
Proof.
apply: (proj2 (operator_norm_zero_iff (linear_operator_normP h0 hC hb0 f))) => x.
have hx : x = 0 by apply/ffunP=> i; have := ltn_ord i; rewrite ltn0.
by rewrite hx linear0.
Qed.

(** Source for [empty_identity_zeroth_operator_norm_one]: Federer 1.7.6, pp.
    33-34, regression: although the identity on R^0 has norm zero, its
    zeroth exterior map has norm one. This checks the empty-power convention
    in the estimate ||f||^0. *)
Example empty_identity_zeroth_operator_norm_one :
  exterior_operator_norm h2 h0 h0 hb0 (linear_id E0) 0 = 1.
Proof. by rewrite top_exterior_operator_determinant det_id normr1. Qed.

(** Source for [first_coordinate_projection_regression]: Federer 1.7.6, p.
    34, regression map (x,y) -> x, used to distinguish the source-top and
    target-top positivity criteria. *)
Definition first_coordinate_projection_regression : {linear R_n R 2 -> R_n R 1} :=
  GRing.Linear.clone _ _ _ _
    (@coordinate_projection R 2 1 (@Lambda_initial 1 2 (erefl true))) _.

(** Source for [projection_source_top_norm_zero]: Federer 1.7.6, p. 34,
    regression for a noninjective map: the second exterior power of the
    first-coordinate projection R^2 -> R has norm zero. *)
Example projection_source_top_norm_zero :
  exterior_operator_norm h2 (@euclidean_inner_productP R 2)
    (@euclidean_inner_productP R 1) (@coordinate_basisP R 2)
    first_coordinate_projection_regression 2 = 0.
Proof.
apply: (proj2 (operator_norm_zero_iff
  (exterior_operator_normP h2 (@euclidean_inner_productP R 2)
    (@euclidean_inner_productP R 1) (@coordinate_basisP R 2)
    first_coordinate_projection_regression 2))) => x.
exact (@exterior_power_above_dimension R 1 (R_n R 1)
  (@coordinate_basis R 1) (@coordinate_basisP R 1) h2 2 (erefl true) _).
Qed.

(** Source for [projection_target_top_norm_positive]: Federer 1.7.6, p. 34,
    regression for the same surjective map: its first exterior power has
    positive norm, although its source-top norm is zero. *)
Example projection_target_top_norm_positive :
  0 < exterior_operator_norm h2 (@euclidean_inner_productP R 2)
    (@euclidean_inner_productP R 1) (@coordinate_basisP R 2)
    first_coordinate_projection_regression 1.
Proof.
apply: (proj2 (@top_target_norm_positive_iff_surjective R h2 (R_n R 2) (R_n R 1)
  (@euclidean_inner_product R 2) (@euclidean_inner_product R 1)
  (@euclidean_inner_productP R 2) (@euclidean_inner_productP R 1)
  2 1 (@coordinate_basis R 2) (@coordinate_basis R 1)
  (@coordinate_basisP R 2) (@coordinate_basisP R 1)
  first_coordinate_projection_regression)) => y.
exists (@coordinate_injection R 2 1 (@Lambda_initial 1 2 (erefl true)) y).
exact: coordinate_projection_injectionK.
Qed.
End OperatorNormRegression.

From Federer Require Import SimpleVectorProjectionSupremum SimpleCovectorProjectionSupremum
  ExteriorFrameUnitNorm InnerExteriorProducts InnerPolarity OrthogonalEuclidean
  ExteriorCovectorInner.

Section ProjectionSupremumRegression.
Variable R : realType.
Local Notation h2 := (real_two_nonzero R).

(** Source for [empty_product_projection_supremum_one]: Federer
    1.7.7, p. 34, regression: the empty simple product in R^0 has
    projected-norm supremum one, despite its ambient dimension zero. *)
Example empty_product_projection_supremum_one :
  sup (simple_vector_projection_values h2
    (e_lambda (@coordinate_basis R 0) (ord_tuple 0))) = 1.
Proof.
rewrite -(simple_vector_projection_supremum h2 (product_simple _)).
exact: euclidean_top_product_unit_norm.
Qed.

(** Source for [empty_covector_projection_supremum_one]: Federer
    1.7.7, p. 34, regression for the covector formula on the empty
    product and the zero-dimensional orthogonal group. *)
Example empty_covector_projection_supremum_one :
  sup (simple_covector_projection_values h2
    (inner_exterior_form h2 (@euclidean_inner_productP R 0)
      (e_lambda (@coordinate_basis R 0) (ord_tuple 0)))) = 1.
Proof.
have hs : simple_covector h2 (inner_exterior_form h2 (@euclidean_inner_productP R 0)
    (e_lambda (@coordinate_basis R 0) (ord_tuple 0))).
  exists (fun i => inner_polarity (@euclidean_inner_productP R 0) (@coordinate_basis R 0 i)).
  exact: inner_exterior_product_covectors.
rewrite -(simple_covector_projection_supremum hs) inner_exterior_form_norm.
exact: euclidean_top_product_unit_norm.
Qed.

(** Source for [no_one_frame_in_zero_space]: Federer 1.7.7,
    p. 34, boundary regression: O(0,1) is empty, so the printed
    supremum must allow an empty set above ambient dimension. *)
Example no_one_frame_in_zero_space (f : {linear R_n R 1 -> R_n R 0}) :
  ~ @FedererOrthogonal.O R 0 1 f.
Proof.
move=> hf.
pose e := @coordinate_basis R 1 ord0.
have hz : f e = 0 by apply/ffunP=> i; have := ltn_ord i; rewrite ltn0.
have he := hf e e.
have hzero : @euclidean_inner_product R 0 (f e) (f e) = 0.
  by rewrite /euclidean_inner_product big_ord0.
have hh : @euclidean_inner_product R 1 e e = 1.
  by rewrite euclidean_inner_basis /e /coordinate_basis ffunE eqxx.
move: he; rewrite hzero hh => /eqP; by rewrite eq_sym oner_eq0.
Qed.

(** Source for [above_dimension_projection_supremum_zero]: Federer
    1.7.7, p. 34, regression for a simple 1-vector in R^0:
    it vanishes and its projected-norm set is empty. The supremum
    formula has value zero with the stated real supremum convention. *)
Example above_dimension_projection_supremum_zero :
  sup (simple_vector_projection_values h2
    (e_lambda (fun _ : 'I_1 => (0 : R_n R 0)) (ord_tuple 1))) = 0.
Proof.
rewrite -(simple_vector_projection_supremum h2 (product_simple _)).
have hz := @exterior_power_above_dimension R 0 (R_n R 0)
  (@coordinate_basis R 0) (@coordinate_basisP R 0) h2 1 (erefl true)
  (e_lambda (fun _ : 'I_1 => (0 : R_n R 0)) (ord_tuple 1)).
rewrite hz.
exact: exterior_norm_zero.
Qed.
End ProjectionSupremumRegression.

From Federer Require Import HodgeMaps HodgeBasis HodgeSquare HodgeMixedPairing
  HodgeIsometry HodgeAlgebraCompatibility ExteriorFrameUnitNorm TopComplements
  InteriorSigns InnerExteriorBasis ExteriorCovectorInner.

Section HodgeRegression.
Variable R : rcfType.
Local Notation h2 := (real_two_nonzero R).
Local Notation h0 := (@euclidean_inner_productP R 0).
Local Notation hE2 := (@euclidean_inner_productP R 2).
Local Notation vol0 := (e_lambda (@coordinate_basis R 0) (ord_tuple 0)).
Local Notation vol2 := (e_lambda (@coordinate_basis R 2) (ord_tuple 2)).

(** Source for [negative_empty_volume_hodge]: Federer 1.7.8,
    p. 34, regression for a negative unit volume in dimension zero:
    the Hodge map takes the empty product to its negative. *)
Example negative_empty_volume_hodge :
  exterior_norm h2 h0 ((-1 : R) *: vol0) = 1 /\
  hodge_vector h2 h0 ((-1 : R) *: vol0) (leqnn 0) vol0 = -vol0.
Proof.
split.
- by rewrite exterior_norm_scale normrN1 euclidean_top_product_unit_norm mul1r.
- have ho : orthonormal_family (@euclidean_inner_product R 0) (@coordinate_basis R 0).
    move=> i; have := ltn_ord i; by rewrite ltn0.
  have hcomp : top_complement (Lambda_top 0) = Lambda_top 0 := Lambda_top_unique _.
  have hN : FedererInteriorSigns.N (Lambda_top 0) (top_complement (Lambda_top 0)) = 0.
    rewrite /FedererInteriorSigns.N.
    apply/eqP; rewrite cards_eq0; apply/eqP/setP=> [[i j]].
    have := ltn_ord i; by rewrite ltn0.
  rewrite hodge_vector_volume_scale
    (@hodge_vector_basis R h2 (R_n R 0) (@euclidean_inner_product R 0) h0
      0 (@coordinate_basis R 0) (@coordinate_basisP R 0) ho 0 (leqnn 0) (Lambda_top 0))
    hN expr0 scale1r hcomp scaleN1r.
  by [].
Qed.

(** Source for [plane_hodge_square_negative]: Federer 1.7.8,
    p. 34, regression for odd p(n-p): on 1-vectors in R^2,
    star squared is negative identity. *)
Example plane_hodge_square_negative (x : exterior_power (R_n R 2) 1) :
  exterior_reindex (subKn (erefl true : (1 <= 2)%N))
    (hodge_vector h2 hE2 vol2 (leq_subr 1 2)
      (hodge_vector h2 hE2 vol2 (erefl true : (1 <= 2)%N) x)) = -x.
Proof.
rewrite (@hodge_vector_square R h2 (R_n R 2) (@euclidean_inner_product R 2) hE2
  2 (@coordinate_basis R 2) (@coordinate_basisP R 2) vol2
  (euclidean_top_product_unit_norm h2 2) 1 (erefl true : (1 <= 2)%N) x).
by rewrite expr1 scaleN1r.
Qed.

(** Source for [negative_empty_covector_hodge_square]: Federer
    1.7.8, p. 34, regression: on every scalar covector, two
    stars for the negative zero-dimensional volume give identity. *)
Example negative_empty_covector_hodge_square (phi : A_m (R_n R 0) R^o 0) :
  form_reindex (subKn (leqnn 0))
    (hodge_covector h2 h0 ((-1 : R) *: vol0) (leq_subr 0 0)
      (hodge_covector h2 h0 ((-1 : R) *: vol0) (leqnn 0) phi)) = phi.
Proof.
rewrite (@hodge_covector_square R h2 (R_n R 0) (@euclidean_inner_product R 0) h0
  0 (@coordinate_basis R 0) (@coordinate_basisP R 0) ((-1 : R) *: vol0)
  (proj1 negative_empty_volume_hodge) 0 (leqnn 0) phi).
by rewrite expr0 scale1r.
Qed.

(** Source for [plane_mixed_pairing_negative]: Federer 1.7.8,
    p. 34, erratum p. 1, book lines 29-30. For a unit 1-vector
    in R^2 and the polarity of its star, the mixed pairing is -1,
    while the simultaneous pairing is 1. This exhibits the printed
    sign (-1)^{p(n-p)} for p = 1, n = 2; the erratum corrects the
    covector to beta in wedge^{n-p} V. *)
Example plane_mixed_pairing_negative (x : exterior_power (R_n R 2) 1)
    (hx : exterior_norm h2 hE2 x = 1) :
  pairing x (form_reindex (subKn (erefl true : (1 <= 2)%N))
    (hodge_covector h2 hE2 vol2 (leq_subr 1 2)
      (inner_exterior_form h2 hE2 (hodge_vector h2 hE2 vol2 (erefl true : (1 <= 2)%N) x)))) = -1 /\
  pairing (hodge_vector h2 hE2 vol2 (erefl true : (1 <= 2)%N) x)
    (inner_exterior_form h2 hE2 (hodge_vector h2 hE2 vol2 (erefl true : (1 <= 2)%N) x)) = 1.
Proof.
have hv := euclidean_top_product_unit_norm h2 2.
have he : pairing (hodge_vector h2 hE2 vol2 (erefl true : (1 <= 2)%N) x)
    (inner_exterior_form h2 hE2 (hodge_vector h2 hE2 vol2 (erefl true : (1 <= 2)%N) x)) = 1.
  change (exterior_inner_form h2 hE2 (hodge_vector h2 hE2 vol2 (erefl true : (1 <= 2)%N) x)
    (hodge_vector h2 hE2 vol2 (erefl true : (1 <= 2)%N) x) = 1).
  rewrite -exterior_norm_square
    (@hodge_vector_norm R h2 (R_n R 2) (@euclidean_inner_product R 2) hE2
      2 (@coordinate_basis R 2) (@coordinate_basisP R 2) vol2 hv 1 (erefl true : (1 <= 2)%N) x).
  by rewrite hx expr1n.
split; last exact he.
rewrite (@hodge_mixed_pairing R h2 (R_n R 2) (@euclidean_inner_product R 2) hE2
  2 (@coordinate_basis R 2) (@coordinate_basisP R 2) vol2 hv 1 (erefl true : (1 <= 2)%N) x
  (inner_exterior_form h2 hE2 (hodge_vector h2 hE2 vol2 (erefl true : (1 <= 2)%N) x))) he.
by rewrite expr1 mulr1.
Qed.
End HodgeRegression.

From Federer Require Import TensorInner HomInner HomInnerCoordinates
  HomNormBound HomNormDimensionBound ExteriorHomInner TopHomDeterminant
  HomOrthogonalChange InnerNormalization InnerNorm OperatorNormUP OperatorNorm Adjoint ExteriorDeterminant.
Import Order.TTheory.

Section TensorHomRegression.
Variable R : realType.
Local Notation h2 := (real_two_nonzero R).
Local Notation hE0 := (@euclidean_inner_productP R 0).
Local Notation hE1 := (@euclidean_inner_productP R 1).
Local Notation hE2 := (@euclidean_inner_productP R 2).

(** Source for [tensor_zero_factor_norm]: Federer 1.7.9,
    p. 35, regression for a zero tensor factor, including the
    zero-dimensional source: its tensor norm is zero. *)
Example tensor_zero_factor_norm (w : R_n R 1) :
  tensor_norm hE0 hE1 (tensor_inj (0 : R_n R 0) w) = 0.
Proof. by rewrite tensor_norm_pure inner_norm0 mul0r. Qed.

(** Source for [zero_source_hom_norm]: Federer 1.7.9,
    p. 35, regression for n=0: every map from the zero space
    has Hom norm zero, as required by both comparison bounds. *)
Example zero_source_hom_norm (f : Hom (R_n R 0) (R_n R 2)) :
  hom_norm hE0 hE2 (@coordinate_basisP R 0) f = 0.
Proof.
apply: inner_norm_value; first exact: lexx.
have ho : orthonormal_family (@euclidean_inner_product R 0) (@coordinate_basis R 0).
  move=> i; have := ltn_ord i; by rewrite ltn0.
rewrite (@hom_inner_orthonormal_sum R (R_n R 0) (R_n R 2) _ _ hE0 hE2
  0 (@coordinate_basis R 0) (@coordinate_basisP R 0)
  0 (@coordinate_basis R 0) (@coordinate_basisP R 0) ho f f).
by rewrite big_ord0 expr0n.
Qed.

(** Source for [plane_identity_distinct_norms]: Federer 1.7.9,
    p. 35, regression distinguishing the two norms: the identity
    on R^2 has operator norm one and Hom norm sqrt(2). *)
Example plane_identity_distinct_norms :
  linear_operator_norm hE2 hE2 (@coordinate_basisP R 2) (linear_id (R_n R 2)) = 1 /\
  hom_norm hE2 hE2 (@coordinate_basisP R 2) (hom_of_linear (linear_id (R_n R 2))) = Num.sqrt (2 : R).
Proof.
have ho : orthonormal_family (@euclidean_inner_product R 2) (@coordinate_basis R 2).
  move=> i j; by rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
split.
- apply: operator_norm_unique (linear_operator_normP _ _ _ _) _.
  constructor; first by move=> x hx.
  exists (@coordinate_basis R 2 ord0); split.
  + by rewrite (orthonormal_norm1 hE2 ho).
  + change (inner_norm hE2 (@coordinate_basis R 2 ord0) = 1).
    exact (@orthonormal_norm1 R (R_n R 2) (@euclidean_inner_product R 2) hE2
      (Finite.clone 'I_2 _) (@coordinate_basis R 2) ho ord0).
- apply: inner_norm_value; first exact: sqrtr_ge0.
  rewrite sqr_sqrtr ?ler0n //.
  rewrite (@hom_inner_orthonormal_sum R (R_n R 2) (R_n R 2) _ _ hE2 hE2
    2 (@coordinate_basis R 2) (@coordinate_basisP R 2)
    2 (@coordinate_basis R 2) (@coordinate_basisP R 2) ho).
  have hd i : euclidean_inner_product
      (hom_of_linear (linear_id (R_n R 2)) (@coordinate_basis R 2 i))
      (hom_of_linear (linear_id (R_n R 2)) (@coordinate_basis R 2 i)) = (1 : R).
    change (euclidean_inner_product (@coordinate_basis R 2 i) (@coordinate_basis R 2 i) = 1).
    by rewrite ho eqxx.
  under eq_bigr do rewrite hd.
  by rewrite sumr_const card_ord.
Qed.

(** Source for [zero_source_top_hom_inner_one]: Federer 1.7.9,
    p. 35, regression for the top-degree determinant formula in
    dimension zero: all induced degree-zero maps have product one. *)
Example zero_source_top_hom_inner_one (f g : {linear R_n R 0 -> R_n R 1}) :
  exterior_hom_inner h2 hE0 hE1 (@coordinate_basisP R 0) 0
    (hom_of_linear (exterior_power_map f 0))
    (hom_of_linear (exterior_power_map g 0)) = 1.
Proof.
rewrite top_hom_inner_determinant.
rewrite (@det_ext R h2 0 (R_n R 0) (@coordinate_basis R 0) (@coordinate_basisP R 0)
  (linear_comp (inner_adjoint hE0 hE1 (@coordinate_basisP R 0) f) g)
  (linear_id (R_n R 0))).
- exact: det_id.
- move=> x; apply/ffunP=> i; have := ltn_ord i; by rewrite ltn0.
Qed.
End TensorHomRegression.

From Federer Require Import BilinearRepresentativeUP BilinearInvariants
  BilinearInvariantsIntrinsic BilinearPrecompose FiniteDualDimension CoefficientCoordinates.

Section BilinearInvariantRegression.
Variable R : rcfType.
Local Notation h2 := (real_two_nonzero R).

(** Source for [inner_form_discriminant_trace]: Federer 1.7.10,
    p. 35, regression: the inner product itself is represented
    by identity, so its discriminant is one and its trace is the
    dimension. The statement includes the empty-dimensional case. *)
Example inner_form_discriminant_trace (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b) :
  bilinear_discriminant h2 hB (inner_bilinear hB) hb = 1 /\
  bilinear_trace h2 hB (inner_bilinear hB) hb = n%:R.
Proof.
have hi : is_bilinear_representative B B (linear_id V) by [].
split.
- rewrite (@bilinear_discriminant_characterisation R h2 V B B hB (inner_bilinear hB)
    n b hb (linear_id V) hi); exact: det_id.
- rewrite (@bilinear_trace_characterisation R h2 V B B hB (inner_bilinear hB)
    n b hb (linear_id V) hi) trace_HomE.
  have hd i : dual_basis hb i (hom_of_linear (linear_id V) (b i)) = (1 : R).
    change (dual_basis hb i (b i) = 1); by rewrite dual_basisE eqxx.
  under eq_bigr do rewrite hd.
  by rewrite sumr_const card_ord.
Qed.

(** Source for [empty_bilinear_discriminant_trace]: Federer 1.7.10,
    p. 35, regression for an arbitrary bilinear form in dimension
    zero: its discriminant is the empty determinant one, while its
    trace is the empty sum zero. *)
Example empty_bilinear_discriminant_trace (S : R_n R 0 -> R_n R 0 -> R)
    (hS : @TensorUP.bilinear R (R_n R 0) (R_n R 0) R^o S) :
  bilinear_discriminant h2 (@euclidean_inner_productP R 0) hS (@coordinate_basisP R 0) = 1 /\
  bilinear_trace h2 (@euclidean_inner_productP R 0) hS (@coordinate_basisP R 0) = 0.
Proof.
split.
- rewrite /bilinear_discriminant.
  rewrite (@det_ext R h2 0 (R_n R 0) (@coordinate_basis R 0) (@coordinate_basisP R 0)
    (bilinear_representative (@euclidean_inner_productP R 0) hS (@coordinate_basisP R 0))
    (linear_id (R_n R 0))).
  + exact: det_id.
  + move=> x; apply/ffunP=> i; have := ltn_ord i; by rewrite ltn0.
- by rewrite /bilinear_trace trace_HomE big_ord0.
Qed.

(** Source for [nonsymmetric_bilinear_representative]: Federer
    1.7.10, p. 35, regression for the order of the arguments
    in B(f(x),y)=S(x,y). A nonsymmetric rank-one form sends the
    first coordinate vector to the second and the second to zero;
    taking the transposed representative would reverse these roles. *)
Example nonsymmetric_bilinear_representative :
  let e := @coordinate_basis R 2 in
  let he := @coordinate_basisP R 2 in
  let hB := @euclidean_inner_productP R 2 in
  let s := hom_as_linear (hom_with_coefficient (e ord_max) (dual_basis he ord0)) in
  let hS := bilinear_linear_precompose (inner_bilinear hB) s (linear_id (R_n R 2)) in
  bilinear_representative hB hS he (e ord0) = e ord_max /\
  bilinear_representative hB hS he (e ord_max) = 0.
Proof.
move=> e he hB s hS.
have hs : is_bilinear_representative (@euclidean_inner_product R 2)
    (fun x y => euclidean_inner_product (s x) y) s by [].
have hh := @bilinear_representative_unique R (R_n R 2)
  (@euclidean_inner_product R 2) (fun x y => euclidean_inner_product (s x) y) hB
  (bilinear_representative hB hS he) s (bilinear_representativeP hB hS he) hs.
rewrite !hh /s !hom_as_linearE !hom_with_coefficientE !dual_basisE.
by rewrite eqxx scale1r scale0r.
Qed.
End BilinearInvariantRegression.

From Federer Require Import SubspaceDifferenceNorm SubspaceDifference ProductInner
  DiagonalExteriorNorm ProductSpaceMaps BilinearNegation InnerExteriorPositivity.

Section DifferenceNormRegression.
Variable R : realType.
Local Notation h2 := (real_two_nonzero R).
Local Notation h0 := (@euclidean_inner_productP R 0).
Local Notation hE2 := (@euclidean_inner_productP R 2).
Local Notation vol0 := (e_lambda (@coordinate_basis R 0) (ord_tuple 0)).
Local Notation vol2 := (e_lambda (@coordinate_basis R 2) (ord_tuple 2)).

(** Source for [empty_difference_operator_norm_one]: Federer
    1.7.11, p. 36, regression at n=k=l=0 with the negative
    unit ambient volume. The zeroth exterior map has norm one,
    and the two negative Hodge values multiply to the empty product. *)
Example empty_difference_operator_norm_one :
  is_operator_norm
    (exterior_inner_productP h2
      (subspace_product_innerP h0 (FedererSimple.T vol0) (FedererSimple.T vol0)) 0)
    (exterior_inner_productP h2 h0 0)
    (exterior_power_map (GRing.Linear.clone _ _ _ _
      (subspace_difference (FedererSimple.T vol0) (FedererSimple.T vol0)) _) 0) 1.
Proof.
have hw : exterior_product vol0 vol0 = vol0.
  apply: val_inj; change (component_val (exterior_product vol0 vol0) = component_val vol0).
  by rewrite exterior_productE !e_lambdaE /= enum_ord0 /= wedge_unitl.
have hh := @subspace_difference_norm R h2 (R_n R 0)
  (@euclidean_inner_product R 0) h0 0 (@coordinate_basis R 0) (@coordinate_basisP R 0)
  ((-1 : R) *: vol0) (proj1 (@negative_empty_volume_hodge R))
  0 0 (leqnn 0) (leqnn 0) (leqnn 0) vol0 vol0
  (product_simple _) (product_simple _)
  (euclidean_top_product_unit_norm h2 0) (euclidean_top_product_unit_norm h2 0).
rewrite expr0 mul1r (proj2 (@negative_empty_volume_hodge R))
  (bilNl (@exterior_product_bilinear R (R_n R 0) 0 0))
  (bilNr (@exterior_product_bilinear R (R_n R 0) 0 0)) opprK hw
  euclidean_top_product_unit_norm in hh.
exact hh.
Qed.

(** Source for [coincident_plane_lines_difference_norm_zero]: Federer
    1.7.11, p. 36, regression for identical one-dimensional
    associated spaces in a two-dimensional ambient space. Their sum
    is proper, so the top exterior difference map has norm zero.
    This checks that no transversality assumption entered the formula. *)
Example coincident_plane_lines_difference_norm_zero
    (x : exterior_power (R_n R 2) 1) (sx : simple x)
    (hx : exterior_norm h2 hE2 x = 1) :
  is_operator_norm
    (exterior_inner_productP h2
      (subspace_product_innerP hE2 (FedererSimple.T x) (FedererSimple.T x)) 2)
    (exterior_inner_productP h2 hE2 2)
    (exterior_power_map (GRing.Linear.clone _ _ _ _
      (subspace_difference (FedererSimple.T x) (FedererSimple.T x)) _) 2) 0.
Proof.
have hz (z : exterior_power (R_n R 2) 1) : exterior_product z z = 0.
  apply: val_inj.
  change (wedge (component_val z) (component_val z) =
    component_val (0 : exterior_power (R_n R 2) 2)).
  rewrite linear0 -{1 2}(@exterior_first_component R (R_n R 2)
    (component_val z) (component_homogeneous z)).
  exact: exterior_generator_square.
have hh := @subspace_difference_norm R h2 (R_n R 2)
  (@euclidean_inner_product R 2) hE2 2 (@coordinate_basis R 2) (@coordinate_basisP R 2)
  vol2 (euclidean_top_product_unit_norm h2 2)
  1 1 (erefl true) (erefl true) (erefl true) x x sx sx hx hx.
rewrite hz exterior_norm_zero mulr0 in hh.
exact hh.
Qed.

(** Source for [diagonal_plane_volume_scale_two]: Federer
    1.7.11, p. 36, regression for the nontrivial factor:
    the diagonal image of a unit two-vector has norm two,
    which is sqrt(2)^2. *)
Example diagonal_plane_volume_scale_two :
  exterior_norm h2 (product_inner_productP hE2 hE2)
    (exterior_power_map (FedererProduct.g_map (R_n R 2)) 2 vol2) = 2.
Proof.
rewrite diagonal_exterior_norm euclidean_top_product_unit_norm mulr1.
by rewrite sqr_sqrtr ?ler0n.
Qed.
End DifferenceNormRegression.

From Federer Require Import ExteriorTwoTrace ExteriorTwoAdjointTrace TraceCyclic
  AdjointSquareTrace HomInnerCoordinates HomInnerTrace AdjointUP.

Section SecondTraceRegression.
Variable R : rcfType.
Local Notation h2 := (real_two_nonzero R).

(** Source for [empty_second_exterior_trace]: Federer 1.7.12,
    pp. 36-37, regression in dimension zero: the second exterior
    trace is zero, as forced by the first identity and empty traces. *)
Example empty_second_exterior_trace (f : Hom (R_n R 0) (R_n R 0)) :
  @trace_Hom R h2 (exterior_power (R_n R 0) 2) (Finite.clone (Lambda 0 2) _)
    (@finite_e_lambda R 0 (R_n R 0) (@coordinate_basis R 0) 2)
    (finite_e_lambda_basis (@coordinate_basisP R 0) h2 2)
    (hom_of_linear (exterior_power_map (hom_as_linear f) 2)) = 0.
Proof.
have ht g : @trace_Hom R h2 (R_n R 0) (Finite.clone 'I_0 _)
    (@coordinate_basis R 0) (@coordinate_basisP R 0) g = 0.
  by rewrite trace_HomE big_ord0.
have hh := @exterior_two_trace R h2 (R_n R 0) 0
  (@coordinate_basis R 0) (@coordinate_basisP R 0) f.
rewrite !ht expr0n subr0 in hh.
apply: (mulfI h2); by rewrite mulr0.
Qed.

(** Source for [plane_identity_second_trace]: Federer 1.7.12,
    pp. 36-37, regression for the normalisation: the second
    exterior trace of the identity on R^2 equals one, checked
    independently through the top-degree determinant formula. *)
Example plane_identity_second_trace :
  @trace_Hom R h2 (exterior_power (R_n R 2) 2) (Finite.clone (Lambda 2 2) _)
    (@finite_e_lambda R 2 (R_n R 2) (@coordinate_basis R 2) 2)
    (finite_e_lambda_basis (@coordinate_basisP R 2) h2 2)
    (hom_of_linear (exterior_power_map (linear_id (R_n R 2)) 2)) = 1.
Proof.
rewrite -trace_Gamma_power trace_top_power.
exact: det_id.
Qed.

(** Source for [nilpotent_plane_adjoint_second_trace]: Federer
    1.7.12, pp. 36-37, regression for the negative cross term:
    N sends the first coordinate vector to the second and squares
    to zero. The second exterior trace of N+adjoint(N) is -1,
    since trace(N)=trace(N squared)=0 and trace(adjoint(N) N)=1. *)
Example nilpotent_plane_adjoint_second_trace :
  let e := @coordinate_basis R 2 in
  let he := @coordinate_basisP R 2 in
  let hB := @euclidean_inner_productP R 2 in
  let f := rank_one (one_form (dual_basis he ord0)) (e ord_max) in
  let a := hom_of_linear (inner_adjoint hB hB he (hom_as_linear f)) in
  @trace_Hom R h2 (exterior_power (R_n R 2) 2) (Finite.clone (Lambda 2 2) _)
    (@finite_e_lambda R 2 (R_n R 2) e 2) (finite_e_lambda_basis he h2 2)
    (hom_of_linear (exterior_power_map (hom_as_linear (f+a)) 2)) = -1.
Proof.
move=> e he hB f a.
have ha : is_adjoint (@euclidean_inner_product R 2) (@euclidean_inner_product R 2)
    (hom_as_linear f) (hom_as_linear a).
  move=> u v; exact (@inner_adjointP R (R_n R 2) (R_n R 2)
    (@euclidean_inner_product R 2) (@euclidean_inner_product R 2) hB hB
    2 e he (hom_as_linear f) u v).
have ht : @trace_Hom R h2 (R_n R 2) (Finite.clone 'I_2 _) e he f = 0.
  by rewrite /f trace_Hom_rank_one one_formK dual_basisE.
have hff : hom_comp f f = 0.
  by rewrite /f rank_one_comp one_formK dual_basisE scale0r.
have ho : orthonormal_family (@euclidean_inner_product R 2) e.
  by move=> i j; rewrite /e euclidean_inner_basis /coordinate_basis ffunE eq_sym.
have hnorm : hom_inner hB hB he f f = 1.
  rewrite (@hom_inner_orthonormal_sum R (R_n R 2) (R_n R 2)
    (@euclidean_inner_product R 2) (@euclidean_inner_product R 2) hB hB
    2 e he 2 e he ho f f).
  rewrite !big_ord_recr big_ord0 /f !rank_oneE !one_formK !dual_basisE
    /= !scale1r !scale0r add0r.
  by rewrite (bil0l (inner_bilinear hB)) addr0 ho eqxx.
have hcross : @trace_Hom R h2 (R_n R 2) (Finite.clone 'I_2 _) e he (hom_comp a f) = 1.
  rewrite -(@hom_inner_adjoint_trace R h2 (R_n R 2) (R_n R 2)
    (@euclidean_inner_product R 2) (@euclidean_inner_product R 2) hB hB
    2 e he f f (hom_as_linear a) ha).
  exact hnorm.
rewrite (@exterior_two_adjoint_trace R h2 (R_n R 2)
  (@euclidean_inner_product R 2) hB 2 e he f a ha) ht hff linear0 hcross.
by rewrite expr0n mulr0 subr0 sub0r.
Qed.
End SecondTraceRegression.

From mathcomp Require Import reals classical_sets topology num_normedtype normed_module.
From Federer Require Import HilbertSpaceUP InnerConvex InnerNearestUP InnerNearIntersection
  HilbertNearest HilbertFunctionalUP HilbertFunctional InnerSetDistance
  InnerMetric InnerNormedTopology.
Import Order.TTheory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Section HilbertRegression.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation M := (inner_metric_space hB).
Hypothesis hH : is_hilbert_space hB.

(** Source for [hilbert_full_space_nearest_self]: Federer 1.7.13,
    p. 37, regression for the whole-space set: its specified
    nearest point to a is a itself. All witnesses of nonemptiness,
    closedness, and convexity give the same result. *)
Example hilbert_full_space_nearest_self (a : M)
    (hne : (@setT M) !=set0) (hclosed : closed (@setT M))
    (hconv : is_inner_convex (@setT M)) :
    @hilbert_nearest R V B hB hH a setT hne hclosed hconv = a.
Proof.
symmetry; apply: hilbert_nearest_unique.
constructor; first exact I.
move=> x _; rewrite subrr inner_norm0; exact: inner_norm_nonnegative.
Qed.

(** Source for [hilbert_singleton_nearest]: Federer 1.7.13,
    p. 37, regression for a singleton, including the zero
    subspace when b=0: its specified nearest point is b. *)
Example hilbert_singleton_nearest (a b : M)
    (hne : [set b] !=set0) (hclosed : closed [set b])
    (hconv : is_inner_convex [set b]) :
    @hilbert_nearest R V B hB hH a [set b] hne hclosed hconv = b.
Proof.
have hh := @hilbert_nearestP R V B hB hH a [set b] hne hclosed hconv.
exact: inner_nearest_member_law hh.
Qed.

(** Source for [hilbert_zero_functional_vector]: Federer 1.7.13,
    p. 37, regression for the zero-functional case, where the
    nonzero normalisation step cannot be used: the sealed vector
    representing zero is the zero vector. *)
Example hilbert_zero_functional_vector (f : {linear V -> R^o})
    (hzero : forall v, f v = 0)
    (hf : continuous (fun x : M => (f x : R^o))) :
    @hilbert_functional_vector R V B hB hH f hf = 0.
Proof.
symmetry; apply: hilbert_functional_unique => x.
by rewrite hzero (bil0l (inner_bilinear hB)).
Qed.
End HilbertRegression.

(** Source for [empty_hilbert_functional_vector]: Federer
    1.7.13, p. 37, regression in dimension zero: every linear
    functional has zero representative, for any supplied proof
    of completeness of the zero-dimensional metric. *)
Example empty_hilbert_functional_vector (R : realType)
    (hH : is_hilbert_space (@euclidean_inner_productP R 0))
    (f : {linear R_n R 0 -> R^o})
    (hf : continuous (fun x : inner_metric_space (@euclidean_inner_productP R 0) =>
      (f x : R^o))) :
    @hilbert_functional_vector R (R_n R 0) (@euclidean_inner_product R 0)
      (@euclidean_inner_productP R 0) hH f hf = 0.
Proof.
symmetry; apply: hilbert_functional_unique => v.
have hv : v=0.
  apply/ffunP=> i; have hi := ltn_ord i; by rewrite ltn0 in hi.
by rewrite hv linear0 (bil0l (inner_bilinear (@euclidean_inner_productP R 0))).
Qed.

From Federer Require Import SimpleUnitBall ComassUP Comass ComassBounds
  ComassZeroDegree MassUP Mass MassBounds MassEquality MassInfimum
  MassPositiveConvexRepresentation.

Section MassComassRegression.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.
Hypothesis hm : (0 < m)%N.
Local Notation kappa := (@comass R h2 V B hB n e he m hm).
Local Notation hk := (@comassP R h2 V B hB n e he m hm).
Local Notation mu := (@mass R h2 V B hB n e he m hm).

(** Source for [mass_above_ambient_dimension]: Federer 1.8.1,
    p. 38, regression for degrees above the ambient dimension.
    All multivectors then have mass zero, including positive-degree
    powers of the zero space; no inverse binomial factor is used. *)
Example mass_above_ambient_dimension (hnm : (n < m)%N)
    (x : exterior_power V m) : mu x = 0.
Proof.
have hx := @exterior_power_above_dimension R n V e he h2 m hnm x.
rewrite hx; exact: mass_unique (@massP R h2 V B hB n e he m hm 0)
  (@mass_zero R h2 V B hB m hm kappa hk).
Qed.

(** Source for [comass_above_ambient_dimension]: Federer 1.8.1,
    p. 38, regression for the corresponding zero covector space.
    The simple unit ball still contains zero in positive degree. *)
Example comass_above_ambient_dimension (hnm : (n < m)%N)
    (phi : A_m V R^o m) : kappa phi = 0.
Proof.
have hphi : phi=0.
  apply: pairing_ext => x.
  rewrite (@exterior_power_above_dimension R n V e he h2 m hnm x).
  by rewrite !(bil0l (@pairing_bilinear R V R^o m)).
rewrite hphi; exact: comass_unique (hk 0) (@comass_zero R h2 V B hB m hm).
Qed.

(** Source for [zero_mass_empty_decomposition]: Federer 1.8.1,
    pp. 38-39, regression for the empty optimal decomposition.
    Its total Euclidean length equals the public mass of zero. *)
Example zero_mass_empty_decomposition :
  (0 : exterior_power V m) = \sum_(i : 'I_0) (0 : exterior_power V m) /\
  mu 0 = \sum_(i : 'I_0) exterior_norm h2 hB (0 : exterior_power V m).
Proof.
rewrite !big_ord0; split=> //.
exact: mass_unique (@massP R h2 V B hB n e he m hm 0)
  (@mass_zero R h2 V B hB m hm kappa hk).
Qed.

(** Source for [orthonormal_top_mass_one]: Federer 1.8.1,
    p. 38, regression for a nonzero simple top vector: an
    orthonormal volume has mass one, also in dimension one. *)
Example orthonormal_top_mass_one (hn : (0 < n)%N) (ho : orthonormal_family B e) :
  @mass R h2 V B hB n e he n hn
    (e_lambda e (ord_tuple n)) = 1.
Proof.
have hh := @simple_mass_euclidean R h2 V B hB n e he n hn
  (@comass R h2 V B hB n e he n hn) (@comassP R h2 V B hB n e he n hn)
  (e_lambda e (ord_tuple n)) _ (product_simple e) (@massP R h2 V B hB n e he n hn _).
by rewrite orthonormal_product_unit_norm // in hh.
Qed.
End MassComassRegression.

(** Source for [empty_space_literal_negative_comass]: Federer 1.8.1,
    p. 38, regression for the local degree-zero correction: even on
    the zero ambient space, the literal unsymmetrised supremum of
    the scalar -1 equals -1, so it cannot define a norm. *)
Example empty_space_literal_negative_comass (R : realType)
    (h2 : (1+1 : R) != 0) c :
  is_comass h2 (@euclidean_inner_productP R 0)
    (zero_form (R_n R 0) (-1 : R^o)) c -> c = -1.
Proof.
move=> hc; exact: comass_unique hc
  (@literal_zeroth_comass R h2 (R_n R 0) (@euclidean_inner_product R 0)
    (@euclidean_inner_productP R 0) (-1)).
Qed.

From Federer Require Import SimpleVectors SimpleZeroDegree SimpleElementary
  ScalarRestriction ComplexScalarSealed ComplexPairedVectors
  BilinearNegation HermitianUP HermitianRealImaginary HermitianRotation StandardHermitian
  TwoFormPowers ExteriorNorm InnerNorm InnerExteriorPositivity
  ComassUP Wirtinger WirtingerPairedEquality WirtingerComass WirtingerZeroDegree PositivePairedScaling
  PairedRealVectors PairedVectorNaturality SkewNormalFormUP OrthonormalFamilies.

(** Source for [empty_complex_space_zeroth_wirtinger_comass]: Federer
    1.8.2, p. 40, regression for m=0 on the zero-dimensional
    complex coordinate space. The empty power has literal comass one. *)
Example empty_complex_space_zeroth_wirtinger_comass (R : realType)
    (h2 : (1+1 : R) != 0) :
  is_comass h2 (hermitian_real_inner_product (@standard_hermitian_productP R 0))
    (two_form_power h2 (hermitian_two_form (@standard_hermitian_productP R 0)) 0) 1.
Proof. exact: two_form_zeroth_comass. Qed.

Section WirtingerRegression.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType (ComplexScalars.C R).
Variable H : V -> V -> ComplexScalars.C R.
Hypothesis hH : is_hermitian_product H.
Local Notation VR := (restricted_space (ComplexScalars.embed R) V).
Local Notation hB := (hermitian_real_inner_product hH).

(** Source for [zero_wirtinger_paired_equality]: Federer 1.8.2,
    p. 40, regression for the zero 2m-vector in positive degree:
    equality and an exact paired representation both hold. *)
Example zero_wirtinger_paired_equality k :
  pairing (0 : exterior_power VR (k.+1+k.+1))
    (two_form_power h2 (hermitian_two_form hH) k.+1) = 0 /\
  exists v : 'I_k.+1 -> V, (0 : exterior_power VR (k.+1+k.+1)) = paired_complex_vector v.
Proof.
split; first by rewrite (bil0l (@pairing_bilinear R VR R^o (k.+1+k.+1))).
have [v hv] := @zero_paired_complex_representation R V k.
exists v; exact: esym hv.
Qed.

(** Source for [opposite_paired_volume_wirtinger_strict]: Federer
    1.8.2, p. 40, regression for the sign in the equality
    condition: reversing a unit complex orientation gives a strictly
    smaller signed evaluation, despite preserving the norm. *)
Example opposite_paired_volume_wirtinger_strict k (v : 'I_k.+1 -> V)
    (hu : exterior_norm h2 hB (paired_complex_vector v) = 1) :
  pairing (-paired_complex_vector v)
    (two_form_power h2 (hermitian_two_form hH) k.+1) <
  k.+1`!%:R * exterior_norm h2 hB (-paired_complex_vector v).
Proof.
rewrite (bilNl (@pairing_bilinear R VR R^o (k.+1+k.+1)))
  (@wirtinger_paired_equality R h2 V H hH k.+1 v) hu mulr1.
have hnegN : exterior_norm h2 hB (-paired_complex_vector v) = 1.
  rewrite -[(-paired_complex_vector v)]scaleN1r exterior_norm_scale normrN normr1 hu mul1r.
  by [].
rewrite hnegN mulr1.
have hf : (0 : R) < k.+1`!%:R by rewrite ltr0n fact_gt0.
have hneg : -(k.+1`!%:R : R) < 0 by rewrite oppr_lt0.
exact: lt_trans hneg hf.
Qed.

(** Source for [wirtinger_empty_product_equality]: Federer 1.8.2,
    p. 40, regression for literal simplicity in degree zero:
    the empty complex paired product evaluates to one and has norm one. *)
Example wirtinger_empty_product_equality :
  pairing (paired_complex_vector (fun _ : 'I_0 => (0 : V)))
    (two_form_power h2 (hermitian_two_form hH) 0) = 1 /\
  exterior_norm h2 hB (paired_complex_vector (fun _ : 'I_0 => (0 : V))) = 1.
Proof.
have hs := @paired_complex_vector_simple R V 0 (fun _ : 'I_0 => (0 : V)).
split.
- exact (@two_form_zeroth_simple_pairing R h2 VR (hermitian_two_form hH)
    (paired_complex_vector (fun _ : 'I_0 => (0 : V))) hs).
- exact (@two_form_zeroth_simple_norm R h2 VR (hermitian_real_part H) hB
    (paired_complex_vector (fun _ : 'I_0 => (0 : V))) hs).
Qed.
End WirtingerRegression.

From Federer Require Import ComassUnitBall EuclideanComassBall.

(** Source for [zero_space_comass_ball_extreme_point]: Federer
    1.8.3, p. 40, regression for n=0 and positive degree.
    The covector space is zero, so the displayed ball is the
    singleton zero and that point is extreme. *)
Example zero_space_comass_ball_extreme_point (R : realType)
    (h2 : (1+1 : R) != 0) m (hm : (0 < m)%N) :
  is_extreme_point (@euclidean_comass_unit_ball R h2 0 m hm) 0.
Proof.
have hz (phi : A_m (R_n R 0) R^o m) : phi = 0.
  apply: pairing_ext => x.
  rewrite (@exterior_power_above_dimension R 0 (R_n R 0)
    (@coordinate_basis R 0) (@coordinate_basisP R 0) h2 m hm x).
  by rewrite !(bil0l (@pairing_bilinear R (R_n R 0) R^o m)).
split; first exact: euclidean_comass_unit_ball_nonempty.
move=> phi psi hp hq t ht ht1 he; split; exact: hz.
Qed.

From Federer Require Import SimpleVectors SubspaceCarrier InnerProductUP
  ExteriorGrading ExteriorMaps ExteriorHomogeneousProducts FiniteExteriorPowers
  AlternatingCoordinates AlternatingPairing LinearBasis
  ComassUP ComassBounds Comass MassUP MassBounds Mass
  OrthogonalMassInterface MassAttainment.

Section OrthogonalMassRegression.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [zero_wedge_mass_regression]: Federer 1.8.4,
    pp. 40-41, regression for a zero first factor: the product
    has mass zero, including exterior degrees exceeding dim V. *)
Example zero_wedge_mass_regression p q (hp : (0 < p)%N) (hq : (0 < q)%N)
    (y : exterior_power V q) :
  mass h2 hB he (leq_trans hp (leq_addr q p))
    (exterior_product (0 : exterior_power V p) y) = 0.
Proof.
rewrite (bil0l (@exterior_product_bilinear R V p q)).
exact: mass_unique (@massP R h2 V B hB n e he (p+q) (leq_trans hp (leq_addr q p)) 0)
  (@mass_zero R h2 V B hB (p+q) (leq_trans hp (leq_addr q p))
    (@comass R h2 V B hB n e he (p+q) (leq_trans hp (leq_addr q p)))
    (@comassP R h2 V B hB n e he (p+q) (leq_trans hp (leq_addr q p)))).
Qed.

(** Source for [no_unit_comass_above_dimension]: Federer 1.8.4,
    p. 41, regression for the local qualification of the unit
    witness choice: when m>dim V, every covector is zero and
    has comass zero, so none can have comass one. Includes V=0. *)
Example no_unit_comass_above_dimension m (hm : (0 < m)%N) (hnm : (n < m)%N)
    (phi : A_m V R^o m) : comass h2 hB he hm phi != 1.
Proof.
have hphi : phi=0.
  apply: pairing_ext => x.
  rewrite (@exterior_power_above_dimension R n V e he h2 m hnm x).
  by rewrite !(bil0l (@pairing_bilinear R V R^o m)).
rewrite hphi.
have hz := comass_unique (@comassP R h2 V B hB n e he m hm 0)
  (@comass_zero R h2 V B hB m hm).
by rewrite hz eq_sym oner_eq0.
Qed.

(** Source for [zero_mass_attainment_boundary]: Federer 1.8.4,
    p. 41, regression for closed-ball attainment when x=0.
    The zero covector attains mass zero without a unit-norm claim. *)
Example zero_mass_attainment_boundary m (hm : (0 < m)%N) :
  exists phi : A_m V R^o m, comass h2 hB he hm phi <= 1 /\
    pairing (0 : exterior_power V m) phi = 0.
Proof.
exists 0; split.
- have hz := comass_unique (@comassP R h2 V B hB n e he m hm 0)
    (@comass_zero R h2 V B hB m hm).
  by rewrite hz; exact: ler01.
- by rewrite (bil0l (@pairing_bilinear R V R^o m)).
Qed.

(** Source for [right_simple_orthogonal_mass_regression]: Federer
    1.8.4, pp. 40-41, regression for the second-simple-factor
    branch. The first factor has no simplicity hypothesis. *)
Example right_simple_orthogonal_mass_regression (S T : subspace V)
    (hST : forall u v, S u -> T v -> B u v = 0)
    p q (hp : (0 < p)%N) (hq : (0 < q)%N)
    (x0 : exterior_power (subspace_space S) p)
    (y0 : exterior_power (subspace_space T) q)
    (hy : simple (exterior_power_map (subspace_inclusion T) q y0)) :
  mass h2 hB he (leq_trans hp (leq_addr q p))
    (exterior_product (exterior_power_map (subspace_inclusion S) p x0)
      (exterior_power_map (subspace_inclusion T) q y0)) =
  mass h2 hB he hp (exterior_power_map (subspace_inclusion S) p x0) *
  mass h2 hB he hq (exterior_power_map (subspace_inclusion T) q y0).
Proof.
apply: (@mass_orthogonal_product R h2 V B hB n e he S T hST p q hp hq x0 y0).
by right.
Qed.
End OrthogonalMassRegression.
