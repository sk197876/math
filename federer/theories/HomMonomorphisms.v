(** Federer (1969), 2.7.16, example (2), printed p. 136: "We observe that
    the monomorphisms form an open subset of X whose complement has phi
    measure 0, because f fails to be univalent if and only if it satisfies
    the polynomial equation |f(e_1) wedge ... wedge f(e_m)|^2 = 0. Moreover
    G acts transitively on the set of monomorphisms." Here X = Hom(U, V)
    with the topology of HomSpaceTopology.v, e_1, ..., e_m is the given base
    of U, wedge and |.| are those of 1.3.1 and 1.7.5, p. 31
    (exterior_inner_form), and phi is a Haar measure of the additive group
    of X. The function P(f) = |f(e_1) wedge ... wedge f(e_m)|^2
    (hom_wedge_square) vanishes exactly at the maps which are not univalent
    (hom_wedge_square_eq0, by 1.3.4 and 1.7.6, pp. 16 and 34); it is a
    polynomial function in the sense of 1.10.4, p. 46
    (hom_wedge_square_polynomial): by the permutation formula of 1.7.5 it is
    a sum of products of the quadratic functions f |-> f(e_i) . f(e_j), each
    a sum of products of linear functions for an orthonormal base of V.
    Hence the monomorphisms form an open set (hom_monomorphisms_open), and,
    for m <= n, the complement has phi measure 0
    (hom_monomorphisms_complement_null): under the isometry Phi of R^N onto
    X of FiniteHaarLinear.v, phi(S) = c L^N(Phi^{-1}(S)) and P o Phi is a
    nonzero polynomial function on R^N, whose zero set is L^N null by 2.6.5,
    p. 120. For m <= n the linear group G of V acts transitively on the
    monomorphisms (hom_monomorphisms_transitive): the images of e_1, ...,
    e_m under two monomorphisms extend to bases of V (1.6.1, p. 23), and the
    map carrying one base onto the other belongs to G. The building blocks
    of polynomial functions (constants, linear maps, sums, products) are
    proved from the symmetric form representation of 1.10.4
    (PolynomialFunctions.v). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From mathcomp Require Import fingroup perm.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerProductLaws InnerNorm InnerMetric InnerNormedTopology LinearBasis
  FiniteIndependence FiniteBasisComparison FiniteBasisCriterion FiniteDualDimension Annihilator
  SimpleAdaptedBasis OrthonormalFamilies OrthonormalisationUP GramSchmidt InnerFiniteSynthesis
  TensorUP Hom HomInner CoefficientCoordinates GradedComponents ExteriorBases ExteriorGrading
  ExteriorMaps ExteriorDeterminant InversionCount TopExteriorInjectivity ExteriorOperatorEstimate
  InnerExterior InnerExteriorProducts InnerExteriorPositivity Graded GradedSums HomogeneousHom BoundedHom
  SymmetricAlgebra SymmetricGrading SymmetricLowPowers
  SymmetricForms SymmetricFormZero SymmetricFormIsomorphism SymmetricFormSum
  HomogeneousPolynomialFunctions SymmetricPolynomialEvaluation PolynomialFunctions
  PolynomialDiagonalNorm SymmetricPolynomialProduct ScalarCoefficients TensorPowers
  PolynomialLinearComposition PolynomialContinuity EuclideanLebesgueDimensions
  EuclideanLinearMaps MeasureUP HaarIntegralUP HomSpaceTopology LinearGroupTopology LinearGroupSealed
  HomCompositionDeterminant FiniteHaarLinear HomHaarCovariance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PolynomialPieces.
Variable K : fieldType.
Variables V W : lmodType K.

(** Source for [polynomial_function_eq]: a function which agrees
    everywhere with a polynomial function is one, Federer 1.10.4, p. 46.
    Supporting lemma. *)
Lemma polynomial_function_eq (P Q : V -> W) : P =1 Q -> is_polynomial_function P -> is_polynomial_function Q.
Proof. by move=> hPQ [f hf]; exists f=> x; rewrite -hPQ hf. Qed.

(** Source for [polynomial_constant]: constant functions are polynomial
    functions, represented by a symmetric form of degree 0, Federer
    1.10.4, p. 46. Supporting lemma. *)
Lemma polynomial_constant (w : W) : is_polynomial_function (fun _ : V => w).
Proof.
exists (sform_include (zero_sform V w))=> x.
rewrite symmetric_polynomial_value_include sform_polynomial_diagonal_value.
by rewrite zero_sformE fact0 invr1 scale1r.
Qed.

(** Source for [polynomial_linear]: linear maps are polynomial
    functions, represented by a symmetric form of degree 1, Federer
    1.10.4, p. 46, with 1.9.1, p. 41. Supporting lemma. *)
Lemma polynomial_linear (f : {linear V -> W}) : is_polynomial_function f.
Proof.
pose h : Hom (symmetric_power V 1) W :=
  hom_comp (hom_of_linear f) (hom_of_linear (symmetric_first_inverse V)).
exists (sform_include (hom_to_sform h))=> x.
rewrite symmetric_polynomial_value_include sform_polynomial_diagonal_value.
have h1 : (1`!%:R : K) = 1 by rewrite /= mulr1n.
rewrite h1 invr1 scale1r hom_to_sformE /h hom_compE !hom_of_linearE.
congr (f _).
change (x = symmetric_degree_one V (component_val (symmetric_tuple_component [tuple x | _ < 1]))).
rewrite symmetric_tuple_componentE symmetric_degree_one_word.
have he : enum 'I_1 = [:: ord0] by apply: (inj_map val_inj); rewrite val_enum_ord.
by rewrite /= he.
Qed.

(** Source for [polynomial_lincomb]: a P + Q is a polynomial function
    when P and Q are, Federer 1.10.4, p. 46. Supporting lemma. *)
Lemma polynomial_lincomb (a : K) (P Q : V -> W) :
  is_polynomial_function P -> is_polynomial_function Q ->
  is_polynomial_function (fun x => a *: P x + Q x).
Proof.
move=> [f hf] [g hg]; exists (a *: f + g)=> x.
by rewrite linearP /= hf hg.
Qed.

(** Source for [polynomial_scale]: a P is a polynomial function when P
    is, Federer 1.10.4, p. 46. Supporting lemma. *)
Lemma polynomial_scale (a : K) (P : V -> W) :
  is_polynomial_function P -> is_polynomial_function (fun x => a *: P x).
Proof.
move=> hP; apply: (polynomial_function_eq _ (polynomial_lincomb a hP (polynomial_constant 0))).
by move=> x; rewrite addr0.
Qed.

(** Source for [polynomial_big_sum]: finite sums of polynomial functions
    are polynomial functions, Federer 1.10.4, p. 46. Supporting lemma. *)
Lemma polynomial_big_sum (I : Type) (s : seq I) (F : I -> V -> W) :
  (forall i, is_polynomial_function (F i)) -> is_polynomial_function (fun x => \sum_(i <- s) F i x).
Proof.
move=> hF; elim: s=> [|i s ih].
  by apply: (polynomial_function_eq _ (polynomial_constant 0))=> x; rewrite big_nil.
apply: (polynomial_function_eq _ (polynomial_lincomb 1 (hF i) ih))=> x.
by rewrite big_cons scale1r.
Qed.

End PolynomialPieces.

Section ScalarPolynomials.
Variable R : realType.
Variable V : lmodType R.

(** Source for [polynomial_mul]: the pointwise product of real valued
    polynomial functions is a polynomial function, Federer 1.10.4, p. 46
    (polynomial_product of SymmetricPolynomialProduct.v). Supporting
    lemma. *)
Lemma polynomial_mul (P Q : V -> R^o) :
  is_polynomial_function P -> is_polynomial_function Q ->
  is_polynomial_function (fun x => P x * Q x).
Proof.
move=> hP hQ.
pose P' := @PolynomialMap R V R^o P (introT (asboolP _) hP).
pose Q' := @PolynomialMap R V R^o Q (introT (asboolP _) hQ).
have h := polynomial_function_proof (polynomial_product (scalar_bilinear R) P' Q').
move/asboolP: h=> [f hf]; exists f=> x.
by rewrite -hf (polynomial_productE (@pchar_num R)).
Qed.

(** Source for [polynomial_foldr_mul]: finite products of real valued
    polynomial functions are polynomial functions, Federer 1.10.4, p. 46.
    Supporting lemma. *)
Lemma polynomial_foldr_mul (I : Type) (s : seq I) (F : I -> V -> R^o) :
  (forall i, is_polynomial_function (F i)) ->
  is_polynomial_function (fun x => foldr *%R 1 [seq F i x | i <- s]).
Proof.
move=> hF; elim: s=> [|i s ih] /=; first exact: polynomial_constant.
exact: (polynomial_mul (hF i) ih).
Qed.

End ScalarPolynomials.

Section Monomorphisms.
Variable R : realType.
Variables U V : lmodType R.
Variable C : U -> U -> R.
Hypothesis hC : is_inner_product C.
Variable m : nat.
Variable c : 'I_m -> U.
Hypothesis hc : is_basis c.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation X := (inner_metric_space (hom_inner_productP hC hB hc)).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation h2 := (euclidean_two_nonzero R).

(** Source for [hom_monomorphisms]: "the monomorphisms" of X =
    Hom(U, V), Federer 2.7.16, p. 136: the univalent linear maps.
    Definition. *)
Definition hom_monomorphisms : set X := [set f | injective (f : Hom U V)].

(** Source for [hom_wedge]: f(e_1) wedge ... wedge f(e_m) in
    wedge_m V, Federer 2.7.16, p. 136, with wedge of 1.3.1, p. 13.
    Definition. *)
Definition hom_wedge (f : Hom U V) : exterior_power V m := e_lambda (fun i => f (c i)) (ord_tuple m).

(** Source for [hom_wedge_square]: |f(e_1) wedge ... wedge f(e_m)|^2,
    Federer 2.7.16, p. 136, with the inner product of wedge_m V of
    1.7.5, p. 31. Definition. *)
Definition hom_wedge_square (f : Hom U V) : R := exterior_inner_form h2 hB (hom_wedge f) (hom_wedge f).

(** Source for [hom_wedge_nonzero]: f(e_1) wedge ... wedge f(e_m) <> 0
    if and only if f is univalent, Federer 1.3.4, p. 16, and 1.7.6,
    p. 34 (top_exterior_nonzero_iff_injective), since this product is
    wedge_m f applied to e_1 wedge ... wedge e_m. Supporting lemma for
    2.7.16, p. 136. *)
Lemma hom_wedge_nonzero (f : Hom U V) : hom_wedge f != 0 <-> injective f.
Proof.
have ht : exterior_power_map (hom_as_linear f) m (top_vector c) = hom_wedge f.
  exact: exterior_map_indexed_product.
rewrite -ht -(top_exterior_nonzero_iff_injective h2 hc (hom_as_linear f)); split.
  by move=> h; exists (top_vector c).
move=> [x hx]; apply/eqP=> hz; move/eqP: hx; apply.
rewrite (top_expansion h2 hc x) linearZ.
change ((top_coordinate h2 hc x : R) *: exterior_power_map (hom_as_linear f) m (top_vector c) = 0).
by rewrite hz scaler0.
Qed.

(** Source for [hom_wedge_square_eq0]: "f fails to be univalent if and
    only if it satisfies the polynomial equation
    |f(e_1) wedge ... wedge f(e_m)|^2 = 0", Federer 2.7.16, p. 136, by
    the positivity of the inner product of 1.7.5, p. 31. Direct
    formalisation. *)
Theorem hom_wedge_square_eq0 (f : Hom U V) : hom_wedge_square f = 0 <-> ~ injective f.
Proof.
rewrite -hom_wedge_nonzero /hom_wedge_square.
have h := inner_self_eq0 (exterior_inner_productP h2 hB m) (hom_wedge f).
split=> [hz|hn]; first by move: h; rewrite hz eqxx=> /esym/eqP ->; rewrite eqxx.
by apply/eqP; rewrite h; apply: contrapT=> hne; apply: hn; exact/negP.
Qed.

(** Source for [hom_inner_coordinate]: f |-> f(x) . v, a linear
    function on Hom(U, V), Federer 1.4.1, p. 17, and 1.7.1, p. 28;
    supporting the polynomial of 2.7.16, p. 136. Definition of the
    function. *)
Definition hom_inner_coordinate (x : U) (v : V) (f : Hom U V) : R^o := B (f x) v.

(** Source for [hom_inner_coordinate_linear]: f |-> f(x) . v is linear,
    Federer 1.7.1, p. 28. Supporting lemma. *)
Lemma hom_inner_coordinate_linear (x : U) (v : V) : linear (hom_inner_coordinate x v).
Proof.
move=> a f g; rewrite /hom_inner_coordinate hom_addE hom_scaleE.
by rewrite -!(inner_coordinateE hB) linearP.
Qed.
HB.instance Definition _ (x : U) (v : V) := GRing.isLinear.Build R (Hom U V) R^o *:%R
  (hom_inner_coordinate x v) (hom_inner_coordinate_linear x v).

(** Source for [inner_orthonormal_expansion]: v . w = sum_k (v . e_k)
    (w . e_k) for an orthonormal base e of V, Federer 1.7.1, p. 28.
    Supporting lemma for 2.7.16, p. 136. *)
Lemma inner_orthonormal_expansion (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e)
    (v w : V) : B v w = \sum_k B v (e k) * B w (e k).
Proof.
have hw := @inner_finite_synthesis_coordinates R V B hB n e he ho w.
rewrite /inner_finite_synthesis in hw.
rewrite -[in LHS]hw (inner_symmetric hB v) -(inner_coordinateE hB v) linear_sum.
apply: eq_bigr=> k _; rewrite linearZ_LR !inner_coordinateE (inner_symmetric hB (e k)).
by change (B w (e k) * B v (e k) = B v (e k) * B w (e k)); rewrite mulrC.
Qed.

(** Source for [hom_inner_values_polynomial]: f |-> f(x) . f(y) is a
    polynomial function on Hom(U, V), Federer 1.10.4, p. 46: for an
    orthonormal base e of V it is sum_k (f(x) . e_k)(f(y) . e_k), 1.7.1,
    p. 28. Supporting lemma for 2.7.16, p. 136. *)
Lemma hom_inner_values_polynomial (x y : U) :
  is_polynomial_function (fun f : Hom U V => (B (f x) (f y) : R^o)).
Proof.
have [e [he hoe]] := orthonormal_basis_exists hB hb.
have ho := orthonormalisation_orthonormal hoe.
apply: (polynomial_function_eq (P := fun f => \sum_(k <- index_enum 'I_n)
  (hom_inner_coordinate x (e k) f * hom_inner_coordinate y (e k) f : R^o))).
  by move=> f; rewrite (inner_orthonormal_expansion he ho).
apply: polynomial_big_sum=> k.
apply: polynomial_mul.
  exact: (polynomial_linear (GRing.Linear.clone _ _ _ _ (hom_inner_coordinate x (e k)) _)).
exact: (polynomial_linear (GRing.Linear.clone _ _ _ _ (hom_inner_coordinate y (e k)) _)).
Qed.

(** Source for [hom_wedge_square_polynomial]: "the polynomial equation
    |f(e_1) wedge ... wedge f(e_m)|^2 = 0", Federer 2.7.16, p. 136: the
    function is polynomial in the sense of 1.10.4, p. 46, by the
    permutation formula of 1.7.5, pp. 31–32
    (exterior_inner_product_permutations). Direct formalisation. *)
Theorem hom_wedge_square_polynomial : is_polynomial_function (fun f : Hom U V => (hom_wedge_square f : R^o)).
Proof.
apply: (polynomial_function_eq (P := fun f : Hom U V =>
  \sum_(s <- index_enum 'S_m) (FedererPermutation.index R s *:
    (foldr *%R 1 [seq (B (f (c (s i))) (f (c i)) : R^o) | i <- enum 'I_m] : R^o)))).
  move=> f; rewrite /hom_wedge_square /hom_wedge (exterior_inner_product_permutations h2 hB).
  by apply: eq_bigr.
apply: polynomial_big_sum=> s.
apply: polynomial_scale.
apply: (@polynomial_foldr_mul R (Hom U V) _ (enum 'I_m) (fun i (f : Hom U V) => (B (f (c (s i))) (f (c i)) : R^o))).
move=> i; exact: hom_inner_values_polynomial.
Qed.

(** Source for [hom_wedge_square_continuous]: f |-> |f(e_1) wedge ...
    wedge f(e_m)|^2 is continuous on X, Federer 2.7.16, p. 136, being a
    polynomial function on a finite dimensional inner product space
    (PolynomialContinuity.v). Supporting lemma. *)
Lemma hom_wedge_square_continuous : continuous (fun f : X => (hom_wedge_square f : R^o)).
Proof.
exact: (@finite_inner_polynomial_continuous R (Hom U V) _ (hom_inner_productP hC hB hc) _ _
  (hom_rank_one_baseP hc hb) _ hom_wedge_square_polynomial).
Qed.

(** Source for [hom_monomorphisms_open]: "the monomorphisms form an
    open subset of X", Federer 2.7.16, p. 136: they are the points where
    the continuous function |f(e_1) wedge ... wedge f(e_m)|^2 does not
    vanish. Direct formalisation. *)
Theorem hom_monomorphisms_open : open hom_monomorphisms.
Proof.
have -> : hom_monomorphisms = (fun f : X => (hom_wedge_square f : R^o)) @^-1` [set r : R^o | r != 0].
  apply/seteqP; split=> f /=.
  - move=> hf; apply/eqP=> h0; exact: (hom_wedge_square_eq0 f).1 h0 hf.
  - by move=> /eqP h0; apply: contrapT=> hf; apply: h0; exact: (hom_wedge_square_eq0 f).2.
apply: (continuousP _).1; first exact: hom_wedge_square_continuous.
exact: open_neq.
Qed.

Hypothesis hmn : (m <= n)%N.

(** Source for [hom_standard_monomorphism]: the map x |-> sum_k
    e_k*(x) v_k of U into V, univalent for m <= n, supporting "the
    monomorphisms" of Federer 2.7.16, p. 136. Definition. *)
Definition hom_standard_monomorphism : Hom U V :=
  \sum_k hom_with_coefficient (b (widen_ord hmn k)) (dual_basis hc k).

(** Source for [hom_standard_monomorphism_coordinates]: the k-th
    coordinate of sum_j e_j*(x) v_j with respect to v is e_k*(x),
    Federer 1.1.4, p. 11; supporting 2.7.16, p. 136. Supporting lemma. *)
Lemma hom_standard_monomorphism_coordinates (z : U) (k : 'I_m) :
  dual_basis hb (widen_ord hmn k) (hom_standard_monomorphism z) = dual_basis hc k z.
Proof.
rewrite /hom_standard_monomorphism hom_sum_coefficientsE -hom_as_linearE linear_sum.
under eq_bigr do rewrite hom_with_coefficientE linearZ_LR hom_as_linearE dual_basisE.
rewrite (bigD1 k) //= big1.
  by rewrite eqxx; change (dual_basis hc k z * 1 + 0 = dual_basis hc k z); rewrite mulr1 addr0.
move=> j hj; have hne : (widen_ord hmn j == widen_ord hmn k) = false.
  by rewrite -val_eqE /= val_eqE (negbTE hj).
by rewrite hne; change (dual_basis hc j z * 0 = 0); rewrite mulr0.
Qed.

(** Source for [hom_standard_monomorphism_injective]: the map
    x |-> sum_k e_k*(x) v_k is univalent, Federer 1.1.4, p. 11:
    its coordinates recover e_k*(x); supporting "the monomorphisms",
    2.7.16, p. 136. Supporting lemma. *)
Lemma hom_standard_monomorphism_injective : injective (hom_standard_monomorphism : Hom U V).
Proof.
move=> x y hxy.
rewrite (basis_vector_expansion hc x) (basis_vector_expansion hc y); apply: eq_bigr=> k _.
by rewrite -!hom_standard_monomorphism_coordinates hxy.
Qed.

(** Source for [hom_monomorphisms_complement_null]: "the monomorphisms
    form an open subset of X whose complement has phi measure 0",
    Federer 2.7.16, p. 136, for m <= n and every Haar measure phi of the
    additive group of X: phi(S) = c L^N(Phi^{-1}(S)) for the isometry
    Phi of R^N onto X (FiniteHaarLinear.v), and Phi^{-1} of the
    complement is the zero set of the polynomial function
    |Phi(x)(e_1) wedge ... wedge Phi(x)(e_m)|^2, which does not vanish at
    Phi^{-1}(x |-> sum_k e_k*(x) v_k), hence is L^N null by 2.6.5,
    p. 120. Direct formalisation. *)
Theorem hom_monomorphisms_complement_null (phi : set X -> \bar R) :
  is_left_haar_measure (fun f g : X => f + g) phi -> phi (~` hom_monomorphisms) = 0%:E.
Proof.
move=> hphi.
have [e [he hoe]] := orthonormal_basis_exists (hom_inner_productP hC hB hc) (hom_rank_one_baseP hc hb).
have ho := orthonormalisation_orthonormal hoe.
have [k hk hkS] := finite_haar_measure_lebesgue (hom_inner_productP hC hB hc) he ho hphi.
pose Phi : {linear R_n R #|{: 'I_m * 'I_n}| -> Hom U V} :=
  GRing.Linear.clone _ _ _ _ (orthonormal_synthesis e) _.
have hP : is_polynomial_function (fun x : R_n R #|{: 'I_m * 'I_n}| => (hom_wedge_square (Phi x) : R^o)).
  exact: (polynomial_linear_precompose Phi hom_wedge_square_polynomial).
pose P := @PolynomialMap R (R_n R #|{: 'I_m * 'I_n}|) R^o _ (introT (asboolP _) hP).
have hnz : exists x, P x <> 0.
  exists (orthonormal_analysis (hom_inner hC hB hc) e hom_standard_monomorphism).
  rewrite /P /= /Phi /=.
  rewrite (orthonormal_analysisK (hom_inner_productP hC hB hc) he ho).
  move=> h0; apply: ((hom_wedge_square_eq0 _).1 h0).
  exact: hom_standard_monomorphism_injective.
have hnull := euclidean_polynomial_zero_set_null hnz.
rewrite hkS.
have -> : (orthonormal_synthesis e : _ -> X) @^-1` (~` hom_monomorphisms) = [set x | P x = 0].
  apply/seteqP; split=> x /=.
  - by move=> hx; apply/(hom_wedge_square_eq0 _).2.
  - by move=> hx; apply/(hom_wedge_square_eq0 _).1.
by rewrite hnull mule0.
Qed.

(** Source for [hom_monomorphisms_transitive]: "Moreover G acts
    transitively on the set of monomorphisms", Federer 2.7.16, p. 136,
    for m <= n: for monomorphisms f_1, f_2 the families f_1(e_k) and
    f_2(e_k) are independent and extend to bases v, w of V (1.6.1,
    p. 23); the map g with g(v_i) = w_i is univalent and g o f_1 = f_2.
    Direct formalisation. *)
Theorem hom_monomorphisms_transitive (f1 f2 : X) :
  hom_monomorphisms f1 -> hom_monomorphisms f2 ->
  exists g : GL, hom_linear_group_action hC hc hB hb g f1 = f2.
Proof.
move=> h1 h2.
have hi1 := finite_independent_map (f := hom_as_linear f1) h1 (finite_basis_independent hc).
have hi2 := finite_independent_map (f := hom_as_linear f2) h2 (finite_basis_independent hc).
have [v [hv hv1]] := finite_basis_extension_fixed hmn hi1 hb.
have [w [hw hw2]] := finite_basis_extension_fixed hmn hi2 hb.
pose g : Hom V V := \sum_i hom_with_coefficient (w i) (dual_basis hv i).
have hgv i : (g : Hom V V) (v i) = w i.
  rewrite /g hom_sum_coefficientsE.
  under eq_bigr do rewrite hom_with_coefficientE dual_basisE.
  rewrite (bigD1 i) //= eqxx scale1r big1 ?addr0 // => j hj.
  by rewrite eq_sym (negbTE hj) scale0r.
have hgi : injective (g : Hom V V).
  move=> x y hxy.
  have hg z : (g : Hom V V) z = \sum_i (dual_basis hv i z : R) *: w i.
    by rewrite /g hom_sum_coefficientsE; apply: eq_bigr=> i _; rewrite hom_with_coefficientE.
  have hz : \sum_i ((dual_basis hv i x : R) - dual_basis hv i y) *: w i = 0.
    under eq_bigr do rewrite scalerBl.
    by rewrite sumrB -!hg hxy subrr.
  rewrite (basis_vector_expansion hv x) (basis_vector_expansion hv y); apply: eq_bigr=> i _.
  have := finite_basis_independent hw hz i.
  by move/eqP; rewrite subr_eq0=> /eqP ->.
exists (exist _ (g : inner_metric_space (hom_inner_productP hB hB hb)) (mem_set hgi)).
apply: hom_ext=> x; rewrite /hom_linear_group_action /=.
apply: (basis_linear_ext hc (hom_as_linear (hom_comp g (f1 : Hom U V))) (hom_as_linear (f2 : Hom U V))) => k.
rewrite !hom_as_linearE hom_compE.
have e1 : (f1 : Hom U V) (c k) = v (widen_ord hmn k) by rewrite hv1.
have e2 : (f2 : Hom U V) (c k) = w (widen_ord hmn k) by rewrite hw2.
by rewrite e1 hgv e2.
Qed.

End Monomorphisms.

Arguments hom_monomorphisms {R U V C} hC {m c} hc {B} hB.
Arguments hom_monomorphisms_open {R U V C} hC {m c} hc {B} hB {n b} hb.
Arguments hom_monomorphisms_transitive {R U V C} hC {m c} hc {B} hB {n b} hb hmn {f1 f2} _ _.
Arguments hom_monomorphisms_complement_null {R U V C} hC {m c} hc {B} hB {n b} hb hmn {phi} _.
Arguments hom_wedge_square_eq0 {R U V m c} hc {B} hB f.
