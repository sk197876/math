(** Federer (1969), 2.7.16, example (2), printed p. 137: "On the other hand
    the linear isomorphism wedge^1: Hom(V, V) ~ Hom(wedge^1 V, wedge^1 V)
    maps G onto the group G' of all linear automorphisms of wedge^1 V, and
    (wedge^1)_# phi is a Haar measure of the additive group of Hom(wedge^1
    V, wedge^1 V), hence (wedge^1)_# phi is a left |det|^{-n} covariant
    measure over G'." Here V has an inner product B and a finite base b,
    wedge^1 V is the dual space Hom(V, R) (1.4.1, p. 17), with the inner
    product of 1.7.9, p. 35, for the scalar product of R and the base b, and
    its dual base; wedge^1 h is omega |-> omega o h (dual_map of
    BlockDeterminant.v). No inner product is used to identify V with wedge^1
    V. The module proves: a linear map between finite dimensional inner
    product spaces is continuous (finite_linear_continuous); the image of a
    Haar measure under an additive homeomorphism is a Haar measure
    (additive_homeomorphism_haar_measure, 2.7.2, p. 122, 2.5.19, p. 113, and
    RegularPushforwardBijection.v); h |-> wedge^1 h is a linear
    homeomorphism of Hom(V, V) onto Hom(wedge^1 V, wedge^1 V), with inverse
    k |-> (x |-> sum_i k(b*_i)(x) b_i) (exterior_one_homeomorphism), mapping
    G onto G' (exterior_one_linear_group, by det(wedge^1 h) = det h); hence
    (wedge^1)_# phi is a Haar measure of the additive group of Hom(wedge^1
    V, wedge^1 V) (exterior_one_haar_measure) and its restriction to G' is a
    left |det|^{-n} covariant measure over G'
    (exterior_one_haar_measure_left_covariant). The commutative diagram
    wedge^1(h g^{-1}) = (wedge^1 g)^{-1} o wedge^1 h and the identity
    |det(wedge^1 g)^{-1}|^{-n} = |det g|^n are formalised
    (exterior_one_diagram, exterior_one_inverse_det); the conclusion that
    phi is right |det|^n covariant is obtained in LinearGroupUnimodular.v
    and LinearGroupHaarMeasure.v by computing the determinant of f |-> f o
    g^{-1}, not by transporting the covariance over G' back to G; the
    continuity of linear maps rests on the estimate of
    FiniteNormUpperBound.v (1.10.5, p. 48). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric InnerNormedTopology ScalarInnerProduct RealNormUP
  FiniteNormUpperBound LinearBasis OrthonormalFamilies OrthonormalisationUP GramSchmidt
  FiniteDualDimension Annihilator Hom HomInner CoefficientCoordinates TensorUP ExteriorDeterminant
  BlockDeterminant HomCompositionDeterminant MeasureUP MeasurePushforward CompactSupportFunctionUP
  FunctionLatticeRegularityUP RealIntegralFunctionalUP MonotoneDaniellIntegralUP HomeomorphismUP
  ProperMapUP DaniellSpacePushforward EquivariantPushforward RegularPushforwardBijection
  CovariantIntegralUP HaarIntegralUP HomSpaceTopology LinearGroupTopology LinearGroupSealed
  EuclideanLinearMaps HomHaarCovariance LinearGroupUnimodular OpenSubspaceMeasure LinearGroupHaarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FiniteLinearContinuity.
Variable R : realType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable C : W -> W -> R.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation X := (inner_metric_space hB).
Local Notation Y := (inner_metric_space hC).

(** Source for [finite_linear_continuous]: a linear map L of a finite
    dimensional inner product space into an inner product space is
    continuous, since |L(x)| <= c |x| with c = sum_i |L(e_i)| for an
    orthonormal base e (1.10.5, p. 48); supporting "the linear
    isomorphism wedge^1: Hom(V, V) ~ Hom(wedge^1 V, wedge^1 V)" as a
    homeomorphism, Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma finite_linear_continuous (L : {linear V -> W}) : continuous (L : X -> Y).
Proof.
pose N (x : V) := inner_norm hC (L x).
have hN : is_real_seminorm N.
  split.
  - by move=> x; exact: inner_norm_nonnegative.
  - by move=> a x; rewrite /N linearZ inner_normZ.
  - move=> x y; rewrite /N linearD.
    have h := ler_normD (L x : Y) (L y : Y).
    by rewrite !inner_norm_topologyE in h.
have [u [hu ho]] := orthonormal_basis_exists hB hb.
pose c := \sum_i N (u i).
have hc : 0 <= c by apply: sumr_ge0=> i _; exact: real_seminorm_nonnegative hN (u i).
have hbound x : N x <= c * inner_norm hB x.
  exact (@finite_seminorm_inner_upper_bound R V B hB N hN n u hu (orthonormalisation_orthonormal ho) x).
move=> x; apply/cvgrPdist_lt; first exact: nbhs_filter.
move=> eps he.
have hD : 0 < c + 1 by rewrite addrC ltr_pwDl.
have hd : 0 < eps / (c + 1) by rewrite divr_gt0.
have hn : \forall y \near (nbhs x), inner_norm hB (x - y) < eps / (c + 1).
  have hi : (fun y : X => y) @ (nbhs x) --> x := cvg_id.
  exact (@cvgr_dist_lt R (PseudoMetricNormedZmod.clone R X _) X (nbhs x)
    (nbhs_filter x) (fun y : X => y) x hi _ hd).
apply: (filterS _ hn)=> y hy.
rewrite inner_norm_topologyE -linearB.
apply: le_lt_trans (hbound (x - y)) _.
have hcD : c <= c + 1 by rewrite lerDl ler01.
apply: le_lt_trans (ler_wpM2r (inner_norm_nonnegative hB (x - y)) hcD) _.
by rewrite mulrC -(@ltr_pdivlMr R (c + 1) (inner_norm hB (x - y)) eps hD).
Qed.

End FiniteLinearContinuity.

Arguments finite_linear_continuous {R V W B} hB {C} hC {n b} hb L.

Section AdditiveHaarPushforward.
Variable R : realType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable C : W -> W -> R.
Hypothesis hC : is_inner_product C.
Local Notation X := (inner_metric_space hB).
Local Notation Y := (inner_metric_space hC).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KY := (@compactly_supported_continuous_functions R Y).

(** Source for [additive_homeomorphism_haar_measure]: the image p_# phi
    of a Haar measure phi of the additive group of X under an additive
    homeomorphism p of X onto Y is a Haar measure of the additive group
    of Y, as in "(wedge^1)_# phi is a Haar measure of the additive group
    of Hom(wedge^1 V, wedge^1 V)", Federer 2.7.16, p. 137: p_#(mu) is a
    nonzero monotone invariant integral (2.7.2, p. 122, and 2.5.19,
    p. 113), represented by p_# phi, which is K(Y) regular because p is
    a bijection. Supporting theorem. *)
Theorem additive_homeomorphism_haar_measure (p : X -> Y) (q : Y -> X) (phi : set X -> \bar R) :
  (forall x y, p (x + y) = p x + p y) -> is_homeomorphism_with_inverse p q ->
  is_left_haar_measure (fun f g : X => f + g) phi ->
  is_left_haar_measure (fun f g : Y => f + g) (measure_pushforward p phi).
Proof.
move=> hp hpq [mu [hmu hm hi hr]].
have hqp := homeomorphism_with_inverse_symmetric hpq.
exists (daniell_pushforward p mu); split.
- have hA : is_nonzero_monotone_invariant_integral (fun (z : Y) (y : X) => q z + y) mu.
    case: hmu=> [[hd hl] hM hn]; split=> //; split=> // u z hu.
    exact: (hl u (q z) hu).
  apply: (equivariant_nonzero_invariant_forward hpq _ hA)=> z y.
  by rewrite /left_multiplication_action hp (homeomorphism_right_inverse hpq).
- exact: measure_pushforward_is_measure.
- exact: (daniell_pushforward_integral (homeomorphism_continuous hpq)
    (homeomorphism_with_inverse_proper hpq) hm hi).
- apply: (bijection_pushforward_regular (homeomorphism_left_inverse hpq)
    (homeomorphism_right_inverse hpq) _ hr)=> f hf.
  exact: (compactly_supported_compose (homeomorphism_continuous hqp)
    (homeomorphism_with_inverse_proper hqp) hf).
Qed.

End AdditiveHaarPushforward.

Section ExteriorOne.
Variable R : realType.
Local Notation h2 := (euclidean_two_nonzero R).
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation E := (Hom V R^o).
(** Source for [hD]: the inner product of wedge^1 V = Hom(V, R) of
    Federer 1.7.9, p. 35, for B and the scalar product of R, used to
    give Hom(wedge^1 V, wedge^1 V) its topology in 2.7.16, p. 137. *)
Let hD := hom_inner_productP hB (scalar_inner_productP R) hb.
Local Notation db := (dual_basisP hb).
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation H' := (inner_metric_space (hom_inner_productP hD hD db)).

(** Source for [exterior_one_fun]: h |-> wedge^1 h, omega |-> omega o h,
    the linear isomorphism wedge^1: Hom(V, V) ~ Hom(wedge^1 V,
    wedge^1 V) of Federer 2.7.16, p. 137, through dual_map. Definition
    of the function. *)
Definition exterior_one_fun (h : Hom V V) : Hom E E := hom_of_linear (dual_map (hom_as_linear h)).

(** Source for [exterior_one_funE]: (wedge^1 h)(omega) = omega o h,
    Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma exterior_one_funE (h : Hom V V) (omega : E) : exterior_one_fun h omega = hom_comp omega h.
Proof. by apply: hom_ext=> x. Qed.

(** Source for [exterior_one_linear]: h |-> wedge^1 h is linear, Federer
    2.7.16, p. 137, "the linear isomorphism wedge^1". Supporting lemma. *)
Lemma exterior_one_linear : linear exterior_one_fun.
Proof.
move=> a h k; apply: hom_ext=> omega.
rewrite hom_addE hom_scaleE !exterior_one_funE; apply: hom_ext=> x.
rewrite !(hom_addE, hom_scaleE, hom_compE).
have e := linearP (hom_as_linear omega) a (h x) (k x).
by rewrite !hom_as_linearE in e.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R (Hom V V) (Hom E E) *:%R
  exterior_one_fun exterior_one_linear.

(** Source for [exterior_one_inverse_fun]: the inverse of wedge^1,
    k |-> (x |-> sum_i k(b*_i)(x) b_i), b* the dual base, supporting "the
    linear isomorphism wedge^1", Federer 2.7.16, p. 137. Definition. *)
Definition exterior_one_inverse_fun (k : Hom E E) : Hom V V :=
  \sum_i hom_with_coefficient (b i) (k (dual_basis hb i)).

(** Source for [exterior_one_inverse_funE]: the values of the inverse of
    wedge^1, Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma exterior_one_inverse_funE (k : Hom E E) x :
  exterior_one_inverse_fun k x = \sum_i (k (dual_basis hb i) x : R) *: b i.
Proof.
by rewrite /exterior_one_inverse_fun hom_sum_coefficientsE; apply: eq_bigr=> i _; rewrite hom_with_coefficientE.
Qed.

(** Source for [exterior_one_inverse_linear]: the inverse of wedge^1 is
    linear, Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma exterior_one_inverse_linear : linear exterior_one_inverse_fun.
Proof.
move=> a k l; apply: hom_ext=> x.
rewrite hom_addE hom_scaleE !exterior_one_inverse_funE scaler_sumr -big_split.
apply: eq_bigr=> i _; rewrite !(hom_addE, hom_scaleE).
by rewrite scalerDl scalerA.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R (Hom E E) (Hom V V) *:%R
  exterior_one_inverse_fun exterior_one_inverse_linear.

(** Source for [exterior_one_inverseK]: the inverse undoes wedge^1,
    x = sum_i b*_i(h(x)) b_i, Federer 1.1.4, p. 11, supporting 2.7.16,
    p. 137. Supporting lemma. *)
Lemma exterior_one_inverseK : cancel exterior_one_fun exterior_one_inverse_fun.
Proof.
move=> h; apply: hom_ext=> x; rewrite exterior_one_inverse_funE.
rewrite [in RHS](basis_vector_expansion hb (h x)); apply: eq_bigr=> i _.
by rewrite exterior_one_funE hom_compE.
Qed.

(** Source for [exterior_one_funK]: wedge^1 undoes the inverse:
    omega(sum_i k(b*_i)(x) b_i) = k(sum_i omega(b_i) b*_i)(x) = k(omega)(x),
    Federer 1.1.4, p. 11, supporting 2.7.16, p. 137. Supporting lemma. *)
Lemma exterior_one_funK : cancel exterior_one_inverse_fun exterior_one_fun.
Proof.
move=> k; apply: hom_ext=> omega; apply: hom_ext=> x.
rewrite exterior_one_funE hom_compE exterior_one_inverse_funE.
rewrite [in RHS](dual_basis_expansion hb omega).
rewrite (linear_sum (hom_as_linear k)) hom_sum_coefficientsE.
rewrite (linear_sum (hom_as_linear omega)); apply: eq_bigr=> i _.
rewrite (linearZ_LR (hom_as_linear omega)) (linearZ_LR (hom_as_linear k)) hom_scaleE.
exact: mulrC.
Qed.

(** Source for [exterior_one_homeomorphism]: wedge^1 is a homeomorphism
    of Hom(V, V) onto Hom(wedge^1 V, wedge^1 V), a linear bijection of
    finite dimensional spaces, Federer 2.7.16, p. 137. Supporting
    theorem. *)
Theorem exterior_one_homeomorphism :
  is_homeomorphism_with_inverse (exterior_one_fun : H -> H') (exterior_one_inverse_fun : H' -> H).
Proof.
split.
- have h := finite_linear_continuous (hom_inner_productP hB hB hb) (hom_inner_productP hD hD db)
    (hom_rank_one_baseP hb hb) (exterior_one_fun : {linear Hom V V -> Hom E E}).
  exact h.
- have h := finite_linear_continuous (hom_inner_productP hD hD db) (hom_inner_productP hB hB hb)
    (hom_rank_one_baseP db db) (exterior_one_inverse_fun : {linear Hom E E -> Hom V V}).
  exact h.
- exact: exterior_one_inverseK.
- exact: exterior_one_funK.
Qed.

(** Source for [exterior_one_linear_group]: "wedge^1 ... maps G onto the
    group G' of all linear automorphisms of wedge^1 V", Federer 2.7.16,
    p. 137: h is univalent if and only if wedge^1 h is, since
    det(wedge^1 h) = det h (dual_map_det, 1.3.4, p. 16), and every k in
    G' is wedge^1 of its inverse image. Direct formalisation. *)
Theorem exterior_one_linear_group :
  (forall h : H, linear_group hB hb h <-> linear_group hD db (exterior_one_fun h : H')) /\
  (forall k : H', linear_group hD db k -> exists2 h : H, linear_group hB hb h & exterior_one_fun h = k).
Proof.
have heq (h : H) : linear_group hB hb h <-> linear_group hD db (exterior_one_fun h : H').
  rewrite /linear_group /=.
  have e1 : injective (h : Hom V V) <-> injective (hom_as_linear h).
    by split=> hi x y; rewrite ?hom_as_linearE; exact: hi.
  have e2 : injective (exterior_one_fun h : Hom E E) <-> injective (dual_map (hom_as_linear h)).
    by split=> hi x y; [rewrite -!(hom_of_linearE (dual_map (hom_as_linear h)))|rewrite !hom_of_linearE];
      exact: hi.
  rewrite e1 e2 -(det_nonzero_injective h2 hb) -(det_nonzero_injective h2 db).
  by rewrite dual_map_det.
split=> // k hk; exists (exterior_one_inverse_fun k : H); last exact: exterior_one_funK.
by apply/heq; rewrite exterior_one_funK.
Qed.

(** Source for [exterior_one_comp]: wedge^1(a o c) = wedge^1 c o
    wedge^1 a, since omega o (a o c) = (omega o a) o c; the functoriality
    behind the commutative diagram of Federer 2.7.16, p. 137, with 1.4.1,
    p. 17. Supporting lemma. *)
Lemma exterior_one_comp (a c : Hom V V) :
  exterior_one_fun (hom_comp a c) = hom_comp (exterior_one_fun c) (exterior_one_fun a).
Proof.
apply: hom_ext=> omega; rewrite hom_compE !exterior_one_funE.
by apply: hom_ext=> x; rewrite !hom_compE.
Qed.

(** Source for [exterior_one_identity]: wedge^1 1_V = 1, Federer 1.4.1,
    p. 17; supporting the commutative diagram of 2.7.16, p. 137.
    Supporting lemma. *)
Lemma exterior_one_identity : exterior_one_fun (hom_identity V) = hom_identity E.
Proof.
apply: hom_ext=> omega; rewrite exterior_one_funE hom_identityE.
by apply: hom_ext=> x; rewrite hom_compE hom_identityE.
Qed.

(** Source for [exterior_one_diagram]: "For each g in G the diagram
    [right multiplication by g^{-1} on G, wedge^1 vertically, left
    multiplication by (wedge^1 g)^{-1} on G'] is commutative", Federer
    2.7.16, p. 137: wedge^1(h g^{-1}) = wedge^1(g^{-1}) o wedge^1 h, and
    wedge^1(g^{-1}) is the inverse of wedge^1 g. Direct formalisation. *)
Theorem exterior_one_diagram (g h : set_type (linear_group hB hb)) :
  [/\ exterior_one_fun (set_val (linear_group_mul hB hb h (linear_group_inv hB hb g)) : Hom V V) =
      hom_comp (exterior_one_fun (set_val (linear_group_inv hB hb g) : Hom V V))
        (exterior_one_fun (set_val h : Hom V V)),
    hom_comp (exterior_one_fun (set_val (linear_group_inv hB hb g) : Hom V V))
      (exterior_one_fun (set_val g : Hom V V)) = hom_identity E &
    hom_comp (exterior_one_fun (set_val g : Hom V V))
      (exterior_one_fun (set_val (linear_group_inv hB hb g) : Hom V V)) = hom_identity E].
Proof.
have hG := linear_group_operations hB hb.
split.
- by rewrite (linear_group_mulE hG) exterior_one_comp.
- by rewrite -exterior_one_comp (linear_group_invE_right hG) exterior_one_identity.
- by rewrite -exterior_one_comp (linear_group_invE hG) exterior_one_identity.
Qed.

(** Source for [exterior_one_inverse_det]: "|det(wedge^1 g)^{-1}|^{-n} =
    |det g|^n", Federer 2.7.16, p. 137, by det(wedge^1 h) = det h
    (dual_map_det, 1.3.4, p. 16) for h = g^{-1}. Direct
    formalisation. *)
Theorem exterior_one_inverse_det (g : set_type (linear_group hB hb)) :
  `|det h2 db (dual_map (hom_as_linear (set_val (linear_group_inv hB hb g) : Hom V V)))| ^- n =
    `|linear_group_det hB hb g| ^+ n.
Proof.
rewrite dual_map_det.
change (`|linear_group_det hB hb (linear_group_inv hB hb g)| ^- n = `|linear_group_det hB hb g| ^+ n).
by rewrite linear_group_det_inv normrV ?unitfE ?linear_group_det_nonzero // exprVn invrK.
Qed.

Variable phi : set H -> \bar R.
Hypothesis hphi : is_left_haar_measure (fun f g : H => f + g) phi.

(** Source for [exterior_one_haar_measure]: "(wedge^1)_# phi is a Haar
    measure of the additive group of Hom(wedge^1 V, wedge^1 V)", Federer
    2.7.16, p. 137. Direct formalisation. *)
Theorem exterior_one_haar_measure :
  is_left_haar_measure (fun f g : H' => f + g) (measure_pushforward (exterior_one_fun : H -> H') phi).
Proof.
apply: (additive_homeomorphism_haar_measure _ exterior_one_homeomorphism hphi)=> f g.
exact: (linearD (exterior_one_fun : {linear Hom V V -> Hom E E})).
Qed.

(** Source for [exterior_one_haar_measure_left_covariant]: "hence
    (wedge^1)_# phi is a left |det|^{-n} covariant measure over G'",
    Federer 2.7.16, p. 137: the restriction of (wedge^1)_# phi to the
    open set G' of linear automorphisms of wedge^1 V is a left
    |det|^{-n} covariant measure, by the first assertion of the case
    U = V applied to wedge^1 V (LinearGroupHaarMeasure.v). Direct
    formalisation. *)
Theorem exterior_one_haar_measure_left_covariant :
  is_left_covariant_measure (linear_group_mul hD db) (linear_group_character hD db)
    (open_subspace_measure (S := linear_group hD db) (measure_pushforward (exterior_one_fun : H -> H') phi)).
Proof. exact: linear_group_haar_measure_left_covariant exterior_one_haar_measure. Qed.

End ExteriorOne.
