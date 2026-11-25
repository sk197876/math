(** Allard (1972), 3.5, printed p. 432, and blueprint al:3.5:lem: the
    measurability of [x ↦ Tan^k(H^k ⌞ E, x)] rests on Federer 3.2.25, p. 261,
    which describes the approximate tangent plane through a simple unit
    k-vector ξ and its associated subspace T(ξ) = R^n ∩ {v : ξ ∧ v = 0}
    (Federer 1.6.1, p. 23). This module supplies the passage from ξ to the
    orthogonal projection of R^n onto T(ξ), a member of Allard's G(n, k)
    (Allard 2.3, p. 421), and proves that it is continuous on the whole
    exterior power.

    For ξ ∈ ∧_k R^n and v, w ∈ R^n set
      c_ξ(v, w) = v • w - ⟨ξ ∧ v, ξ ∧ w⟩,
    where ⟨·,·⟩ is the inner product of ∧_{k+1} R^n of Federer 1.7.5, p. 32,
    and let P(ξ) ∈ Hom(R^n, R^n) be the linear map with P(ξ)(v) • w =
    c_ξ(v, w), that is P(ξ) = Σ_{i,j} c_ξ(e_i, e_j) (e_i^* · e_j) for the
    standard basis e_1, …, e_n, with the rank-one maps ω · b of Allard
    [All72, 2.3(4)]. The map [ξ ↦ P(ξ)] is continuous, since
    4 ⟨ξ ∧ v, ξ ∧ w⟩ = |ξ ∧ (v + w)|^2 - |ξ ∧ (v - w)|^2 and
    |ξ ∧ a| ≤ |ξ| |a| (Federer 1.7.5, p. 32). If ξ is simple and |ξ| = 1,
    then ξ = c u_1 ∧ … ∧ u_k with u orthonormal (Federer 1.7.5), T(ξ) is the
    span of u (Federer 1.6.1, p. 24), ξ ∧ v = ξ ∧ (v - Q(v)) for the
    orthogonal projection Q onto T(ξ), and |ξ ∧ a| = |ξ| |a| = |a| whenever
    a is orthogonal to T(ξ) (the equality case of Federer 1.7.5). By
    polarisation c_ξ(v, w) = v • w - (v - Q(v)) • (w - Q(w)) = Q(v) • w;
    hence P(ξ) = Q. The principal results are
    - [simple_projection_hom_continuous]: [ξ ↦ P(ξ)] is continuous from
      ∧_k R^n to Hom(R^n, R^n), both with the inner products of Federer
      1.7.5 and 1.7.9;
    - [simple_projection_hom_projector] and [simple_projection_hom_image]:
      for a simple unit k-vector ξ, P(ξ) is an orthogonal projector of rank
      k whose image is T(ξ).
    The same identity appears in the proof of Federer 2.7.16, example (6),
    p. 139, as |ζ ∧ η| = |⟨ζ, ∧_m q⟩| with ker q = T(η); here it is proved
    from the orthonormal factorisation instead. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From mathcomp.analysis.normedtype_theory Require Import pseudometric_normed_Zmodule normed_module.
From mathcomp Require Import ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates CoordinateProjection
  EuclideanCoordinateTopology EuclideanLinearMaps InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  LinearBasis TensorUP Hom HomInner Bilinear OrthonormalFamilies FiniteSpans InnerOrthogonality
  ExteriorGrading ExteriorPowers ExteriorHomogeneousProducts InnerExterior InnerExteriorPositivity ExteriorNorm
  AssociatedSubspace SimpleElementary SimpleProducts SimpleOrthonormalFactor SimpleWedgeNorm
  SimpleWedgeEquality ProductAssociatedOrthogonality ExteriorDegreeOneNorm NormDifferentialUP
  InnerCartesianContinuousMaps RealMetricBackground OrthonormalProjection ModuleQuotient
  GradedComponents FiniteExteriorPowers ExteriorAlgebra.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SimpleProjection.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation Bn := (@euclidean_inner_product R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation h2 := (euclidean_two_nonzero R).
Local Notation e := (@coordinate_basis R n).
Local Notation first := (exterior_first_inclusion Rn).
Local Notation EI := (@exterior_inner_form R h2 Rn Bn hBn (k + 1)).
Local Notation L := (inner_metric_space (@exterior_inner_productP R h2 Rn Bn hBn k)).
Local Notation HEn := (inner_metric_space (hom_inner_productP hBn hBn hbn)).

Local Notation Ek := (@exterior_inner_productP R h2 Rn Bn hBn k).
Local Notation E1 := (@exterior_inner_productP R h2 Rn Bn hBn (k + 1)).
Local Notation L1 := (inner_metric_space E1).

(** Source for [simple_tangent_form]: the form c_ξ(v, w) = v • w - ⟨ξ ∧ v,
    ξ ∧ w⟩ on R^n, with the exterior inner product of Federer 1.7.5, p. 32,
    and the order ξ ∧ v of the associated subspace of Federer 1.6.1, p. 23;
    supporting Allard 3.5, p. 432. Definition. *)
Definition simple_tangent_form (xi : exterior_power Rn k) (v w : Rn) : R^o :=
  Bn v w - EI (exterior_product xi (first v)) (exterior_product xi (first w)).

(** Source for [linear_predicate_sum]: a map satisfying the linearity
    predicate of Federer 1.1.1, p. 8, commutes with finite sums. Supporting
    lemma. *)
Lemma linear_predicate_sum (U Z : lmodType R) (f : U -> Z) (hf : linear f) (I : Type) (r : seq I)
    (P : pred I) (F : I -> U) :
  f (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) f (F i).
Proof. exact: (big_morph f (linD hf) (lin0 hf)). Qed.

(** Source for [simple_tangent_form_bilinear]: c_ξ is bilinear, by the
    bilinearity of the inner products (Federer 1.7.1, p. 28, and 1.7.5,
    p. 32) and of the exterior multiplication (Federer 1.3.1, p. 13).
    Supporting lemma. *)
Lemma simple_tangent_form_bilinear xi : TensorUP.bilinear (simple_tangent_form xi).
Proof.
have hx := proj2 (@exterior_product_bilinear R Rn k 1) xi.
have hE := inner_bilinear E1.
have hB := inner_bilinear hBn.
split.
- move=> w a x y; rewrite /simple_tangent_form linearP (linD hx) (linZ hx).
  rewrite (bilDl hE) (bilZl hE) (bilDl hB) (bilZl hB).
  by rewrite scalerBr opprD addrACA.
- move=> v a x y; rewrite /simple_tangent_form linearP (linD hx) (linZ hx).
  rewrite (bilDr hE) (bilZr hE) (bilDr hB) (bilZr hB).
  by rewrite scalerBr opprD addrACA.
Qed.

(** Source for [simple_projection_hom]: P(ξ) = Σ_{i,j} c_ξ(e_i, e_j)
    (e_i^* · e_j) ∈ Hom(R^n, R^n), with the rank-one maps of Allard 2.3(4),
    p. 422; for a simple unit k-vector ξ it is the orthogonal projection
    onto T(ξ), Allard 2.3, p. 421, and Federer 1.6.1, p. 23. Definition. *)
Definition simple_projection_hom (xi : exterior_power Rn k) : Hom Rn Rn :=
  \sum_i \sum_j simple_tangent_form xi (e i) (e j) *:
    rank_one_map (hom_of_linear (inner_coordinate hBn (e i))) (e j).

(** Source for [hom_sum_eval]: the value of a finite sum of linear maps is
    the sum of their values, Federer 1.4.1, p. 17. Supporting lemma. *)
Lemma hom_sum_eval (I : Type) (r : seq I) (P : pred I) (F : I -> Hom Rn Rn) x :
  (\sum_(i <- r | P i) F i) x = \sum_(i <- r | P i) F i x.
Proof.
apply: (big_morph (fun f : Hom Rn Rn => f x)); [move=> f g; exact: hom_addE|exact: hom_zeroE].
Qed.

(** Source for [simple_projection_homE]: P(ξ)(v) = Σ_j c_ξ(v, e_j) e_j,
    by the expansion v = Σ_i v_i e_i of Federer 1.7.1, p. 28. Supporting
    lemma. *)
Lemma simple_projection_homE xi v :
  simple_projection_hom xi v = \sum_j simple_tangent_form xi v (e j) *: e j.
Proof.
rewrite /simple_projection_hom hom_sum_eval.
under eq_bigr=> i _ do rewrite hom_sum_eval.
rewrite exchange_big; apply: eq_bigr=> j _.
have hv := euclidean_coordinate_expansion v.
rewrite -[in RHS]hv (linear_predicate_sum (proj1 (simple_tangent_form_bilinear xi) (e j))) scaler_suml.
apply: eq_bigr=> i _; rewrite hom_scaleE rank_one_mapE hom_of_linearE inner_coordinateE.
rewrite euclidean_inner_basis scalerA (bilZl (simple_tangent_form_bilinear xi)).
by rewrite mulrC.
Qed.

(** Source for [simple_projection_hom_inner]: P(ξ)(v) • w = c_ξ(v, w) for
    v, w ∈ R^n, Federer 1.7.1, p. 28. Supporting lemma. *)
Lemma simple_projection_hom_inner xi v w :
  Bn (simple_projection_hom xi v) w = simple_tangent_form xi v w.
Proof.
rewrite simple_projection_homE (linear_predicate_sum (proj1 (inner_bilinear hBn) w)).
have hw := euclidean_coordinate_expansion w.
rewrite -[in RHS]hw (linear_predicate_sum (proj2 (simple_tangent_form_bilinear xi) v)).
apply: eq_bigr=> j _; rewrite (bilZl (inner_bilinear hBn)) (bilZr (simple_tangent_form_bilinear xi)).
rewrite (inner_symmetric hBn (coordinate_basis R j) w) euclidean_inner_basis.
by rewrite /GRing.scale /= mulrC.
Qed.


(** Source for [exterior_first_simple]: every vector, regarded as a
    1-vector, is simple, Federer 1.6.1, p. 23. Supporting lemma. *)
Lemma exterior_first_simple (a : Rn) : simple (first a).
Proof. by exists [tuple a]; rewrite exterior_first_word. Qed.

(** Source for [right_first_wedge_continuous]: [ξ ↦ ξ ∧ a] is continuous
    from ∧_k R^n to ∧_{k+1} R^n, since |ξ ∧ a| ≤ |ξ| |a| by Federer 1.7.5,
    p. 32. Supporting lemma. *)
Lemma right_first_wedge_continuous (a : Rn) :
  continuous (fun xi : L => (exterior_product xi (first a) : L1)).
Proof.
pose f : Hom (exterior_power Rn k) (exterior_power Rn (k + 1)) :=
  HomMap (asboolT (proj1 (@exterior_product_bilinear R Rn k 1) (first a))).
have h := @inner_bounded_linear_continuous R _ _ _ _ Ek E1 f.
apply: h; exists (exterior_norm h2 hBn (first a)); split; first exact: exterior_norm_nonnegative.
move=> x; rewrite mulrC.
exact: (@simple_right_wedge_norm_bound R h2 Rn Bn hBn k 1 x (first a) (exterior_first_simple a)).
Qed.

(** Source for [right_first_wedge_norm_continuous]: [ξ ↦ |ξ ∧ a|] is
    continuous on ∧_k R^n, Federer 1.7.5, p. 32. Supporting lemma. *)
Lemma right_first_wedge_norm_continuous (a : Rn) :
  continuous (fun xi : L => (exterior_norm h2 hBn (exterior_product xi (first a)) : real_line_metric R)).
Proof.
move=> xi.
have hn : {for (exterior_product xi (first a) : L1),
    continuous (fun y : L1 => (exterior_norm h2 hBn y : real_line_metric R))}.
  have h := @norm_continuous R L1 (exterior_product xi (first a)).
  have he' : (fun y : L1 => (exterior_norm h2 hBn y : real_line_metric R)) = (fun y : L1 => `|y|).
    by apply: funext=> y; rewrite inner_norm_topologyE.
  by rewrite he'.
exact: (continuous_comp (@right_first_wedge_continuous a xi) hn).
Qed.

(** Source for [inner_polarisation]: 4 C(x, y) = |x + y|^2 - |x - y|^2 for
    an inner product C, Federer 1.7.1, p. 28. Supporting lemma. *)
Lemma inner_polarisation (V : lmodType R) (C : V -> V -> R) (hC : is_inner_product C) x y :
  C x y = (inner_norm hC (x + y) ^+ 2 - inner_norm hC (x - y) ^+ 2) / 4%:R.
Proof.
have hbil := inner_bilinear hC.
have hsum (u w : V) : C (u + w) (u + w) = C u u + (C u w + C u w) + C w w.
  rewrite (bilDl hbil) !(bilDr hbil) (inner_symmetric hC w u); ring.
have hdif (u w : V) : C (u - w) (u - w) = C u u - (C u w + C u w) + C w w.
  rewrite (bilBl hbil) !(bilBr hbil) (inner_symmetric hC w u); ring.
rewrite !inner_norm_sqr hsum hdif.
have h4 : (4%:R : R) != 0 by rewrite pnatr_eq0.
by apply: (mulIf h4); rewrite divfK //; ring.
Qed.

(** Source for [simple_tangent_form_continuous]: [ξ ↦ c_ξ(v, w)] is
    continuous on ∧_k R^n, by polarisation and
    [right_first_wedge_norm_continuous]. Supporting lemma. *)
Lemma simple_tangent_form_continuous v w :
  continuous (fun xi : L => (simple_tangent_form xi v w : R^o)).
Proof.
have hx xi := proj2 (@exterior_product_bilinear R Rn k 1) xi.
have he : (fun xi : L => (simple_tangent_form xi v w : R^o)) =
    (fun xi : L => Bn v w - (exterior_norm h2 hBn (exterior_product xi (first (v + w))) *
      exterior_norm h2 hBn (exterior_product xi (first (v + w))) -
      exterior_norm h2 hBn (exterior_product xi (first (v - w))) *
      exterior_norm h2 hBn (exterior_product xi (first (v - w)))) / 4%:R).
  apply: funext=> xi; rewrite /simple_tangent_form (inner_polarisation E1) !expr2.
  by rewrite -(linD (hx xi)) -(linB (hx xi)) -linearD -linearB.
rewrite he=> xi.
have h1 := @right_first_wedge_norm_continuous (v + w) xi.
have h2' := @right_first_wedge_norm_continuous (v - w) xi.
apply: (@continuousB R R^o L _ _ xi (@cst_continuous L R^o _ xi)).
apply: (@continuousM R L _ (fun _ : L => 4%:R^-1) xi); last exact: cst_continuous.
apply: (@continuousB R R^o L _ _ xi); exact: (@continuousM R L _ _ xi).
Qed.

(** Source for [simple_projection_hom_continuous]: [ξ ↦ P(ξ)] is
    continuous from ∧_k R^n to Hom(R^n, R^n), with the inner products of
    Federer 1.7.5, p. 32, and 1.7.9, p. 35; supporting the measurability of
    [x ↦ Tan^k(H^k ⌞ E, x)] in Allard 3.5, p. 432, via Federer 3.2.25,
    p. 261. *)
Lemma simple_projection_hom_continuous :
  continuous (fun xi : L => (simple_projection_hom xi : HEn)).
Proof.
apply: continuous_big; first exact: add_continuous.
move=> i _; apply: continuous_big; first exact: add_continuous.
move=> j _ xi.
apply: (@continuousZ R HEn L (fun x : L => (simple_tangent_form x (e i) (e j) : R))
  (fun _ : L => (rank_one_map (hom_of_linear (inner_coordinate hBn (e i))) (e j) : HEn)) xi).
- exact: (@simple_tangent_form_continuous (e i) (e j) xi).
- exact: cst_continuous.
Qed.


(** Source for [associated_right_first_wedge]: ξ ∧ w = 0 whenever w
    belongs to the associated subspace T(ξ), Federer 1.6.1, p. 23.
    Supporting lemma. *)
Lemma associated_right_first_wedge (xi : exterior_power Rn k) w : FedererSimple.T xi w -> exterior_product xi (first w) = 0.
Proof.
move=> hw; apply: val_inj.
change (wedge (component_val xi) (exterior_degree 1 (exterior_generator w)) =
  component_val (0 : exterior_power Rn (k + 1))).
rewrite exterior_generator_homogeneous.
have hz : wedge (component_val xi) (exterior_generator w) = 0 := hw.
by rewrite hz linear0.
Qed.

(** Source for [frame_right_first_wedge_norm]: if ξ = c u_1 ∧ … ∧ u_k is
    simple with |ξ| = 1 and a is orthogonal to u_1, …, u_k, then
    |ξ ∧ a| = |a|; this is the equality case of Federer 1.7.5, p. 32,
    together with T(ξ) = span u, Federer 1.6.1, p. 24. Supporting lemma. *)
Lemma frame_right_first_wedge_norm (xi : exterior_power Rn k) (u : 'I_k -> Rn) (c : R) (a : Rn) :
  simple xi -> c != 0 -> xi = c *: e_lambda u (ord_tuple k) -> exterior_norm h2 hBn xi = 1 ->
  (forall i, Bn (u i) a = 0) -> inner_norm E1 (exterior_product xi (first a)) = inner_norm hBn a.
Proof.
move=> hs hc hxi h1 ha.
have hxp := proj2 (@exterior_product_bilinear R Rn k 1) xi.
have [->|ha0] := eqVneq a 0.
  by rewrite linear0 (lin0 hxp) !inner_norm0.
have hx0 : xi != 0.
  by apply/eqP=> hz; move: h1; rewrite hz exterior_norm_zero=> /eqP; rewrite eq_sym oner_eq0.
have hue : e_lambda u (ord_tuple k) != 0.
  by apply/eqP=> hz; move: hx0; rewrite hxi hz scaler0 eqxx.
have hfa : first a = e_lambda (tnth [tuple a]) (ord_tuple 1).
  by rewrite exterior_first_word tuple_product.
have hf0 : first a != 0.
  apply/eqP=> hz; have hn := exterior_first_norm h2 hBn a.
  rewrite hz exterior_norm_zero in hn.
  by move: ha0; rewrite -(inner_norm_eq0 hBn) -hn eqxx.
have heq := simple_wedge_norm_equality h2 hBn hx0 hf0 hs (exterior_first_simple a).
change (exterior_norm h2 hBn (exterior_product xi (first a)) = inner_norm hBn a).
rewrite (proj2 heq _); last first.
  move=> s t hs' ht.
  have hsu : FedererSimple.T (e_lambda u (ord_tuple k)) s.
    apply: (proj1 (associated_scale_nonzero _ hc s)); by rewrite -hxi.
  rewrite hfa in ht hf0.
  apply: (proj2 (product_associated_orthogonality h2 hBn hue hf0)) hsu ht.
  move=> i j; by rewrite (ord1 j).
rewrite exterior_first_norm -[RHS]mul1r; congr (_ * _); exact: h1.
Qed.

(** Source for [simple_tangent_form_frame]: if ξ = c u_1 ∧ … ∧ u_k is
    simple with u orthonormal and |ξ| = 1, then c_ξ(v, w) = Q(v) • w for the
    orthogonal projection Q = [x ↦ Σ_i (x • u_i) u_i] of Allard 2.3, p. 421;
    Federer 1.6.1, p. 24, and 1.7.5, p. 32. Supporting lemma. *)
Lemma simple_tangent_form_frame (xi : exterior_power Rn k) (u : 'I_k -> Rn) (c : R) :
  simple xi -> orthonormal_family Bn u -> c != 0 -> xi = c *: e_lambda u (ord_tuple k) ->
  exterior_norm h2 hBn xi = 1 ->
  forall v w, simple_tangent_form xi v w = Bn (frame_projector hBn u v) w.
Proof.
move=> hs hu hc hxi h1.
pose F := frame_projector hBn u.
have hF : is_orthogonal_projector hBn hbn k F := frame_projector_orthogonal_projector hBn hbn hu.
have hxp := proj2 (@exterior_product_bilinear R Rn k 1) xi.
have hB := inner_bilinear hBn.
have hspan x : FedererSimple.T xi (F x).
  rewrite hxi; apply/(associated_scale_nonzero _ hc); apply: product_associated_span.
  rewrite frame_projectorE; by exists (fun i => Bn x (u i)).
have hres x i : Bn (u i) (x - F x) = 0.
  rewrite (inner_symmetric hBn).
  exact: (@orthonormal_residual_orthogonal R Rn Bn hBn _ u hu x i).
have hwedge x : exterior_product xi (first x) = exterior_product xi (first (x - F x)).
  by rewrite linearB (linB hxp) (associated_right_first_wedge (hspan x)) subr0.
have horth x y : (forall i, Bn (u i) x = 0) -> (forall i, Bn (u i) y = 0) ->
    EI (exterior_product xi (first x)) (exterior_product xi (first y)) = Bn x y.
  move=> hx hy; rewrite (inner_polarisation E1) (inner_polarisation hBn).
  rewrite -(linD hxp) -(linB hxp) -linearD -linearB.
  rewrite (frame_right_first_wedge_norm hs hc hxi h1); last first.
    by move=> i; rewrite (bilDr hB) hx hy addr0.
  rewrite (frame_right_first_wedge_norm hs hc hxi h1) //.
  by move=> i; rewrite (bilBr hB) hx hy subr0.
move=> v w; rewrite /simple_tangent_form (hwedge v) (hwedge w) horth; last 2 first.
- exact: hres.
- exact: hres.
rewrite (bilBl hB) !(bilBr hB) (allard_2_3_1 hF v w).
rewrite -(orthogonal_projector_symmetric hF v w).
rewrite /GRing.scale /=; ring.
Qed.


(** Source for [simple_projection_hom_frame]: under the hypotheses of
    [simple_tangent_form_frame], P(ξ) = Q, Allard 2.3, p. 421. Supporting
    lemma. *)
Lemma simple_projection_hom_frame (xi : exterior_power Rn k) (u : 'I_k -> Rn) (c : R) :
  simple xi -> orthonormal_family Bn u -> c != 0 -> xi = c *: e_lambda u (ord_tuple k) ->
  exterior_norm h2 hBn xi = 1 -> simple_projection_hom xi = frame_projector hBn u.
Proof.
move=> hs hu hc hxi h1; apply: hom_ext=> v.
rewrite -[LHS]euclidean_coordinate_expansion -[RHS]euclidean_coordinate_expansion.
apply: eq_bigr=> i _; congr (_ *: _).
rewrite -!euclidean_inner_basis simple_projection_hom_inner.
exact: (simple_tangent_form_frame hs hu hc hxi h1).
Qed.

(** Source for [simple_unit_frame]: a simple k-vector ξ with |ξ| = 1 is
    c u_1 ∧ … ∧ u_k with u orthonormal, c ≠ 0 and u_1 ∧ … ∧ u_k ≠ 0,
    Federer 1.7.5, p. 32. Supporting lemma. *)
Lemma simple_unit_frame (xi : exterior_power Rn k) :
  simple xi -> exterior_norm h2 hBn xi = 1 ->
  exists (u : 'I_k -> Rn) (c : R), [/\ orthonormal_family Bn u, c != 0,
    xi = c *: e_lambda u (ord_tuple k) & e_lambda u (ord_tuple k) != 0].
Proof.
move=> hs h1.
have hx0 : xi != 0.
  by apply/eqP=> hz; move: h1; rewrite hz exterior_norm_zero=> /eqP; rewrite eq_sym oner_eq0.
have [u [c [hu [hc hxi]]]] := @simple_orthonormal_factor R h2 Rn Bn hBn k xi hx0 hs.
exists u, c; split=> //.
by apply/eqP=> hz; move: hx0; rewrite hxi hz scaler0 eqxx.
Qed.

(** Source for [simple_projection_hom_projector]: for a simple k-vector ξ
    with |ξ| = 1, P(ξ) is an orthogonal projector of rank k, that is a
    member of Allard's G(n, k), Allard 2.3, p. 421; supporting the passage
    from the orientation of Federer 3.2.25, p. 261, to Tan^k in Allard 3.5,
    p. 432. *)
Lemma simple_projection_hom_projector (xi : exterior_power Rn k) :
  simple xi -> exterior_norm h2 hBn xi = 1 ->
  is_orthogonal_projector hBn hbn k (simple_projection_hom xi).
Proof.
move=> hs h1; have [u [c [hu hc hxi _]]] := simple_unit_frame hs h1.
rewrite (simple_projection_hom_frame hs hu hc hxi h1).
exact: frame_projector_orthogonal_projector.
Qed.

(** Source for [simple_projection_hom_image]: for a simple k-vector ξ with
    |ξ| = 1, the image of P(ξ) is the associated subspace T(ξ) of Federer
    1.6.1, p. 23; with [simple_projection_hom_projector] this identifies
    P(ξ) with the member of G(n, k) corresponding to T(ξ), Allard 2.3,
    p. 421, as used in Allard 3.5, p. 432. *)
Lemma simple_projection_hom_image (xi : exterior_power Rn k) :
  simple xi -> exterior_norm h2 hBn xi = 1 ->
  forall v, (exists w, simple_projection_hom xi w = v) <-> FedererSimple.T xi v.
Proof.
move=> hs h1 v; have [u [c [hu hc hxi hue]]] := simple_unit_frame hs h1.
rewrite (simple_projection_hom_frame hs hu hc hxi h1) (frame_projector_image hBn v hu).
rewrite -(product_associated_space h2 hue v) hxi.
split=> h; [exact: (proj2 (associated_scale_nonzero _ hc v) h)|exact: (proj1 (associated_scale_nonzero _ hc v) h)].
Qed.

End SimpleProjection.
