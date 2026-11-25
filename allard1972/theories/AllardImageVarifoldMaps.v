(** Allard (1972), 3.2, printed p. 430, specialised to M = M' = R^n;
    blueprint al:3.2 and new:projection_formula. For a map F : R^n → R^n
    of class 1 with derivative DF, the image varifold F_# V is the image of
    the measure V⌞J under the map

        F_♮(x, S) = (F(x), DF(x)(S)),   J(x, S) = ‖∧_k(DF(x) ∘ S)‖,

    of G_k(R^n) = R^n × G(n, k) into itself, where DF(x)(S) is the
    orthogonal projection of R^n onto DF(x)[im S] given by the projection
    formula of new:projection_formula. This file defines the plane map
    ([projection_grassmann_image]), the maps F_♮ ([image_bundle_map]) and
    J ([image_bundle_jacobian]), and proves that J is continuous and that
    F_♮ is continuous and proper if DF(x) is injective for every x and F is
    proper. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm boolp reals ring.
From mathcomp Require Import classical_sets functions topology normedtype lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerMetric LinearBasis Bilinear
  TensorUP Hom HomInner AdjointUP Adjoint OrthonormalFamilies OrthogonalMaps OrthonormalFrameMap
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates EuclideanLinearMaps
  ExteriorGrading ExteriorMaps ExteriorMapScaling InnerExterior
  InnerExteriorPositivity ExteriorNorm ExteriorOperatorNorm OperatorNormUP OperatorNormLaws
  TopExteriorNorm FiniteExteriorPowers ExteriorProjectionNorm EuclideanLinearJacobian
  ExteriorFrameUnitNorm AssociatedSubspace SimpleElementary.
From Federer Require Import TopologicalProductMaps MetricSubsetBackground ExteriorMapNormContinuity
  RealMetricBackground HomInnerCoordinates CurrentSupportMapTopology NormClassOneUP
  EuclideanClassZeroContinuity HomSpaceTopology ProperMapUP.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardJacobians AllardProjectionFormula AllardProjectionContinuity AllardVarifolds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_function_composition]: general topology,
    used for the continuity assertions of blueprint al:3.2: the
    composition of continuous maps is continuous. Supporting lemma. *)
Lemma continuous_function_composition (X Y Z : topologicalType) (f : X -> Y) (g : Y -> Z) :
  continuous f -> continuous g -> continuous (fun x => g (f x)).
Proof. by move=> hf hg x; exact: (continuous_comp (hf x) (hg (f x))). Qed.

(** Source for [open_set_type_continuous_at]: general topology, used for
    the continuity of the projection formula on its open domain
    (blueprint new:projection_formula): if A is open, x ∈ A and f|A is
    continuous with respect to the relative topology, then f is
    continuous at x. Supporting lemma. *)
Lemma open_set_type_continuous_at (X Y : topologicalType) (A : set X) (f : X -> Y) (x : X) :
  open A -> A x -> continuous (fun z : set_type A => f (set_val z)) -> f @ x --> f x.
Proof.
move=> hA hx hf W; rewrite nbhsE => -[W' [hW'o hW'x] hW'W].
pose O := (fun z : set_type A => f (set_val z)) @^-1` W'.
have hO : open O := (proj1 (continuousP _) hf) W' hW'o.
have hOX : open (set_val @` O) := open_subspace_open_image hA hO.
have hxO : (set_val @` O) x.
  by exists (@exist X (fun y => y \in A) x (mem_set hx)).
rewrite nbhsE; exists (set_val @` O); first by split.
by move=> y [z hz <-]; apply: hW'W.
Qed.

Section ImageJacobian.
Variable R : realType.
Variables n p k : nat.
Local Notation h2 := (euclidean_two_nonzero R).
Local Notation Rn := (R_n R n).
Local Notation Rp := (R_n R p).
Local Notation Rk := (R_n R k).
Local Notation Bn := (@euclidean_inner_product R n).
Local Notation Bp := (@euclidean_inner_product R p).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hBp := (@euclidean_inner_productP R p).
Local Notation hBk := (@euclidean_inner_productP R k).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hbk := (@coordinate_basisP R k).
Local Notation HEn := (inner_metric_space (hom_inner_productP hBn hBn hbn)).
Local Notation HEnp := (inner_metric_space (hom_inner_productP hBn hBp hbn)).

(** Source for [jacobian_exterior_factor]: Allard 2.4, p. 422, and
    Federer 1.7.5, 3.2.1: if S ∈ G(n, k), L ∈ Hom(R^n, R^p) and
    ξ ∈ ∧_k R^n, then |∧_k(L ∘ S) ξ| = ‖∧_k(L ∘ S)‖ |∧_k S ξ|, because
    ∧_k S ξ is a multiple of the unit k vector of im S. Supporting lemma
    for the continuity of J. *)
Lemma jacobian_exterior_factor (L : Hom Rn Rp) (S : Hom Rn Rn) (y : exterior_power Rn k) :
  is_orthogonal_projector hBn hbn k S ->
  exterior_norm h2 hBp (exterior_power_map (hom_as_linear (hom_comp L S)) k y) =
  euclidean_linear_jacobian k (hom_comp L S) *
    exterior_norm h2 hBn (exterior_power_map (hom_as_linear S) k y).
Proof.
move=> hS; have [u [j [hu hSu hj hju [hSj hjS]]]] := orthogonal_projector_frame_map hS.
pose a := inner_adjoint hBk hBn hbk j.
pose xi0 := e_lambda (@coordinate_basis R k) (ord_tuple k).
have hxi0 : exterior_norm h2 hBk xi0 = 1 := euclidean_top_product_unit_norm h2 k.
have hxi0n : xi0 != 0 by rewrite -(exterior_norm_eq0 h2 hBk) hxi0 oner_eq0.
have [c hc] := @nonzero_top_vector_spans R h2 Rk k (@coordinate_basis R k) hbk xi0 hxi0n
  (exterior_power_map a k y).
have hfac (M : Hom Rn Rp) : exterior_power_map (hom_as_linear (hom_comp M S)) k y =
    c *: exterior_power_map (hom_as_linear (hom_comp M (hom_of_linear j))) k xi0.
  rewrite -linearZ -hc exterior_power_map_composition; apply: exterior_power_map_ext=> x.
  change (M (S x) = M (j (a x))); by rewrite hSj.
have hj1 : exterior_norm h2 hBn (exterior_power_map j k xi0) = 1.
  by rewrite (exterior_orthogonal_norm h2 hBk hBn hj) hxi0.
have hS1 : exterior_power_map (hom_as_linear S) k y = c *: exterior_power_map j k xi0.
  rewrite -linearZ -hc exterior_power_map_composition; apply: exterior_power_map_ext=> x.
  change (S x = j (a x)); exact: hSj.
have hJ : euclidean_linear_jacobian k (hom_comp L S) =
    exterior_norm h2 hBp (exterior_power_map (hom_as_linear (hom_comp L (hom_of_linear j))) k xi0).
  rewrite hSu (jacobian_frame_projector_factor L hj hju).
  exact: (top_exterior_operator_unit_value hBp hbk (hom_as_linear (hom_comp L (hom_of_linear j))) hxi0).
by rewrite hfac hS1 !exterior_norm_scale hj1 mulr1 hJ mulrC.
Qed.

(** Source for [jacobian_param_continuous]: Allard 3.2, p. 430: the
    factor ‖∧_k(DF(x) ∘ S)‖ of 3.2(1) depends continuously on
    (DF(x), S). Here: if f and g are continuous families of linear maps
    and g(t) ∈ G(n, k) for every t, then t ↦ ‖∧_k(f(t) ∘ g(t))‖ is
    continuous. Near t₀ the Jacobian equals the quotient
    |∧_k(f(t) ∘ g(t)) ξ| / |∧_k g(t) ξ| for a unit simple k vector ξ of
    im g(t₀) ([jacobian_exterior_factor]); numerator and denominator are
    continuous by Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma jacobian_param_continuous (T : topologicalType) (f : T -> HEnp) (g : T -> HEn) :
  continuous f -> continuous g -> (forall t, is_orthogonal_projector hBn hbn k (g t : Hom Rn Rn)) ->
  continuous (fun t => (euclidean_linear_jacobian k (hom_comp (f t : Hom Rn Rp) (g t : Hom Rn Rn))
    : real_line_metric R)).
Proof.
move=> hf hg hP t0.
have [u [j [hu hSu hj hju [hSj hjS]]]] := orthogonal_projector_frame_map (hP t0).
pose y := e_lambda u (ord_tuple k).
have hy : simple y := product_simple u.
pose N := fun t => exterior_norm h2 hBp
  (exterior_power_map (hom_as_linear (hom_comp (f t : Hom Rn Rp) (g t : Hom Rn Rn))) k y).
pose D := fun t => exterior_norm h2 hBn (exterior_power_map (hom_as_linear (g t : Hom Rn Rn)) k y).
pose J := fun t => euclidean_linear_jacobian k (hom_comp (f t : Hom Rn Rp) (g t : Hom Rn Rn)).
have hJD t : J t * D t = N t.
  by rewrite /J /D /N (jacobian_exterior_factor _ _ (hP t)).
have hcomp := hom_comp_continuous_param hf hg.
have hNc : continuous (N : T -> real_line_metric R).
  move=> t; exact: (continuous_comp (hcomp t)
    (@exterior_map_norm_continuous R h2 Rn Rp Bn Bp hBn hBp n _ hbn k y hy _)).
have hDc : continuous (D : T -> real_line_metric R).
  move=> t; exact: (continuous_comp (hg t)
    (@exterior_map_norm_continuous R h2 Rn Rn Bn Bn hBn hBn n _ hbn k y hy _)).
have hD0 : D t0 = 1.
  rewrite /D exterior_power_map_e_lambda.
  have -> : (hom_as_linear (g t0 : Hom Rn Rn) \o u) = u.
    apply: funext=> l; rewrite /= -hju; exact: hjS.
  exact: orthonormal_product_unit_norm.
have hND : (fun t => N t / D t : R^o) @ t0 --> (N t0 / D t0 : R^o).
  apply: cvgM; first exact: (hNc t0).
  apply: cvgV; first by rewrite hD0 oner_neq0.
  exact: (hDc t0).
have hpos : \forall t \near t0, 0 < D t.
  have hb : nbhs (D t0 : real_line_metric R)
      [set x : real_line_metric R | mdist (D t0 : real_line_metric R) x < 1].
    apply: (proj2 (metricType_numDomainType.nbhs_mdistP (D t0 : real_line_metric R) _)).
    exists 1; first exact: ltr01.
    by move=> x.
  have hb' : nbhs t0 [set t | mdist (D t0 : real_line_metric R) (D t : real_line_metric R) < 1].
    exact: (hDc t0 _ hb).
  apply: (filterS _ hb')=> t /=; rewrite real_line_metric_distanceE hD0.
  by rewrite ltr_norml => /andP [h1 h2']; lra.
have hJ0 : J t0 = N t0 / D t0 by rewrite -hJD hD0 divr1 mulr1.
have hnear : \forall t \near t0, J t = N t / D t.
  apply: (filterS _ hpos)=> t ht; rewrite -hJD mulfK //; exact: lt0r_neq0.
move=> U hU.
have hU2 : nbhs (N t0 / D t0 : R^o) U.
  have hU1 : nbhs (J t0 : real_line_metric R) U := hU.
  rewrite hJ0 in hU1; exact: hU1.
have hU' : nbhs t0 [set t | U (N t / D t)] := hND U hU2.
suff h : nbhs t0 [set t | U (J t)] by exact: h.
apply: (filterS2 _ _ hnear hU')=> t ht hUt; by rewrite /= ht.
Qed.
End ImageJacobian.

Section ImageMaps.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation RnM := (inner_metric_space hBn).
Local Notation HEn := (inner_metric_space (hom_inner_productP hBn hBn hbn)).
Local Notation GA := (projection_grassmann R n k).
Local Notation GB := (grassmann_bundle R n k).

(** Source for [projection_grassmann_cvg]: Allard 2.2, p. 421: G(n, k)
    carries the metric of Hom(R^n, R^n), so that convergence in G(n, k)
    is convergence of the orthogonal projections. Supporting lemma. *)
Lemma projection_grassmann_cvg (T : topologicalType) (g : T -> GA) (t : T) :
  (fun s => (set_val (g s) : HEn)) @ t --> (set_val (g t) : HEn) -> g @ t --> g t.
Proof.
move=> hg U hU.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP (g t) U) hU.
have hn : nbhs (set_val (g t) : HEn) [set y : HEn | mdist (set_val (g t) : HEn) y < e].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (set_val (g t) : HEn) _)).
  by exists e.
have hn' : nbhs t [set s | mdist (set_val (g t) : HEn) (set_val (g s) : HEn) < e] := hg _ hn.
apply: (filterS _ hn')=> s hs; apply: hb; exact hs.
Qed.

(** Source for [projection_formula_total]: blueprint
    new:projection_formula, for p = n: the map P = L ∘ S ∘ A^{-1} ∘ L^*
    where A = S ∘ L^* ∘ L ∘ S + 1 - S is invertible, extended by S
    elsewhere. Only the values on the domain of the projection formula
    enter the integrals of Allard 3.2(1). Definition. *)
Definition projection_formula_total (L S : Hom Rn Rn) : Hom Rn Rn :=
  match pselect (injective (projection_formula_operator L S)) with
  | left hA => projection_formula_map hA
  | right _ => S
  end.

(** Source for [projection_formula_totalE]: blueprint
    new:projection_formula: on the domain of the projection formula,
    [projection_formula_total] is the map P. Supporting lemma. *)
Lemma projection_formula_totalE (L S : Hom Rn Rn) (hA : injective (projection_formula_operator L S)) :
  projection_formula_total L S = projection_formula_map hA.
Proof.
rewrite /projection_formula_total; case: pselect=> [hA'|//].
by have -> : hA' = hA by exact: Prop_irrelevance.
Qed.

(** Source for [projection_formula_total_cvg]: blueprint
    new:projection_formula: (L, S) ↦ P is continuous on the open domain
    of the projection formula; composed with continuous families of
    linear maps. Supporting lemma. *)
Lemma projection_formula_total_cvg (T : topologicalType) (f g : T -> HEn) (t : T) :
  continuous f -> continuous g -> projection_formula_domain R n n (f t, g t) ->
  (fun s => (projection_formula_total (f s) (g s) : HEn)) @ t -->
    (projection_formula_total (f t) (g t) : HEn).
Proof.
move=> hf hg ht.
have hon : continuous (fun w : set_type (projection_formula_domain R n n) =>
    (projection_formula_total (set_val w).1 (set_val w).2 : HEn)).
  have -> : (fun w : set_type (projection_formula_domain R n n) =>
      (projection_formula_total (set_val w).1 (set_val w).2 : HEn)) = @projection_formula_on R n n.
    apply: funext=> w; exact: (projection_formula_totalE (set_valP w)).
  exact: projection_formula_continuous.
have hc := @open_set_type_continuous_at _ HEn _
  (fun w : (HEn * HEn)%type => (projection_formula_total w.1 w.2 : HEn)) (f t, g t)
  (@projection_formula_domain_open R n n) ht hon.
have hp := topological_pair_continuous hf hg.
exact: (continuous_comp (hp t) hc).
Qed.

(** Source for [projection_grassmann_image]: Allard 3.2, p. 430, the
    plane DF(x)(S) = L[im S] for L = DF(x), represented by the orthogonal
    projection P of R^n onto L[im S] (blueprint new:projection_formula)
    when ‖∧_k(L ∘ S)‖ > 0, and by S otherwise. Definition. *)
Definition projection_grassmann_image (L : Hom Rn Rn) (S : GA) : GA :=
  match pselect (injective (projection_formula_operator L (set_val S))) with
  | left hA => projection_grassmann_of
      (projection_formula_orthogonal_projector (projection_grassmannP S) hA)
  | right _ => S
  end.

(** Source for [projection_grassmann_image_val]: blueprint
    new:projection_formula: the orthogonal projection of
    [projection_grassmann_image L S] is [projection_formula_total L S].
    Supporting lemma. *)
Lemma projection_grassmann_image_val (L : Hom Rn Rn) (S : GA) :
  set_val (projection_grassmann_image L S) = projection_formula_total L (set_val S).
Proof. by rewrite /projection_grassmann_image /projection_formula_total; case: pselect. Qed.

(** Source for [projection_grassmann_imageE]: blueprint
    new:projection_formula: if ‖∧_k(L ∘ S)‖ > 0, then
    [projection_grassmann_image L S] is the orthogonal projection
    P = L ∘ S ∘ A^{-1} ∘ L^* of R^n onto L[im S]. Supporting lemma. *)
Lemma projection_grassmann_imageE (L : Hom Rn Rn) (S : GA)
    (hA : injective (projection_formula_operator L (set_val S))) :
  set_val (projection_grassmann_image L S) = projection_formula_map hA.
Proof. by rewrite projection_grassmann_image_val (projection_formula_totalE hA). Qed.

(** Source for [projection_grassmann_image_cvg]: blueprint
    new:projection_formula: (L, S) ↦ L[im S] is continuous wherever
    ‖∧_k(L ∘ S)‖ > 0; composed with continuous families. Supporting
    lemma. *)
Lemma projection_grassmann_image_cvg (T : topologicalType) (f : T -> HEn) (h : T -> GA) (t : T) :
  continuous f -> continuous h ->
  0 < euclidean_linear_jacobian k (hom_comp (f t : Hom Rn Rn) (set_val (h t) : Hom Rn Rn)) ->
  (fun s => projection_grassmann_image (f s) (h s)) @ t --> projection_grassmann_image (f t) (h t).
Proof.
move=> hf hh hJ; apply: projection_grassmann_cvg.
have hg : continuous (fun s => (set_val (h s) : HEn)).
  apply: (continuous_function_composition hh); exact: metric_subset_inclusion_continuous.
have hz : projection_formula_domain R n n (f t, set_val (h t)).
  exact/(projection_formula_domainE (f t) (h t)).
have -> : (fun s => (set_val (projection_grassmann_image (f s) (h s)) : HEn)) =
    (fun s => (projection_formula_total (f s) (set_val (h s)) : HEn)).
  by apply: funext=> s; rewrite projection_grassmann_image_val.
rewrite projection_grassmann_image_val.
exact: (projection_formula_total_cvg hf hg hz).
Qed.

(** Source for [class_one_differential_continuous]: Federer 3.1.1,
    p. 210: if F is of class 1 with derivative DF, then DF is continuous
    into Hom(R^n, R^n) with its metric of Federer 2.7.16, p. 134.
    Supporting lemma. *)
Lemma class_one_differential_continuous (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) :
  is_norm_class_one_field (inner_norm hBn) (inner_norm hBn) setT F DF ->
  continuous (fun x : RnM => (DF x : HEn)).
Proof.
move=> hF a A hA.
have [r hr hrA] := proj1 (hom_space_nbhs_operator (DF a : HEn) A) hA.
have hr2 : 0 < r / 2 by rewrite divr_gt0.
have [d [hd hb]] := @norm_class_one_continuity _ _ _ _ _ _ _ _ hF a Logic.I (r / 2) hr2.
have hn : nbhs (a : RnM) [set x : RnM | mdist (a : RnM) x < d].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (a : RnM) _)).
  exists d; first exact: hd.
  by move=> x.
suff h : nbhs (a : RnM) [set x : RnM | A (DF x : HEn)] by exact: h.
apply: (filterS _ hn)=> x hx; apply: hrA.
have hx' : inner_norm hBn (x - a) < d.
  by move: hx; rewrite /= inner_metric_distanceE -inner_normN opprB.
have hxa : a + (x - a) = x by rewrite addrC subrK.
apply: (@le_lt_trans _ _ (r / 2)); last lra.
apply: hom_operator_norm_least; first exact: ltW.
move=> v; have := hb (x - a) Logic.I hx' v; by rewrite hxa.
Qed.

(** Source for [class_one_continuous]: Federer 3.1.1, p. 210: a map of
    class 1 is continuous. Supporting lemma. *)
Lemma class_one_continuous (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) :
  is_norm_class_one_field (inner_norm hBn) (inner_norm hBn) setT F DF ->
  continuous (fun x : RnM => (F x : RnM)).
Proof. move=> hF; exact: (euclidean_class_zero_continuous (norm_class_one_zero hF)). Qed.

(** Source for [image_bundle_map]: Allard 3.2, p. 430: the map
    F_♮(x, S) = (F(x), DF(x)(S)) of G_k(R^n) into itself, with the plane
    DF(x)(S) of [projection_grassmann_image]. Definition. *)
Definition image_bundle_map (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (z : GB) : GB :=
  ((F z.1 : RnM), projection_grassmann_image (DF z.1) z.2).

(** Source for [image_bundle_jacobian]: Allard 3.2(1), p. 430: the
    factor J(x, S) = ‖∧_k(DF(x) ∘ S)‖ of the integrand, with the norm of
    Federer 3.2.1 (blueprint al:2.4). Definition. *)
Definition image_bundle_jacobian (DF : Rn -> Hom Rn Rn) (z : GB) : R :=
  euclidean_linear_jacobian k (hom_comp (DF z.1) (set_val z.2 : Hom Rn Rn)).

(** Source for [grassmann_bundle_plane_continuous]: the projection
    (x, S) ↦ S of G_k(R^n) onto G(n, k) is continuous. Supporting
    lemma. *)
Lemma grassmann_bundle_plane_continuous : continuous (fun z : GB => z.2).
Proof. exact: (@second_projection_continuous RnM GA). Qed.

(** Source for [image_bundle_jacobian_continuous]: Allard 3.2, p. 430:
    if F is of class 1, then J(x, S) = ‖∧_k(DF(x) ∘ S)‖ is continuous on
    G_k(R^n). Supporting lemma. *)
Lemma image_bundle_jacobian_continuous (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) :
  is_norm_class_one_field (inner_norm hBn) (inner_norm hBn) setT F DF ->
  continuous (fun z : GB => (image_bundle_jacobian DF z : real_line_metric R)).
Proof.
move=> hF.
have h1 : continuous (fun z : GB => (DF z.1 : HEn)).
  exact: (continuous_function_composition (@grassmann_bundle_point_continuous R n k)
    (class_one_differential_continuous hF)).
have h2 : continuous (fun z : GB => (set_val z.2 : HEn)).
  apply: (continuous_function_composition grassmann_bundle_plane_continuous).
  exact: metric_subset_inclusion_continuous.
exact: (jacobian_param_continuous h1 h2 (fun z => projection_grassmannP z.2)).
Qed.

(** Source for [image_bundle_jacobian_positive]: blueprint
    new:projection_formula: if DF(x) is injective, then
    ‖∧_k(DF(x) ∘ S)‖ > 0 for every S ∈ G(n, k). Supporting lemma. *)
Lemma image_bundle_jacobian_positive (DF : Rn -> Hom Rn Rn) :
  (forall x, injective (DF x)) -> forall z : GB, 0 < image_bundle_jacobian DF z.
Proof.
move=> hinj z; apply/(projection_formula_jacobian (DF z.1) (projection_grassmannP z.2)).
move=> x _ hx; apply: (hinj z.1); rewrite hx; exact/esym/linear0.
Qed.

(** Source for [image_bundle_map_continuous]: Allard 3.2, p. 430, with
    blueprint new:projection_formula: if F is of class 1 and DF(x) is
    injective for every x, then F_♮ is continuous. Supporting lemma. *)
Lemma image_bundle_map_continuous (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) :
  is_norm_class_one_field (inner_norm hBn) (inner_norm hBn) setT F DF ->
  (forall x, injective (DF x)) -> continuous (image_bundle_map F DF).
Proof.
move=> hF hinj.
have h1 : continuous (fun z : GB => (DF z.1 : HEn)).
  exact: (continuous_function_composition (@grassmann_bundle_point_continuous R n k)
    (class_one_differential_continuous hF)).
have hF1 : continuous (fun z : GB => (F z.1 : RnM)).
  exact: (continuous_function_composition (@grassmann_bundle_point_continuous R n k)
    (class_one_continuous hF)).
have hG : continuous (fun z : GB => projection_grassmann_image (DF z.1) z.2).
  move=> z; apply: (projection_grassmann_image_cvg h1 grassmann_bundle_plane_continuous).
  exact: (image_bundle_jacobian_positive hinj z).
have h := topological_pair_continuous hF1 hG.
exact h.
Qed.

(** Source for [image_bundle_map_proper]: Allard 3.2, p. 430: if
    moreover F is proper, then F_♮ is proper, because
    F_♮^{-1}[C] is a closed subset of F^{-1}[π[C]] × G(n, k) for compact
    C, where π(x, S) = x. Supporting lemma. *)
Lemma image_bundle_map_proper (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) :
  is_norm_class_one_field (inner_norm hBn) (inner_norm hBn) setT F DF ->
  (forall x, injective (DF x)) -> is_proper_map (fun x : RnM => (F x : RnM)) ->
  is_proper_map (image_bundle_map F DF).
Proof.
move=> hF hinj hP C hC.
have hcont := image_bundle_map_continuous hF hinj.
have hCc : closed C := compact_closed (@metric_hausdorff R GB) hC.
have hpre : closed (image_bundle_map F DF @^-1` C) := (proj1 (continuous_closedP _) hcont) C hCc.
have hpC : compact (@grassmann_bundle_point R n k @` C).
  exact: (continuous_compact (continuous_subspaceT (@grassmann_bundle_point_continuous R n k)) hC).
have hK : compact ((fun x : RnM => (F x : RnM)) @^-1` (@grassmann_bundle_point R n k @` C)) :=
  hP _ hpC.
have hKG : compact ((((fun x : RnM => (F x : RnM)) @^-1` (@grassmann_bundle_point R n k @` C))
    `*` [set: GA]) : set GB).
  have h := @compact_setX RnM GA _ [set: GA] hK (@projection_grassmann_compact R n k).
  exact h.
apply: (subclosed_compact hpre hKG).
move=> z hz; split=> //=; exists (image_bundle_map F DF z) => //.
Qed.
End ImageMaps.
