(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    section “Varifolds and the Michael–Simon inequality”, mr:varifolds
    and def:BF. An integrand is a map
    F : G(n, k) → (0, ∞) of class 1 in the sense of Federer 3.1.22,
    p. 236, relative to the compact submanifold G(n, k) of
    Hom(R^n, R^n) (Allard 2.3); it is represented by a map
    F : Hom(R^n, R^n) → R whose values off G(n, k) play no role. The map
    B_F : G(n, k) → Hom(R^n, R^n) of def:BF is the map [ddg_B] of DDG
    (A.3) for an integrand not depending on the point; no second
    construction is made.

    The file proves that F is bounded, Lipschitzian and relatively
    differentiable on G(n, k) (the hypotheses of DDG Lemma A.2), and
    that B_F is continuous on G(n, k) (first sentence of the proof of
    lem:KF). Hom(R^n, R^n) carries the inner product
    A • B = trace(A^* ∘ B) and the norm |A| of Federer 1.7.9; G(n, k)
    carries the metric induced by this norm. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology normedtype ring lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities
  LinearBasis Bilinear TensorUP Hom HomInner HomInnerCoordinates AdjointUP AdjointLaws Adjoint
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates EuclideanRectangularAdjoint
  HilbertFormCompactness RealNormUP NormMetric PartialFunctionUP TangentConeUP NormDifferentialUP
  NormClassOneUP NormRegularity RelativeClassUP RelativeDifferentialUP RelativeDifferentialRestriction
  RelativeDifferentialUniqueness NormClassOneLocalLipschitz MetricCompactLocalLipschitz LipschitzUP
  RealMetricBackground NormMetricScaleContinuity ConvexHull InnerConvex LinearRankAtLeast
  InnerMetric.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann.
From DPDRG Require Import DdgLinearAlgebra DdgGrassmann DdgLemmaA1 DdgGrassmannTangent DdgHomInner
  DdgAnisotropicIntegrandUP DdgAnisotropicIntegrand.
From DPGPR Require Import DgprSingularValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dgpr_local_lipschitz_continuous]: Federer 2.2.7, p. 63:
    a map between metric spaces which is Lipschitzian on a ball about
    every point is continuous. Supporting lemma for blueprint lem:KF. *)
Lemma dgpr_local_lipschitz_continuous (R : realType) (T U : metricType R) (f : T -> U) :
  (forall c, exists r L : R, [/\ 0 < r, 0 <= L &
    forall y, mdist c y < r -> mdist (f c) (f y) <= L * mdist c y]) ->
  continuous f.
Proof.
move=> hloc x W hW.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP (f x) W) hW.
have [r [L [hr hL hb]]] := hloc x.
have hpos : 0 < 1 + L by rewrite ltr_pwDl.
pose d := Num.min r (e / (1 + L)).
have hd : 0 < d by rewrite lt_min hr divr_gt0.
apply: (proj2 (metricType_numDomainType.nbhs_mdistP x _)); exists d => // y hy.
apply: hball; rewrite /=.
have hyr : mdist x y < r by apply: lt_le_trans hy _; rewrite ge_min lexx.
have hye : mdist x y < e / (1 + L) by apply: lt_le_trans hy _; rewrite ge_min lexx orbT.
apply: le_lt_trans (hb y hyr) _.
have h0 := mdist_ge0 x y.
have h1 : L * mdist x y <= (1 + L) * mdist x y by rewrite ler_wpM2r // lerDr.
apply: le_lt_trans h1 _; by rewrite mulrC -ltr_pdivlMr.
Qed.

Section AnisotropicIntegrand.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation NH := (hom_norm hBn hBn hbn).
Local Notation hH := (hom_inner_productP hBn hBn hbn).
Local Notation hNH := (inner_norm_real_norm hH).
Local Notation N1 := (fun t : R^o => `|t|).
Local Notation hN1 := (@scalar_absolute_value_norm R).
Local Notation HI := (hom_inner hBn hBn hbn).
Local Notation G := (orthogonal_projectors R n k).
Local Notation GA := (projection_grassmann R n k).

(** Source for [dgpr_integrand]: blueprint mr:varifolds: F : G(n, k) →
    (0, ∞) is of class 1 in the sense of Federer 3.1.22, p. 236, on the
    submanifold G(n, k) of Hom(R^n, R^n), and positive on G(n, k). The
    values of F off G(n, k) play no role. Definition. *)
Definition dgpr_integrand (F : Hom Rn Rn -> R) : Prop :=
  @norm_class_relative R _ R^o NH N1 hNH hN1 G G F 1 /\ forall S, G S -> 0 < F S.

Variable F : Hom Rn Rn -> R.
Hypothesis hF : @norm_class_relative R _ R^o NH N1 hNH hN1 G G F 1.

(** Source for [dgpr_integrand_local_lipschitz]: Federer 3.1.22, p. 236,
    and 3.1.1, p. 210: F agrees near S₀ ∈ G(n, k) with a map of class 1
    on an open neighbourhood of S₀, which is Lipschitzian on a ball
    about S₀ (Federer 3.4.2(8)). Supporting lemma. *)
Lemma dgpr_integrand_local_lipschitz (c : GA) :
  exists r L : R, [/\ 0 < r, 0 <= L &
    forall S S' : GA, mdist c S < r -> mdist c S' < r ->
      `|F (set_val S) - F (set_val S')| <= L * mdist S S'].
Proof.
have hc : G (set_val c : Hom Rn Rn) := set_valP c.
have [U [g [hcU [hg hag]]]] := hF hc.
have hg1 := (norm_class_firstP hNH hN1 U g).1 hg.
have [C [d [hC [hd [hdom hloc]]]]] := norm_class_one_local_lipschitz hNH hN1 hcU hg1.
exists d, C; split=> //; first exact: ltW.
move=> S S' hS hS'.
have hSd : NH ((set_val S : Hom Rn Rn) - set_val c) < d.
  by rewrite -projection_grassmann_distanceE metric_sym.
have hS'd : NH ((set_val S' : Hom Rn Rn) - set_val c) < d.
  by rewrite -projection_grassmann_distanceE metric_sym.
have [_ e1] := hag _ (set_valP S) (hdom _ hSd).
have [_ e2] := hag _ (set_valP S') (hdom _ hS'd).
rewrite e1 e2 projection_grassmann_distanceE.
exact: hloc _ _ hSd hS'd.
Qed.

(** Source for [dgpr_integrand_continuous]: F is continuous on G(n, k),
    Federer 3.1.22, p. 236. Supporting lemma. *)
Lemma dgpr_integrand_continuous :
  continuous (fun S : GA => (F (set_val S : Hom Rn Rn) : real_line_metric R)).
Proof.
apply: dgpr_local_lipschitz_continuous => c.
have [r [L [hr hL hb]]] := dgpr_integrand_local_lipschitz c.
exists r, L; split=> // y hy.
rewrite real_line_metric_distanceE; apply: le_trans (hb c y _ hy) _.
- by rewrite mdistxx.
- by [].
Qed.

(** Source for [dgpr_integrand_bounded]: F is bounded on the compact set
    G(n, k) (Allard 2.3), being continuous. Supporting lemma. *)
Lemma dgpr_integrand_bounded : exists Phi : R, forall S, G S -> `|F S| <= Phi.
Proof.
have hK : compact ((fun S : GA => (F (set_val S : Hom Rn Rn) : real_line_metric R)) @` setT).
  apply: continuous_compact; last exact: projection_grassmann_compact.
  exact: continuous_subspaceT dgpr_integrand_continuous.
have hK' : compact ((fun S : GA => (F (set_val S : Hom Rn Rn) : real_line_metric R)) @` setT
  : set R^o) := hK.
have [M hM] := @filter_ex _ _ proper_pinfty_nbhs _ (compact_bounded hK').
exists M => S hS; apply: hM; exists (projection_grassmann_of hS) => //.
Qed.

(** Source for [dgpr_integrand_lipschitz]: F is Lipschitzian on the
    compact set G(n, k), being Lipschitzian near each point (Federer
    3.4.2(8), with the covering argument of 2.2.7). Supporting lemma. *)
Lemma dgpr_integrand_lipschitz :
  exists2 Lam : R, 0 <= Lam & forall S S', G S -> G S' -> `|F S - F S'| <= Lam * NH (S - S').
Proof.
have [Phi hPhi] := dgpr_integrand_bounded.
pose M := Num.max 0 Phi + Num.max 0 Phi.
have hM : 0 <= M by rewrite addr_ge0 // le_max lexx.
have hlip := @metric_compact_local_lipschitz R GA (real_line_metric R) setT
  (fun S : GA => (F (set_val S : Hom Rn Rn) : real_line_metric R)) M (@projection_grassmann_compact R n k) hM.
have [L [hL [_ hLb]]] : is_metric_lipschitz setT
    (fun S : GA => (F (set_val S : Hom Rn Rn) : real_line_metric R)).
  apply: hlip.
  - move=> x y _ _; rewrite real_line_metric_distanceE.
    apply: le_trans (ler_normB _ _) _.
    apply: lerD; apply: le_trans (hPhi _ (set_valP _)) _; by rewrite le_max lexx orbT.
  - move=> c _; have [r [L0 [hr hL0 hb0]]] := dgpr_integrand_local_lipschitz c.
    exists r, L0; split; first exact: hr.
    split; first exact: hL0.
    move=> x y hx hy; have := hb0 x y hx hy; by rewrite -real_line_metric_distanceE.
exists L; first exact: ltW.
move=> S S' hS hS'.
have := hLb (projection_grassmann_of hS) (projection_grassmann_of hS') Logic.I Logic.I.
by rewrite real_line_metric_distanceE projection_grassmann_distanceE.
Qed.

(** Source for [dgpr_integrand_differentiable]: Federer 3.1.22, p. 235:
    F is differentiable relative to G(n, k) at every point of G(n, k).
    Supporting lemma. *)
Lemma dgpr_integrand_differentiable (T : Hom Rn Rn) : G T -> ddg_relative_differentiable_at k F T.
Proof. move=> hT; exact: ddg_relative_differentiable hT hF. Qed.


End AnisotropicIntegrand.

(** Source for [dgpr_metric_continuous]: continuity between metric
    spaces in the ε–δ form, Federer 2.2.7, p. 63. Supporting lemma. *)
Lemma dgpr_metric_continuous (R : realType) (T U : metricType R) (f : T -> U) :
  (forall c (e : R), 0 < e -> exists2 d : R, 0 < d & forall y, mdist c y < d -> mdist (f c) (f y) < e) ->
  continuous f.
Proof.
move=> h x W hW.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP (f x) W) hW.
have [d hd hxy] := h x e he.
apply: (proj2 (metricType_numDomainType.nbhs_mdistP x _)); exists d => // y hy.
exact: hball (hxy y hy).
Qed.

Section BContinuity.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation NH := (hom_norm hBn hBn hbn).
Local Notation hH := (hom_inner_productP hBn hBn hbn).
Local Notation hNH := (inner_norm_real_norm hH).
Local Notation N1 := (fun t : R^o => `|t|).
Local Notation hN1 := (@scalar_absolute_value_norm R).
Local Notation HI := (hom_inner hBn hBn hbn).
Local Notation G := (orthogonal_projectors R n k).
Local Notation GA := (projection_grassmann R n k).
Local Notation adjL L := (euclidean_rectangular_adjoint L).
Local Notation cn := (Num.sqrt (n%:R : R)).
Local Notation cS := (Num.sqrt (k%:R : R)).
Local Notation cP := (Num.sqrt ((n - k)%:R : R)).

(** Source for [dgpr_B]: blueprint def:BF, B_F(S) ∈ Hom(R^n, R^n) with
    B_F(S) • L = F(S) (S • L) + DF(S)(S^⊥ ∘ L ∘ S + (S^⊥ ∘ L ∘ S)^* ) for
    L ∈ Hom(R^n, R^n); it is the map [ddg_B] of DDG (A.3), p. 1143,
    for an integrand not depending on the point. Definition. *)
Definition dgpr_B (F : Hom Rn Rn -> R) (S : Hom Rn Rn) : Hom Rn Rn := ddg_B k F S.

(** Source for [dgpr_hom_comp_subr]: Federer 1.4.1: composition is
    linear in its second argument. Supporting lemma. *)
Lemma dgpr_hom_comp_subr (f g h : Hom Rn Rn) : hom_comp f (g - h) = hom_comp f g - hom_comp f h.
Proof. by apply: hom_ext => x; rewrite !ddg_hom_subE !hom_compE ddg_hom_subE ddg_homB. Qed.

(** Source for [dgpr_hom_comp_subl]: Federer 1.4.1: composition is
    linear in its first argument. Supporting lemma. *)
Lemma dgpr_hom_comp_subl (f g h : Hom Rn Rn) : hom_comp (f - g) h = hom_comp f h - hom_comp g h.
Proof. by apply: hom_ext => x; rewrite !ddg_hom_subE !hom_compE ddg_hom_subE. Qed.

(** Source for [dgpr_perp_sub]: blueprint mr:varifolds, S^⊥ = 1 − S:
    S^⊥ − T^⊥ = T − S. Supporting lemma. *)
Lemma dgpr_perp_sub (S T : Hom Rn Rn) : ddg_perp S - ddg_perp T = T - S.
Proof.
apply: hom_ext => x; rewrite !ddg_hom_subE ?ddg_hom_idE ?ddg_perpE.
by rewrite ddg_sub_sub opprB.
Qed.

(** Source for [dgpr_hom_normN]: Federer 1.7.1, p. 28: |−f| = |f|.
    Supporting lemma. *)
Lemma dgpr_hom_normN (f : Hom Rn Rn) : NH (- f) = NH f.
Proof. exact: (inner_normN hH). Qed.

(** Source for [dgpr_eq_le]: an equality of real numbers gives an
    inequality. Supporting lemma. *)
Lemma dgpr_eq_le (a b : R) : a = b -> a <= b.
Proof. by move=> ->. Qed.

(** Source for [dgpr_tangent_direction_bound]: blueprint proof of lem:KF:
    |S^⊥ ∘ A ∘ S + (S^⊥ ∘ A ∘ S)^*| ≤ c |A| for S ∈ G(n, k), with
    c = 2 n^{1/2} (n − k)^{1/2} n^{1/2} k^{1/2}, by |S| = k^{1/2},
    |S^⊥| = (n − k)^{1/2} (DDG (A.1)) and |f ∘ g| ≤ n^{1/2} |f| |g|.
    Supporting lemma. *)
Lemma dgpr_tangent_direction_bound (S A : Hom Rn Rn) : G S ->
  NH (ddg_tangent_direction S A) <= 2 * (cn * (cP * (cn * cS))) * NH A.
Proof.
move=> hS; rewrite /ddg_tangent_direction.
set P := hom_comp (ddg_perp S) (hom_comp A S).
have hcn : 0 <= cn := sqrtr_ge0 _.
have hcP : 0 <= cP := sqrtr_ge0 _.
have hP : NH P <= cn * (cP * (cn * cS)) * NH A.
  apply: le_trans (ddg_hom_norm_comp _ _) _.
  rewrite (ddg_A_1_norm (ddg_A_1_perp hS)).
  have h1 := ddg_hom_norm_comp A S; rewrite (ddg_A_1_norm hS) in h1.
  have h2 : cn * (cP * NH (hom_comp A S)) <= cn * (cP * (cn * (NH A * cS))).
    by apply: ler_wpM2l => //; apply: ler_wpM2l.
  apply: le_trans h2 _; apply: dgpr_eq_le; ring.
apply: le_trans (ddg_hom_norm_triangle _ _) _.
rewrite ddg_hom_norm_adjoint.
apply: le_trans (lerD hP hP) _; apply: dgpr_eq_le; ring.
Qed.

(** Source for [dgpr_tangent_direction_difference]: blueprint proof of
    lem:KF: for S, T ∈ G(n, k), the maps [A ↦ S^⊥ ∘ A ∘ S + (S^⊥ ∘ A ∘ S)^*]
    and [A ↦ T^⊥ ∘ A ∘ T + (T^⊥ ∘ A ∘ T)^*] differ by at most c |S − T| |A|.
    Supporting lemma. *)
Lemma dgpr_tangent_direction_difference (S T A : Hom Rn Rn) : G S -> G T ->
  NH (ddg_tangent_direction S A - ddg_tangent_direction T A) <=
    2 * (cn * (cP * cn) + cn * (cn * cS)) * NH (S - T) * NH A.
Proof.
move=> hS hT; rewrite /ddg_tangent_direction.
set PS := hom_comp (ddg_perp S) (hom_comp A S).
set PT := hom_comp (ddg_perp T) (hom_comp A T).
have hPe : PS - PT = hom_comp (ddg_perp S) (hom_comp A (S - T)) + hom_comp (T - S) (hom_comp A T).
  rewrite /PS /PT !dgpr_hom_comp_subr -(dgpr_perp_sub S T) dgpr_hom_comp_subl.
  by rewrite addrA subrK.
have hcn : 0 <= cn := sqrtr_ge0 _.
have hcP : 0 <= cP := sqrtr_ge0 _.
have hcS : 0 <= cS := sqrtr_ge0 _.
have hA0 : 0 <= NH A := ddg_hom_norm_nonnegative A.
have hST0 : 0 <= NH (S - T) := ddg_hom_norm_nonnegative _.
have hP : NH (PS - PT) <= (cn * (cP * cn) + cn * (cn * cS)) * NH (S - T) * NH A.
  rewrite hPe; apply: le_trans (ddg_hom_norm_triangle _ _) _.
  have e1 : (cn * (cP * cn) + cn * (cn * cS)) * NH (S - T) * NH A =
      cn * (cP * (cn * (NH A * NH (S - T)))) + cn * (NH (S - T) * (cn * (NH A * cS))).
    ring.
  rewrite e1; apply: lerD.
  - apply: le_trans (ddg_hom_norm_comp _ _) _.
    rewrite (ddg_A_1_norm (ddg_A_1_perp hS)).
    have h1 := ddg_hom_norm_comp A (S - T).
    by apply: ler_wpM2l => //; apply: ler_wpM2l.
  - apply: le_trans (ddg_hom_norm_comp _ _) _.
    have h1 := ddg_hom_norm_comp A T; rewrite (ddg_A_1_norm hT) in h1.
    have hTS : NH (T - S) = NH (S - T) by rewrite -opprB dgpr_hom_normN.
    rewrite hTS.
    by apply: ler_wpM2l => //; apply: ler_wpM2l.
have -> : PS + adjL PS - (PT + adjL PT) = (PS - PT) + adjL (PS - PT).
  by rewrite ddg_adjointB opprD !addrA [_ + adjL _ - _]addrAC.
apply: le_trans (ddg_hom_norm_triangle _ _) _.
rewrite ddg_hom_norm_adjoint.
apply: le_trans (lerD hP hP) _; apply: dgpr_eq_le; ring.
Qed.

(** Source for [dgpr_functional_subE]: Federer 1.4.1: the operations of
    Hom(X, R) are pointwise. Supporting lemma. *)
Lemma dgpr_functional_subE (X : lmodType R) (f g : Hom X R^o) x : (f - g) x = f x - g x.
Proof. by rewrite hom_addE. Qed.

(** Source for [dgpr_functionalB]: Federer 1.4.1: a member of Hom(X, R)
    is additive. Supporting lemma. *)
Lemma dgpr_functionalB (X : lmodType R) (f : Hom X R^o) x y : f (x - y) = f x - f y.
Proof. exact: linearB. Qed.

(** Source for [dgpr_square_le]: if 0 ≤ x, 0 ≤ K and x^2 ≤ K x, then
    x ≤ K. Supporting lemma. *)
Lemma dgpr_square_le (x K : R) : 0 <= x -> 0 <= K -> x ^+ 2 <= K * x -> x <= K.
Proof.
move=> hx hK h; have [->|hx0] := eqVneq x 0; first exact: hK.
have hxp : 0 < x by rewrite lt0r hx0 hx.
by rewrite -(ler_pM2r hxp) -expr2.
Qed.

Section BLocal.
Variable F : Hom Rn Rn -> R.

(** Source for [dgpr_B_local]: blueprint def:BF and Federer 3.1.22,
    p. 235: if g is of class 1 on an open set U with differentials D(S)
    and F = g on G(n, k) ∩ U, then for S ∈ G(n, k) ∩ U and
    L ∈ Hom(R^n, R^n),
    B_F(S) • L = F(S) (S • L) + D(S)(S^⊥ ∘ L ∘ S + (S^⊥ ∘ L ∘ S)^* ),
    since D(S) restricted to Tan(G(n, k), S) is the differential of F
    at S relative to G(n, k). Supporting lemma. *)
Lemma dgpr_B_local (U : set (Hom Rn Rn)) (g : Hom Rn Rn -> R^o)
    (D : Hom Rn Rn -> Hom (Hom Rn Rn) R^o) :
  is_norm_class_one_field NH N1 U g D -> (forall x, G x -> U x -> G x /\ F x = g x) ->
  forall S, G S -> U S -> forall L,
    HI (dgpr_B F S) L = F S * HI S L + D S (ddg_tangent_direction S L).
Proof.
move=> hfield hag S hS hUS L.
have hD := norm_class_one_differential hfield hUS.
have [Lp hLp] := tangent_differential_restriction_exists NH G S (D S).
have hrel : @has_relative_norm_differential R _ R^o NH N1 hNH G G F S Lp.
  split; first exact: subset_closure.
  by exists U, g, (D S); split=> //; split.
have hB := ddg_B_formula L hS hrel.
have [_ hv] := (hLp _ _).1 hB.
by rewrite /dgpr_B hv addrC subrK.
Qed.

(** Source for [dgpr_B_difference]: blueprint proof of lem:KF, the
    estimate behind the continuity of B_F: with g, U, D as in
    [dgpr_B_local], if |F(S) − F(C)| ≤ Λ |S − C|, |D(C)(w)| ≤ c |w| and
    |(D(S) − D(C))(v)| ≤ e |v| for all v and w, then
    |B_F(S) − B_F(C)| ≤ (Λ k^{1/2} + |F(C)| + c c₂) |S − C| + e c₁ with
    the constants c₁, c₂ of [dgpr_tangent_direction_bound] and
    [dgpr_tangent_direction_difference]. Supporting lemma. *)
Lemma dgpr_B_difference (U : set (Hom Rn Rn)) (g : Hom Rn Rn -> R^o)
    (D : Hom Rn Rn -> Hom (Hom Rn Rn) R^o) :
  is_norm_class_one_field NH N1 U g D -> (forall x, G x -> U x -> G x /\ F x = g x) ->
  forall (Lam Cc e : R) (C S : Hom Rn Rn), 0 <= Lam -> 0 <= Cc -> 0 <= e ->
  G C -> G S -> U C -> U S ->
  `|F S - F C| <= Lam * NH (S - C) ->
  (forall w, `|D C w| <= Cc * NH w) ->
  (forall v, `|(D S - D C) v| <= e * NH v) ->
  NH (dgpr_B F S - dgpr_B F C) <=
    (Lam * cS + `|F C| + Cc * (2 * (cn * (cP * cn) + cn * (cn * cS)))) * NH (S - C) +
    e * (2 * (cn * (cP * (cn * cS)))).
Proof.
move=> hfield hag Lam Cc e C S hLam hCc he hC hS hUC hUS hFL hDC hDS.
set A := dgpr_B F S - dgpr_B F C.
set ct := 2 * (cn * (cP * (cn * cS))).
set cd := 2 * (cn * (cP * cn) + cn * (cn * cS)).
have hcn : 0 <= cn := sqrtr_ge0 _.
have hcP : 0 <= cP := sqrtr_ge0 _.
have hcS : 0 <= cS := sqrtr_ge0 _.
have hct : 0 <= ct by rewrite /ct !mulr_ge0.
have hcd : 0 <= cd by rewrite /cd mulr_ge0 // addr_ge0 // !mulr_ge0.
have hA0 : 0 <= NH A := ddg_hom_norm_nonnegative A.
have hSC0 : 0 <= NH (S - C) := ddg_hom_norm_nonnegative _.
have hcs (x y : Hom Rn Rn) : `|HI x y| <= NH x * NH y := inner_cauchy hH x y.
have hsq : NH A ^+ 2 = HI A A := inner_norm_sqr hH A.
have hNS : NH S = cS := ddg_A_1_norm hS.
set tS := ddg_tangent_direction S A.
set tC := ddg_tangent_direction C A.
have hexp : HI A A = (F S - F C) * HI S A + F C * HI (S - C) A +
    ((D S - D C) tS + D C (tS - tC)).
  rewrite {1}/A (bilBl (inner_bilinear hH)) (dgpr_B_local hfield hag hS hUS)
    (dgpr_B_local hfield hag hC hUC) (bilBl (inner_bilinear hH)).
  rewrite dgpr_functional_subE dgpr_functionalB -/tS -/tC.
  ring.
have t1 : `|(F S - F C) * HI S A| <= Lam * NH (S - C) * (cS * NH A).
  rewrite normrM; apply: ler_pM => //; rewrite -hNS; exact: hcs.
have t2 : `|F C * HI (S - C) A| <= `|F C| * (NH (S - C) * NH A).
  by rewrite normrM; apply: ler_wpM2l => //; exact: hcs.
have t3 : `|(D S - D C) tS| <= e * (ct * NH A).
  apply: le_trans (hDS tS) _; apply: ler_wpM2l => //.
  exact: dgpr_tangent_direction_bound.
have t4 : `|D C (tS - tC)| <= Cc * (cd * NH (S - C) * NH A).
  apply: le_trans (hDC _) _; apply: ler_wpM2l => //.
  exact: dgpr_tangent_direction_difference.
have hK0 : 0 <= (Lam * cS + `|F C| + Cc * cd) * NH (S - C) + e * ct :=
  addr_ge0 (mulr_ge0 (addr_ge0 (addr_ge0 (mulr_ge0 hLam hcS) (normr_ge0 _)) (mulr_ge0 hCc hcd)) hSC0)
    (mulr_ge0 he hct).
apply: dgpr_square_le => //.
rewrite hsq; apply: le_trans (ler_norm _) _; rewrite hexp.
apply: le_trans (ler_normD _ _) _.
have t12 := le_trans (ler_normD _ _) (lerD t1 t2).
have t34 := le_trans (ler_normD _ _) (lerD t3 t4).
apply: le_trans (lerD t12 t34) _; apply: dgpr_eq_le; ring.
Qed.

End BLocal.

Section BContinuous.
Variable F : Hom Rn Rn -> R.
Hypothesis hF : @norm_class_relative R _ R^o NH N1 hNH hN1 G G F 1.

(** Source for [dgpr_B_continuous]: blueprint proof of lem:KF: the map
    B_F is continuous on G(n, k), because F is of class 1 relative to
    G(n, k) (Federer 3.1.22) and the differential of a local
    representative of class 1 is continuous (Federer 3.1.1); the
    estimate is [dgpr_B_difference]. *)
Theorem dgpr_B_continuous :
  continuous (fun S : GA => (dgpr_B F (set_val S) : real_norm_metric_space hNH)).
Proof.
have [Lam hLam hFL] := dgpr_integrand_lipschitz hF.
apply: dgpr_metric_continuous => c eps heps.
have hc : G (set_val c : Hom Rn Rn) := set_valP c.
have [U [g [hcU [hg hag]]]] := hF hc.
have [D hfield] := (norm_class_firstP hNH hN1 U g).1 hg.
have [[rU [hrU hUball]] _] := norm_class_one_zero hfield hcU.
have [Cc [hCc hCcb]] := norm_differential_bounded (norm_class_one_differential hfield hcU).
set ct := 2 * (cn * (cP * (cn * cS))).
set cd := 2 * (cn * (cP * cn) + cn * (cn * cS)).
have hcn : 0 <= cn := sqrtr_ge0 _.
have hcP : 0 <= cP := sqrtr_ge0 _.
have hcS : 0 <= cS := sqrtr_ge0 _.
have hct : 0 <= ct by rewrite /ct !mulr_ge0.
have hcd : 0 <= cd by rewrite /cd mulr_ge0 // addr_ge0 // !mulr_ge0.
have heps2 : 0 < eps / 2 by rewrite divr_gt0.
pose e := eps / 2 / (ct + 1).
have hct1 : 0 < ct + 1 by rewrite ltr_wpDl.
have he : 0 < e by rewrite /e divr_gt0.
have [d0 [hd0 hcont]] := norm_class_one_continuity hfield hcU he.
pose K1 := Lam * cS + `|F (set_val c)| + Cc * cd.
have hK1 : 0 <= K1 by rewrite /K1 !addr_ge0 // mulr_ge0.
have hK11 : 0 < K1 + 1 by rewrite ltr_wpDl.
pose d1 := eps / 2 / (K1 + 1).
have hd1 : 0 < d1 by rewrite /d1 divr_gt0.
exists (Num.min rU (Num.min d0 d1)); first by rewrite !lt_min hrU hd0 hd1.
move=> y hy.
set S := (set_val y : Hom Rn Rn).
have hS : G S := set_valP y.
have hySc : NH (S - set_val c) < Num.min rU (Num.min d0 d1).
  by rewrite -projection_grassmann_distanceE metric_sym.
have hrU' : NH (S - set_val c) < rU by apply: lt_le_trans hySc _; rewrite ge_min lexx.
have hd0' : NH (S - set_val c) < d0.
  by apply: lt_le_trans hySc _; rewrite !ge_min lexx orbT.
have hd1' : NH (S - set_val c) < d1.
  by apply: lt_le_trans hySc _; rewrite !ge_min lexx !orbT.
have hcS' : set_val c + (S - set_val c) = S by rewrite addrC subrK.
have hUS : U S by rewrite -hcS'; exact: hUball.
have hDS v : `|(D S - D (set_val c)) v| <= e * NH v.
  by have := hcont (S - set_val c) (ltac:(by rewrite hcS')) hd0' v; rewrite hcS'.
have hb := dgpr_B_difference hfield hag hLam hCc (ltW he) hc hS hcU hUS
  (hFL _ _ hS hc) hCcb hDS.
have -> : mdist (dgpr_B F (set_val c) : real_norm_metric_space hNH) (dgpr_B F S) =
    NH (dgpr_B F S - dgpr_B F (set_val c)).
  by rewrite real_norm_metric_distanceE -(inner_normN hH) opprB.
apply: le_lt_trans hb _.
rewrite -/ct -/cd -/K1.
have h1 : K1 * NH (S - set_val c) < eps / 2.
  have hle : K1 * NH (S - set_val c) <= (K1 + 1) * NH (S - set_val c).
    by rewrite ler_wpM2r ?ddg_hom_norm_nonnegative // lerDl.
  have hlt : (K1 + 1) * NH (S - set_val c) < (K1 + 1) * d1 by rewrite ltr_pM2l.
  have hd1e : (K1 + 1) * d1 = eps / 2 by rewrite /d1 mulrC divfK // lt0r_neq0.
  by rewrite -hd1e; exact: le_lt_trans hle hlt.
have h2 : e * ct < eps / 2.
  have hlt : e * ct < e * (ct + 1) by rewrite ltr_pM2l // ltrDl.
  have hee : e * (ct + 1) = eps / 2 by rewrite /e divfK // lt0r_neq0.
  by rewrite -hee.
lra.
Qed.

End BContinuous.

End BContinuity.
