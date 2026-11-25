(** De Philippis, De Rosa and Ghiraldin (2018), Appendix A, proof of
    Lemma A.2, p. 1144; blueprint new:flow, for Ω = R^n. Suppose
    g : R^n → R^n is of class 1 with derivative Dg (Federer 3.1.1, p. 210),
    Lip g ≤ K and |g(x)| ≤ M for x ∈ R^n, and set φ_t(x) = x + t g(x). If
    |t| K < 1, then φ_t is univalent, φ_t(x) = x whenever g(x) = 0,
    |φ_t(x) - x| ≤ |t| M, Dφ_t(x) = 1_{R^n} + t Dg(x) is univalent for every
    x, and φ_t is proper. Hence φ_t satisfies the hypotheses of Allard 3.2
    ([is_proper_class_one_immersion]) used to form the image varifold
    φ_t# V. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology ring lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities
  InnerMetric InnerBoundedness InnerFiniteCompactness LinearBasis Bilinear TensorUP Hom
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates HilbertFormCompactness
  RealNormUP NormDifferentialUP NormDifferentialLinear NormDifferentialArithmetic NormClassOneUP
  NormClassOneLaws ProperMapUP NormMetricScaleContinuity RealMetricBackground
  StieltjesDaniellIntegral.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardImageVarifoldMaps AllardImageVarifoldUP.
From DPDRG Require Import DdgLinearAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ddg_sub_swap]: if x + a = y + b in an abelian group,
    then x - y = b - a. Supporting lemma. *)
Lemma ddg_sub_swap (V : zmodType) (x y a b : V) : x + a = y + b -> x - y = b - a.
Proof.
move=> h; apply/eqP.
by rewrite subr_eq [b - a + y]addrAC [b + y]addrC -h addrK.
Qed.

Section Flow.
Variable R : realType.
Variable n : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation Nn := (inner_norm hBn).
Local Notation hNn := (inner_norm_real_norm hBn).
Local Notation RnM := (inner_metric_space hBn).
Local Notation idn := (hom_of_linear (linear_id Rn)).

Variables (g : Rn -> Rn) (Dg : Rn -> Hom Rn Rn).

(** Source for [ddg_flow]: blueprint new:flow: φ_t(x) = x + t g(x).
    Definition. *)
Definition ddg_flow (t : R) (x : Rn) : Rn := x + t *: g x.

(** Source for [ddg_flow_differential]: blueprint new:flow:
    Dφ_t(x) = 1_{R^n} + t Dg(x). Definition. *)
Definition ddg_flow_differential (t : R) (x : Rn) : Hom Rn Rn := idn + t *: Dg x.

(** Source for [ddg_flow_fixed]: blueprint new:flow: φ_t(x) = x if
    g(x) = 0, in particular for x ∉ spt g. Direct formalisation. *)
Lemma ddg_flow_fixed (t : R) (x : Rn) : g x = 0 -> ddg_flow t x = x.
Proof. by move=> hx; rewrite /ddg_flow hx scaler0 addr0. Qed.

(** Source for [ddg_flow_displacement]: proof of blueprint new:flow:
    |φ_t(x) - x| ≤ |t| sup |g|. Direct formalisation. *)
Lemma ddg_flow_displacement (M t : R) (x : Rn) :
  (forall y, Nn (g y) <= M) -> Nn (ddg_flow t x - x) <= `|t| * M.
Proof.
move=> hM; rewrite /ddg_flow addrC addKr inner_normZ.
by rewrite ler_wpM2l // hM.
Qed.

Hypothesis hg : is_norm_class_one_field Nn Nn setT g Dg.

(** Source for [ddg_flow_class_one]: blueprint new:flow: φ_t is of
    class 1 with Dφ_t(x) = 1_{R^n} + t Dg(x), Federer 3.1.1, p. 210, and
    3.1.1(3). Direct formalisation; class ∞ is not needed for Allard 3.2. *)
Theorem ddg_flow_class_one (t : R) :
  is_norm_class_one_field Nn Nn setT (ddg_flow t) (ddg_flow_differential t).
Proof.
have hint a : norm_domain_interior Nn setT a by exists 1; split=> //; exact: ltr01.
have hid : norm_bounded_linear Nn Nn idn.
  by exists 1; split=> // h; rewrite mul1r ddg_hom_idE.
have hd a : setT a -> has_norm_differential Nn Nn setT (ddg_flow t) a (ddg_flow_differential t a).
  move=> _.
  have h1 := @norm_differential_linear R Rn Rn Nn Nn hNn hNn setT a idn (hint a) hid.
  have h2 := @norm_differential_scale R Rn Rn Nn Nn hNn hNn setT g a (Dg a) t
    (norm_class_one_differential hg (I : setT a)).
  exact: (@norm_differential_add R Rn Rn Nn Nn hNn setT idn (fun x => t *: g x) a idn (t *: Dg a) h1 h2).
constructor.
- exact: (@norm_everywhere_differentiable_class_zero R Rn Rn Nn Nn hNn setT (ddg_flow t)
    (ddg_flow_differential t) hd).
- exact: hd.
- move=> a _ e he.
  have he' : 0 < e / (`|t| + 1) by rewrite divr_gt0 // ltr_pwDr // normr_ge0.
  have [d [hd0 hcont]] := norm_class_one_continuity hg (I : setT a) he'.
  exists d; split=> // h hah hh v.
  have -> : (ddg_flow_differential t (a + h) - ddg_flow_differential t a) v =
      t *: ((Dg (a + h) - Dg a) v).
    rewrite /ddg_flow_differential !ddg_hom_subE !hom_addE !hom_scaleE.
    by rewrite /ddg_flow_differential opprD addrACA subrr add0r scalerBr.
  rewrite inner_normZ.
  have hb := hcont h hah hh v.
  have hv := inner_norm_nonnegative hBn v.
  have ht := normr_ge0 t.
  apply: (le_trans (ler_wpM2l ht hb)).
  rewrite mulrA ler_wpM2r //.
  have ht1 : 0 < `|t| + 1 by lra.
  have hne : `|t| + 1 != 0 := lt0r_neq0 ht1.
  have h1 : `|t| * (e / (`|t| + 1)) <= (`|t| + 1) * (e / (`|t| + 1)).
    by rewrite ler_wpM2r ?ltW //; lra.
  by apply: (le_trans h1); rewrite mulrC divfK.
Qed.

(** Source for [ddg_flow_differential_bound]: Federer 3.1.1, p. 209:
    if Lip g ≤ K, then |Dg(x)(v)| ≤ K |v|. Supporting lemma. *)
Lemma ddg_flow_differential_bound (K : R) (x v : Rn) :
  (forall y z, Nn (g y - g z) <= K * Nn (y - z)) -> Nn (Dg x v) <= K * Nn v.
Proof.
move=> hK.
have hv := inner_norm_nonnegative hBn v.
have hdx := norm_class_one_differential hg (I : setT x).
have hv1 : 0 < Nn v + 1 by lra.
have hne1 : Nn v + 1 != 0 := lt0r_neq0 hv1.
apply/ler_addgt0Pr=> e he.
have he' : 0 < e / (Nn v + 1) by rewrite divr_gt0.
have [d [hd hrem]] := norm_differential_remainder hdx he'.
pose s := d / (2 * (Nn v + 1)).
have hv2 : 0 < 2 * (Nn v + 1) by lra.
have hne2 : 2 * (Nn v + 1) != 0 := lt0r_neq0 hv2.
have hs : 0 < s by rewrite /s divr_gt0.
have hsv : Nn (s *: v) < d.
  rewrite inner_normZ gtr0_norm //.
  have h1 : s * Nn v < s * (2 * (Nn v + 1)) by rewrite ltr_pM2l //; lra.
  have h2 : s * (2 * (Nn v + 1)) = d by rewrite /s divfK.
  by rewrite h2 in h1.
have hr := hrem (s *: v) I hsv.
have hgK := hK (x + s *: v) x.
rewrite addrAC subrr add0r in hgK.
have hDs : Dg x (s *: v) = s *: Dg x v by exact: linearZ.
rewrite hDs in hr.
have htri : Nn (s *: Dg x v) <= Nn (g (x + s *: v) - g x) + Nn (g (x + s *: v) - g x - s *: Dg x v).
  have e1 : s *: Dg x v = (g (x + s *: v) - g x) - (g (x + s *: v) - g x - s *: Dg x v).
    by rewrite opprB addrC subrK.
  rewrite {1}e1; exact: ddg_vector_norm_sub.
rewrite inner_normZ gtr0_norm // in htri.
rewrite inner_normZ gtr0_norm // in hgK.
rewrite inner_normZ gtr0_norm // in hr.
have hsum : s * Nn (Dg x v) <= s * (K * Nn v + e / (Nn v + 1) * Nn v).
  rewrite mulrDr; apply: (le_trans htri); apply: lerD.
    by rewrite mulrCA.
  by rewrite mulrCA.
rewrite ler_pM2l // in hsum.
apply: (le_trans hsum); rewrite lerD2l.
have h3 : e / (Nn v + 1) * Nn v <= e / (Nn v + 1) * (Nn v + 1).
  by rewrite ler_wpM2l ?ltW //; lra.
by rewrite divfK in h3.
Qed.

Variable K : R.
Hypothesis hK : forall y z, Nn (g y - g z) <= K * Nn (y - z).

(** Source for [ddg_flow_injective]: blueprint new:flow:
    |φ_t(x) - φ_t(y)| ≥ (1 - |t| Lip g) |x - y|, hence φ_t is univalent
    for |t| K < 1. Direct formalisation. *)
Theorem ddg_flow_injective (t : R) : `|t| * K < 1 -> injective (ddg_flow t).
Proof.
move=> htK x y hxy.
have e : x - y = t *: (g y - g x).
  by rewrite scalerBr; apply: ddg_sub_swap; exact: hxy.
have hb : Nn (x - y) <= `|t| * K * Nn (x - y).
  rewrite {1}e inner_normZ -mulrA ler_wpM2l //.
  by rewrite -inner_normN opprB; exact: hK.
have h0 : Nn (x - y) <= 0.
  have hn := inner_norm_nonnegative hBn (x - y).
  have : (1 - `|t| * K) * Nn (x - y) <= 0 by rewrite mulrBl mul1r subr_le0.
  by rewrite pmulr_rle0 // subr_gt0.
apply/eqP; rewrite -subr_eq0 -(inner_norm_eq0 hBn); apply/eqP.
by apply: le_anti; rewrite h0 inner_norm_nonnegative.
Qed.

(** Source for [ddg_flow_differential_injective]: blueprint new:flow:
    |Dφ_t(x)(v)| ≥ (1 - |t| Lip g) |v|, hence Dφ_t(x) is univalent for
    |t| K < 1. Direct formalisation. *)
Theorem ddg_flow_differential_injective (t : R) (x : Rn) :
  `|t| * K < 1 -> injective (ddg_flow_differential t x).
Proof.
move=> htK v w hvw.
have hz : ddg_flow_differential t x (v - w) = 0.
  by rewrite ddg_homB hvw subrr.
have e : v - w = - (t *: Dg x (v - w)).
  move: hz; rewrite /ddg_flow_differential hom_addE hom_scaleE ddg_hom_idE=> /eqP.
  by rewrite addr_eq0=> /eqP.
have hb : Nn (v - w) <= `|t| * K * Nn (v - w).
  rewrite {1}e inner_normN inner_normZ -mulrA ler_wpM2l //.
  exact: ddg_flow_differential_bound.
have h0 : Nn (v - w) <= 0.
  have hn := inner_norm_nonnegative hBn (v - w).
  have : (1 - `|t| * K) * Nn (v - w) <= 0 by rewrite mulrBl mul1r subr_le0.
  by rewrite pmulr_rle0 // subr_gt0.
apply/eqP; rewrite -subr_eq0 -(inner_norm_eq0 hBn); apply/eqP.
by apply: le_anti; rewrite h0 inner_norm_nonnegative.
Qed.

(** Source for [ddg_flow_continuous]: φ_t is Lipschitz with constant
    1 + |t| K, hence continuous. Supporting lemma. *)
Lemma ddg_flow_continuous (t : R) : 0 <= K -> continuous (fun x : RnM => (ddg_flow t x : RnM)).
Proof.
move=> hK0.
apply: (@metric_fixed_lipschitz_continuous R RnM RnM _ (1 + `|t| * K)).
  by rewrite addr_ge0 // mulr_ge0.
move=> x y; change (Nn (ddg_flow t x - ddg_flow t y) <= (1 + `|t| * K) * Nn (x - y)).
have e : ddg_flow t x - ddg_flow t y = (x - y) + t *: (g x - g y).
  by rewrite /ddg_flow scalerBr opprD addrACA.
rewrite e; apply: (le_trans (ddg_vector_norm_triangle _ _)).
rewrite mulrDl mul1r lerD2l inner_normZ -mulrA ler_wpM2l //.
Qed.

(** Source for [ddg_norm_continuous]: the norm of R^n is continuous,
    Federer 1.7.1, p. 28. Supporting lemma. *)
Lemma ddg_norm_continuous : continuous (fun x : RnM => (Nn x : real_line_metric R)).
Proof.
apply: (@metric_fixed_lipschitz_continuous R RnM (real_line_metric R) _ 1 ler01).
move=> x y; rewrite real_line_metric_distanceE mul1r.
change (`|Nn x - Nn y| <= Nn (x - y)).
rewrite ler_norml; apply/andP; split.
  rewrite lerBrDr -[Nn y]inner_normN.
  have := ddg_vector_norm_triangle (x - y) (- x).
  by rewrite addrAC subrr add0r -opprB inner_normN [Nn (- x)]inner_normN; lra.
have := ddg_vector_norm_triangle (x - y) y.
by rewrite subrK; lra.
Qed.

(** Source for [ddg_compact_bounded]: a compact subset of R^n is
    bounded. Supporting lemma. *)
Lemma ddg_compact_bounded (C : set RnM) : compact C -> exists r : R, forall x, C x -> Nn x <= r.
Proof.
move=> hC.
have hNC : compact ((fun x : RnM => (Nn x : real_line_metric R)) @` C).
  exact: (continuous_compact (continuous_subspaceT ddg_norm_continuous) hC).
have [r hr] := compact_real_bounded hNC.
exists r=> x hx; have := hr (Nn x) (ex_intro2 _ _ x hx erefl).
by rewrite ger0_norm // inner_norm_nonnegative.
Qed.

(** Source for [ddg_flow_proper]: blueprint new:flow, last sentence of the
    proof: if C is compact, then φ_t^{-1}[C] is closed and contained in
    {x : |x| ≤ sup_C |·| + |t| sup |g|}, hence compact. Direct
    formalisation for Ω = R^n. *)
Theorem ddg_flow_proper (M t : R) :
  0 <= K -> (forall y, Nn (g y) <= M) -> is_proper_map (fun x : RnM => (ddg_flow t x : RnM)).
Proof.
move=> hK0 hM C hC.
have hCc : closed C := compact_closed (@metric_hausdorff R RnM) hC.
have hcont := ddg_flow_continuous (t := t) hK0.
have hpre : closed ((fun x : RnM => (ddg_flow t x : RnM)) @^-1` C) :=
  (proj1 (continuous_closedP _) hcont) C hCc.
have [r hr] := ddg_compact_bounded hC.
apply: (@inner_finite_basis_boundedly_compact R _ _ hBn _ _ hbn _ hpre).
exists (r + `|t| * M)=> x hx.
have h1 := hr _ hx.
have h2 := ddg_flow_displacement t x hM.
have e : x = ddg_flow t x - (ddg_flow t x - x) by rewrite opprB addrC subrK.
rewrite e; apply: (le_trans (ddg_vector_norm_sub _ _)); exact: lerD.
Qed.

(** Source for [ddg_flow_immersion]: blueprint new:flow and the proof of
    ddg:A.2: for |t| K < 1 the map φ_t satisfies the hypotheses of
    Allard 3.2, p. 430: it is of class 1, every Dφ_t(x) is univalent, and
    φ_t is proper. Direct formalisation for Ω = R^n. *)
Theorem ddg_flow_immersion (M t : R) :
  0 <= K -> (forall y, Nn (g y) <= M) -> `|t| * K < 1 ->
  is_proper_class_one_immersion (ddg_flow t) (ddg_flow_differential t).
Proof.
move=> hK0 hM htK; split.
- exact: ddg_flow_class_one.
- by move=> x; exact: ddg_flow_differential_injective.
- exact: ddg_flow_proper hK0 hM.
Qed.

End Flow.
