(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    thm:main, proof: the cut-off functions φ_ϱ and their products with
    test functions.

    The normalised smooth cut-off of Federer 3.1.23 ([AnnularCutoff],
    with inner radius 1/2), scaled to the radius 2ϱ, is a function
    φ_ϱ of class ∞ on R^n with 0 ≤ φ_ϱ ≤ 1, φ_ϱ(x) = 1 for |x| ≤ ϱ,
    φ_ϱ(x) = 0 for |x| ≥ 2ϱ, and |Dφ_ϱ(x)(v)| ≤ c_0 ϱ^{-1} |v|, where
    c_0 does not depend on ϱ ([dgpr_main_cutoff]). Multiplication by
    φ_ϱ is a linear map of D(R^n, Y) into itself (Federer 4.1.1,
    [test_multiplier_operator]), and
    D(φ_ϱ g)(x) = Dφ_ϱ(x) · g(x) + φ_ϱ(x) Dg(x)
    ([dgpr_product_differential]), with the rank one map ω · b of
    Allard 2.3(4) ([dgpr_rank_one]); a real function of class ∞ on R^n
    is continuous and has a differential at every point
    ([dgpr_smooth_real_differential]). The file also contains the
    estimates of Hom(R^n, Y) used in the proof:
    |X • (ω · b)| = |ω(X^*(b))| ≤ a |X| |b| whenever |ω(v)| ≤ a |v|
    ([dgpr_rank_one_inner_bound]), |F| ≤ n^{1/2} a whenever
    |F(v)| ≤ a |v| ([dgpr_hom_norm_le]), and the continuity of a
    continuous differential field for the norm |·| of Hom(R^n, Y)
    ([dgpr_differential_field_continuous]). *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm InnerProductLaws
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis
  HomInner HomNormBound HomOperatorNorm OperatorNorm OperatorNormUP Adjoint AdjointUP InnerMetric
  NormDifferentialUP NormDifferentialScalarProduct NormHigherCurveDerivativeUP NormClassOneUP
  NormClassZeroTopology RealMetricBackground
  NormRegularity CoefficientCoordinates SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  SmoothMultiplierUP SmoothMultiplierSealed TestMultiplierOperator AnnularCutoffUP AnnularCutoffSealed
  AnnularCutoffScaling ScaledCutoffUP EuclideanDistributionMeasureContext.
From DPGPR Require Import DgprHomNorms DgprMichaelSimon.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Cutoff.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation RnM := (inner_metric_space BX).

(** Source for [dgpr_main_cutoff]: blueprint proof of thm:main, the
    choice of φ and of c_0 = sup |grad φ|, with the functions
    φ_ϱ(x) = φ(ϱ^{-1} x). Here φ_ϱ is the smooth cut-off of Federer
    3.1.23, p. 237, equal to one on B(0, ϱ) and to zero outside
    U(0, 2ϱ), and c_0 is a bound for the differential of the normalised
    cut-off of Federer 3.1.23 ([AnnularCutoff.bound]). Direct
    formalisation. *)
Lemma dgpr_main_cutoff : exists c : R, 0 < c /\ forall r : R, 0 < r ->
  exists w : X -> R,
    [/\ forall x, 0 <= w x <= 1, forall x, N x <= r -> w x = 1,
      forall x, 2 * r <= N x -> w x = 0,
      norm_class_all_orders hN (@scalar_absolute_value_norm R) setT w &
      forall x (L : Hom X R^o), has_norm_differential N (fun t : R^o => `|t|) setT w x L ->
        forall v, `|L v| <= c / r * N v].
Proof.
have h2 : (0 : R) < 2 by rewrite ltr0n.
have ht : 0 < (2^-1 : R) < 1 by rewrite invr_gt0 h2 /= invf_lt1 // ltr1n.
have hu := AnnularCutoff.laws BX heX ht.
set c := AnnularCutoff.bound BX heX ht.
have hc : 0 < c := annular_cutoff_bound_positive hu.
exists c; split=> // r hr.
have h2r : 0 < 2 * r by rewrite mulr_gt0.
have [w hw] := scaled_annular_cutoff_exists 0 hu h2r.
exists w; split.
- exact: scaled_cutoff_range hw.
- move=> x hx; apply: (scaled_cutoff_inner hw).
  by rewrite subr0 mulrA mulVf ?mul1r //; lra.
- by move=> x hx; apply: (scaled_cutoff_outer hw); rewrite subr0.
- exact: scaled_cutoff_smooth hw.
- move=> x L hL v; apply: le_trans (scaled_cutoff_differential_bound hw hL v) _.
  apply: ler_wpM2r; first exact: inner_norm_nonnegative.
  rewrite ler_wpM2l ?(ltW hc) // lef_pV2 ?posrE //; lra.
Qed.

(** Source for [dgpr_smooth_real_differential]: Federer 3.1.1, p. 210,
    and 3.1.11, p. 220: a real function w of class ∞ on R^n has a
    differential Dw(x) at every x ∈ R^n, and w is continuous.
    Supporting lemma. *)
Lemma dgpr_smooth_real_differential (w : X -> R) :
  norm_class_all_orders hN (@scalar_absolute_value_norm R) setT w ->
  (exists Dw : X -> Hom X R^o, forall x, has_norm_differential N (fun t : R^o => `|t|) setT w x (Dw x)) /\
  continuous (fun x : RnM => (w x : real_line_metric R)).
Proof.
move=> hw.
have [D hD] := (norm_class_firstP hN (@scalar_absolute_value_norm R) setT w).1 (hw 1%N).
split; first by exists D => x; exact: (norm_class_one_differential hD (Logic.I : setT x)).
have hc : continuous (fun y : real_norm_metric_space hN =>
    (w y : real_norm_metric_space (@scalar_absolute_value_norm R))).
  move=> a; exact: (@norm_class_zero_continuous_at R _ _ _ _ hN (@scalar_absolute_value_norm R)
    setT w a (norm_class_one_zero hD) Logic.I).
apply: dgpr_real_norm_line_continuous => x.
apply: continuous_comp (@euclidean_distribution_inner_to_norm R n x) _.
exact: hc.
Qed.

End Cutoff.

Section HomEstimates.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Local Notation RnM := (inner_metric_space BX).
Variable Y : lmodType R.
Variable CY : Y -> Y -> R.
Hypothesis hCY : is_inner_product CY.
Variable d : nat.
Variable eY : 'I_d -> Y.
Hypothesis heY : is_basis eY.
Local Notation NY := (inner_norm hCY).
Local Notation BH := (hom_inner_productP BX hCY heX).
Local Notation HI := (hom_inner BX hCY heX).
Local Notation NH := (hom_norm BX hCY heX).
Local Notation hNH := (inner_norm_real_norm BH).

(** Source for [dgpr_hom_norm_le]: Federer 1.7.6, p. 33, and 1.7.9,
    p. 35 ([hom_operator_norm_comparison]): if |F(v)| ≤ a |v| for
    v ∈ R^n, then ‖F‖ ≤ a and |F| ≤ n^{1/2} ‖F‖ ≤ n^{1/2} a.
    Supporting lemma. *)
Lemma dgpr_hom_norm_le (F : Hom X Y) (a : R) : 0 <= a ->
  (forall v, NY (F v) <= a * N v) -> NH F <= Num.sqrt n%:R * a.
Proof.
move=> ha hF.
have hL := linear_operator_normP BX hCY heX (hom_as_linear F).
have hLa : linear_operator_norm BX hCY heX (hom_as_linear F) <= a.
  have [x [hx hxe]] := operator_norm_attained hL.
  rewrite -hxe; apply: le_trans (hF x) _.
  by rewrite -[X in _ <= X]mulr1 ler_wpM2l.
apply: le_trans (hom_operator_norm_comparison BX hCY heX F).2 _.
by apply: ler_wpM2l; [exact: sqrtr_ge0 | exact: hLa].
Qed.

(** Source for [dgpr_rank_one_inner_bound]: blueprint proof of
    thm:main, X • (Dφ_ϱ · g) = Dφ_ϱ(X^*(g)) and ‖X^*‖ ≤ |X^*| = |X|
    (DgprHomNorms.v): if |ω(v)| ≤ a |v| for v ∈ R^n, then
    |A • (ω · b)| ≤ a |A| |b| for A ∈ Hom(R^n, Y) and b ∈ Y.
    Supporting lemma. *)
Lemma dgpr_rank_one_inner_bound (A : Hom X Y) (omega : Hom X R^o) (b : Y) (a : R) :
  0 <= a -> (forall v, `|omega v| <= a * N v) -> `|HI A (dgpr_rank_one omega b)| <= a * NH A * NY b.
Proof.
move=> ha hw.
rewrite (inner_symmetric BH) (dgpr_rank_one_inner BX hCY heX omega b A).
apply: le_trans (hw _) _.
rewrite -mulrA; apply: ler_wpM2l => //.
have h := hom_norm_vector_bound hCY BX heY
  (hom_of_linear (inner_adjoint BX hCY heX (hom_as_linear A))) b.
rewrite (dgpr_hom_norm_adjoint BX hCY heX heY A) hom_of_linearE in h.
exact: h.
Qed.

(** Source for [dgpr_differential_field_continuous]: Federer 3.1.1,
    p. 210: a differential field D continuous in the operator norm
    ([norm_field_continuous]) is continuous for the norm |·| of
    Hom(R^n, Y), by [dgpr_hom_norm_le]. Supporting lemma. *)
Lemma dgpr_differential_field_continuous (D : X -> Hom X Y) :
  norm_field_continuous N NY setT D -> continuous (fun x : RnM => (D x : real_norm_metric_space hNH)).
Proof.
move=> hD.
suff hc : continuous (fun x : real_norm_metric_space hN => (D x : real_norm_metric_space hNH)).
  move=> x; apply: continuous_comp (@euclidean_distribution_inner_to_norm R n x) _.
  exact: hc.
move=> a W hW.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP
  (D a : real_norm_metric_space hNH) W) hW.
have hs : 0 < Num.sqrt n%:R + 1 :> R by have := sqrtr_ge0 (n%:R : R); lra.
pose e' := e / (Num.sqrt n%:R + 1).
have he' : 0 < e' by rewrite divr_gt0.
have [r [hr hb]] := hD a Logic.I e' he'.
apply: (proj2 (metricType_numDomainType.nbhs_mdistP (a : real_norm_metric_space hN) _)).
exists r => // x hx; apply: hball.
change (is_true (NH (D a - D x) < e)).
have hxa : N (x - a) < r.
  rewrite (real_seminorm_subtract hN.1); exact hx.
have hb' := hb (x - a) Logic.I hxa.
rewrite (addrC a (x - a)) subrK in hb'.
have e1 : NH (D a - D x) = NH (D x - D a) by rewrite /hom_norm (real_seminorm_subtract hNH.1).
rewrite e1; apply: le_lt_trans (dgpr_hom_norm_le (ltW he') hb') _.
by rewrite /e' mulrA ltr_pdivrMr // mulrDr mulr1 [e * _]mulrC ltrDl.
Qed.

End HomEstimates.

Section TestProducts.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Variable Y : lmodType R.
Variable NY : Y -> R.
Hypothesis hNY : is_real_norm NY.
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.

(** Source for [dgpr_test_multiplier]: Federer 4.1.1, p. 345: for a
    function w of class ∞ on R^n, multiplication by w is a linear map
    P of D(R^n, Y) into itself with (P g)(x) = w(x) g(x)
    ([test_multiplier_operator]); in the proof of thm:main it is
    the map [g ↦ φ_ϱ g]. Supporting lemma. *)
Lemma dgpr_test_multiplier (w : X -> R) :
  norm_class_all_orders hN (@scalar_absolute_value_norm R) setT w ->
  exists P : Hom (smooth_test_space hE) (smooth_test_space hE),
    forall g x, smooth_test_value hE (P g) x = w x *: smooth_test_value hE g x.
Proof.
move=> hw.
have hP := SmoothMultiplier.laws hE hw.
exists (test_multiplier_operator hE hP) => g x.
rewrite /smooth_test_value test_multiplier_evaluation.
exact: hP.
Qed.

(** Source for [dgpr_product_differential]: blueprint proof of
    thm:main, D(φ_ϱ g) = φ_ϱ Dg + Dφ_ϱ · g, by the product rule of
    Federer 3.1.11, pp. 220–222 ([norm_differential_scalar_product]).
    Supporting lemma. *)
Lemma dgpr_product_differential (w : X -> R) (g : X -> Y) (x : X) (L : Hom X R^o) (Dg : Hom X Y) :
  has_norm_differential N (fun t : R^o => `|t|) setT w x L ->
  has_norm_differential N NY setT g x Dg ->
  has_norm_differential N NY setT (fun y => w y *: g y) x (dgpr_rank_one L (g x) + w x *: Dg).
Proof.
move=> hw hg.
have h := norm_differential_scalar_product hN hNY hw hg.
suff -> : dgpr_rank_one L (g x) + w x *: Dg = scalar_vector_product_linear_term (w x) (g x) L Dg.
  exact: h.
apply: hom_ext => v.
by rewrite /scalar_vector_product_linear_term !hom_addE dgpr_rank_oneE hom_compE.
Qed.

End TestProducts.
