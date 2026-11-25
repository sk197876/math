(** De Philippis, De Rosa and Ghiraldin (2018), Lemma A.1, p. 1143;
    blueprint ddg:A.lemma1 (item A.5 of the blueprint).

    "Let T ∈ G(n, d) and L ∈ R^n ⊗ R^n, and let us define T(t) ∈ G(n, d)
    as the orthogonal projection onto (Id + tL)(T). Then
    T'(0) = T^⊥ ∘ L ∘ T + (T^⊥ ∘ L ∘ T)^* ∈ Tan_T G(n, d)."

    The derivative is the derivative of a curve in the normed space
    Hom(R^n, R^n) of Federer 2.9.22 ([has_normed_curve_derivative]), for
    the norm |A| = (A • A)^{1/2} of Allard 2.2. The statement
    [ddg_lemma_A_1] applies to every family P(t) of orthogonal projections
    onto (1_{R^n} + t L)[im T] defined for |t| < δ; the curve
    [ddg_moving_plane] of DdgMovingPlane.v is such a family
    ([ddg_lemma_A_1_moving_plane]). The membership in Tan_T G(n, d) is
    proved in DdgGrassmannTangent.v.

    The proof differs from DDG's, which differentiates
    T(t) ∘ (Id + tL) ∘ T = (Id + tL) ∘ T after asserting the smoothness of
    T(t). With h ≠ 0 small and P = T(h) one has

        h^{-1} (P - T) - T'(0) = Y_1 + Y_2 + Y_3,

    where Y_1(v) = (T - P)(L(T(v))), Y_2 = h^{-1} T ∘ P ∘ T^⊥ - (T^⊥ ∘ L ∘ T)^*
    satisfies Y_2(v) • w = - v • T^⊥((P - T)(L(T(w)))), and
    Y_3 = h^{-1} T^⊥ ∘ (P - T) ∘ (P - T) ∘ T^⊥; the estimate
    |(P - T)(v)| ≤ 3 |h| |L| |v| of DdgMovingPlane.v gives
    |Y_1 + Y_2 + Y_3| ≤ 15 n^{1/2} |L|^2 |h|. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals ring lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities
  LinearBasis Bilinear TensorUP Hom HomInner HomInnerCoordinates AdjointUP AdjointLaws Adjoint
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates EuclideanRectangularAdjoint
  TraceDefinition TraceCyclic HilbertFormCompactness RealNormUP NormedCurveDerivativeUP.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardProjectionFormula.
From DPDRG Require Import DdgLinearAlgebra DdgGrassmann DdgMovingPlane.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section LemmaA1.
Variable R : realType.
Variables n d : nat.
Local Notation Rn := (R_n R n).
Local Notation Bn := (@euclidean_inner_product R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation Nn := (inner_norm hBn).
Local Notation NH := (hom_norm hBn hBn hbn).
Local Notation adjL L := (euclidean_rectangular_adjoint L).
Local Notation idn := (hom_of_linear (linear_id Rn)).
Local Notation G := (orthogonal_projectors R n d).

(** Source for [ddg_tangent_direction]: DDG Lemma A.1, p. 1143:
    T^⊥ ∘ L ∘ T + (T^⊥ ∘ L ∘ T)^*, the derivative T'(0) and the argument
    of d_T F in (A.5), p. 1144. Definition. *)
Definition ddg_tangent_direction (T L : Hom Rn Rn) : Hom Rn Rn :=
  hom_comp (ddg_perp T) (hom_comp L T) + adjL (hom_comp (ddg_perp T) (hom_comp L T)).

(** Source for [ddg_tangent_directionE]: the value of
    T^⊥ ∘ L ∘ T + (T^⊥ ∘ L ∘ T)^* at v. Supporting lemma. *)
Lemma ddg_tangent_directionE (T L : Hom Rn Rn) v :
  ddg_tangent_direction T L v =
  ddg_perp T (L (T v)) + adjL (hom_comp (ddg_perp T) (hom_comp L T)) v.
Proof. by rewrite /ddg_tangent_direction hom_addE !hom_compE. Qed.

Section Quotient.
Variables T L P : Hom Rn Rn.
Variable h : R.
Hypothesis hT : G T.
Hypothesis hP : is_ddg_plane_projection d (idn + h *: L) T P.
Hypothesis hsmall : NH L * `|h| <= 1 / 2.
Hypothesis hh : h != 0.
Local Notation c := (NH L).
Local Notation hP0 := (ddg_plane_member hP).

(** Source for [ddg_quotient_nonnegative]: 0 ≤ |L| and 0 ≤ |h|.
    Supporting lemma. *)
Lemma ddg_quotient_nonnegative : 0 <= c /\ 0 <= `|h|.
Proof. by split; [exact: ddg_hom_norm_nonnegative|exact: normr_ge0]. Qed.

(** Source for [ddg_quotient_estimate_vector]: [ddg_plane_estimate]
    in the form |(P - T)(y)| ≤ 3 |h| |L| |y|. Supporting lemma. *)
Lemma ddg_quotient_estimate_vector y : Nn ((P - T) y) <= 3 * (`|h| * c) * Nn y.
Proof. exact: ddg_plane_estimate hT hP hsmall y. Qed.

(** Source for [ddg_quotient_part1]: proof of DDG Lemma A.1:
    h^{-1}(- P^⊥(T(v))) - T^⊥(L(T(v))) = (T - P)(L(T(v))), and its norm
    is at most 3 |L|^2 |h| |v|. Supporting lemma. *)
Lemma ddg_quotient_part1 v :
  Nn (h^-1 *: (- ddg_perp P (T v)) - ddg_perp T (L (T v))) <= 3 * (c ^+ 2 * `|h|) * Nn v.
Proof.
have [hc0 hh0] := ddg_quotient_nonnegative.
rewrite (ddg_plane_perp_T hP) opprK scalerA mulVf // scale1r.
have he : ddg_perp P (L (T v)) - ddg_perp T (L (T v)) = - ((P - T) (L (T v))).
  by rewrite !ddg_perpE ddg_hom_subE ddg_sub_sub.
rewrite he inner_normN.
apply: (le_trans (ddg_quotient_estimate_vector _)).
have h1 : Nn (L (T v)) <= c * Nn v.
  apply: (le_trans (ddg_hom_vector_bound L (T v))).
  by rewrite ler_wpM2l // (ddg_projector_contraction hT).
have h2 : 3 * (`|h| * c) * Nn (L (T v)) <= 3 * (`|h| * c) * (c * Nn v).
  by rewrite ler_wpM2l // mulr_ge0 // mulr_ge0.
apply: (le_trans h2); rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

(** Source for [ddg_quotient_part2_pairing]: proof of DDG Lemma A.1:
    with Y_2 = h^{-1} T ∘ P ∘ T^⊥ - (T^⊥ ∘ L ∘ T)^*, one has
    Y_2(v) • w = - v • T^⊥((P - T)(L(T(w)))). Supporting lemma. *)
Lemma ddg_quotient_part2_pairing v w :
  Bn (h^-1 *: T (P (ddg_perp T v)) - adjL (hom_comp (ddg_perp T) (hom_comp L T)) v) w =
  - Bn v (ddg_perp T ((P - T) (L (T w)))).
Proof.
have hb := inner_bilinear hBn.
have hPT : P (T w) = T w + h *: ddg_perp P (L (T w)).
  have := ddg_perpE P (T w); rewrite (ddg_plane_perp_T hP)=> he.
  by rewrite -[h *: _]opprK he opprB addrC subrK.
have h1 : Bn (T (P (ddg_perp T v))) w = h * Bn v (ddg_perp T (ddg_perp P (L (T w)))).
  rewrite (ddg_projector_sym hT) (ddg_projector_sym hP0) (ddg_perp_sym hT) hPT.
  by rewrite ddg_homD (ddg_proj_perp hT) add0r ddg_homZ (bilZr hb).
have h2 : Bn (adjL (hom_comp (ddg_perp T) (hom_comp L T)) v) w =
    Bn v (ddg_perp T (L (T w))).
  by rewrite (inner_symmetric hBn) ddg_adjoint_pairing !hom_compE (inner_symmetric hBn).
rewrite (bilBl hb) (bilZl hb) h1 h2 scalerA mulVf // scale1r.
rewrite -(bilBr hb) -[RHS]sub0r -(bil0r hb v) -(bilBr hb) sub0r; congr (Bn v _).
rewrite -ddg_homB ddg_hom_subE [in RHS]ddg_homB (ddg_proj_perp hT) subr0.
by rewrite [ddg_perp P _]ddg_perpE addrAC subrr add0r ddg_homN.
Qed.

(** Source for [ddg_quotient_part2]: proof of DDG Lemma A.1:
    |Y_2(v)| ≤ 3 |L|^2 |h| |v|. Supporting lemma. *)
Lemma ddg_quotient_part2 v :
  Nn (h^-1 *: T (P (ddg_perp T v)) - adjL (hom_comp (ddg_perp T) (hom_comp L T)) v)
  <= 3 * (c ^+ 2 * `|h|) * Nn v.
Proof.
have [hc0 hh0] := ddg_quotient_nonnegative.
set Y := _ - _.
apply: ddg_vector_bound_by_pairing.
  by rewrite mulr_ge0 ?inner_norm_nonnegative // mulr_ge0 // mulr_ge0 // exprn_ge0.
rewrite /Y ddg_quotient_part2_pairing -/Y.
apply: (le_trans (ler_norm _)); rewrite normrN.
apply: (le_trans (ddg_vector_cauchy _ _)).
have h1 : Nn (ddg_perp T ((P - T) (L (T Y)))) <= 3 * (`|h| * c) * (c * Nn Y).
  apply: (le_trans (ddg_perp_contraction hT _)).
  apply: (le_trans (ddg_quotient_estimate_vector _)).
  rewrite ler_wpM2l ?mulr_ge0 //.
  apply: (le_trans (ddg_hom_vector_bound L (T Y))).
  by rewrite ler_wpM2l // (ddg_projector_contraction hT).
have h2 : Nn v * Nn (ddg_perp T ((P - T) (L (T Y)))) <=
    Nn v * (3 * (`|h| * c) * (c * Nn Y)).
  by rewrite ler_wpM2l // inner_norm_nonnegative.
apply: (le_trans h2); rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

(** Source for [ddg_quotient_part3]: proof of DDG Lemma A.1:
    T^⊥(P(T^⊥(v))) = T^⊥((P - T)((P - T)(T^⊥(v)))), hence
    |h^{-1} T^⊥(P(T^⊥(v)))| ≤ 9 |L|^2 |h| |v|. Supporting lemma. *)
Lemma ddg_quotient_part3 v :
  Nn (h^-1 *: ddg_perp T (P (ddg_perp T v))) <= 9 * (c ^+ 2 * `|h|) * Nn v.
Proof.
have [hc0 hh0] := ddg_quotient_nonnegative.
have he : ddg_perp T (P (ddg_perp T v)) =
    ddg_perp T ((P - T) ((P - T) (ddg_perp T v))).
  set z := (P - T) (ddg_perp T v).
  have hz : P (ddg_perp T v) = z by rewrite /z ddg_hom_subE (ddg_perp_proj hT) subr0.
  clearbody z.
  rewrite -(ddg_projector_idem hP0 (ddg_perp T v)) hz (ddg_hom_subE P T z) ddg_homB.
  by rewrite (ddg_proj_perp hT) subr0.
rewrite he inner_normZ normfV.
have h1 : Nn (ddg_perp T ((P - T) ((P - T) (ddg_perp T v)))) <=
    3 * (`|h| * c) * (3 * (`|h| * c) * Nn v).
  apply: (le_trans (ddg_perp_contraction hT _)).
  apply: (le_trans (ddg_quotient_estimate_vector _)).
  rewrite ler_wpM2l ?mulr_ge0 //.
  apply: (le_trans (ddg_quotient_estimate_vector _)).
  by rewrite ler_wpM2l ?mulr_ge0 // (ddg_perp_contraction hT).
have hpos : 0 < `|h| by rewrite normr_gt0.
have h2 : `|h|^-1 * Nn (ddg_perp T ((P - T) ((P - T) (ddg_perp T v)))) <=
    `|h|^-1 * (3 * (`|h| * c) * (3 * (`|h| * c) * Nn v)).
  by rewrite ler_wpM2l // invr_ge0.
apply: (le_trans h2); rewrite le_eqVlt; apply/orP; left; apply/eqP.
by field; rewrite gt_eqF.
Qed.

(** Source for [ddg_quotient_decomposition]: proof of DDG Lemma A.1:
    (h^{-1}(P - T) - T'(0))(v) = Y_1(v) + Y_2(v) + Y_3(v). Supporting
    lemma. *)
Lemma ddg_quotient_decomposition v :
  (h^-1 *: (P - T) - ddg_tangent_direction T L) v =
  (h^-1 *: (- ddg_perp P (T v)) - ddg_perp T (L (T v))) +
  (h^-1 *: T (P (ddg_perp T v)) - adjL (hom_comp (ddg_perp T) (hom_comp L T)) v) +
  h^-1 *: ddg_perp T (P (ddg_perp T v)).
Proof.
rewrite ddg_hom_subE hom_scaleE ddg_tangent_directionE ddg_plane_difference.
rewrite {1}(ddg_perp_decomposition T (P (ddg_perp T v))) scalerBr scalerDr scalerN.
exact: ddg_rearrange.
Qed.

(** Source for [ddg_quotient_estimate]: proof of DDG Lemma A.1:
    |h^{-1}(P - T) - T'(0)| ≤ 15 n^{1/2} |L|^2 |h|. Supporting lemma. *)
Theorem ddg_quotient_estimate :
  NH (h^-1 *: (P - T) - ddg_tangent_direction T L) <=
  Num.sqrt n%:R * (15 * (c ^+ 2 * `|h|)).
Proof.
have [hc0 hh0] := ddg_quotient_nonnegative.
apply: ddg_hom_norm_from_vector_bound.
  by rewrite mulr_ge0 // mulr_ge0 // exprn_ge0.
move=> v; rewrite ddg_quotient_decomposition.
apply: (le_trans (ddg_vector_norm_triangle _ _)).
have h3 := ddg_quotient_part3 v.
apply: (le_trans (lerD (ddg_vector_norm_triangle _ _) (lexx _))).
have h1 := ddg_quotient_part1 v.
have h2 := ddg_quotient_part2 v.
have he : 15 * (c ^+ 2 * `|h|) * Nn v =
  3 * (c ^+ 2 * `|h|) * Nn v + 3 * (c ^+ 2 * `|h|) * Nn v + 9 * (c ^+ 2 * `|h|) * Nn v.
  by ring.
by rewrite he lerD // lerD.
Qed.
End Quotient.

(** Source for [ddg_lemma_A_1]: DDG Lemma A.1, p. 1143; blueprint
    ddg:A.lemma1: "T'(0) = T^⊥ ∘ L ∘ T + (T^⊥ ∘ L ∘ T)^*", for every
    family P(t), |t| < δ, of orthogonal projections onto
    (1_{R^n} + t L)[im T]. The derivative is that of Federer 2.9.22 in
    Hom(R^n, R^n) with the norm of Allard 2.2. The membership
    T'(0) ∈ Tan_T G(n, d) is [ddg_tangent_direction_tangent] in
    DdgGrassmannTangent.v. Direct formalisation. *)
Theorem ddg_lemma_A_1 (T L : Hom Rn Rn) (P : R -> Hom Rn Rn) :
  G T ->
  (exists2 delta : R, 0 < delta &
    forall t, `|t| < delta -> is_ddg_plane_projection d (idn + t *: L) T (P t)) ->
  has_normed_curve_derivative NH P 0 (ddg_tangent_direction T L).
Proof.
move=> hT [delta hdelta hP].
have hP0 : P 0 = T.
  apply: (ddg_plane_zero (L := L) hT); apply: hP; by rewrite normr0.
set c := NH L.
have hc0 : 0 <= c := ddg_hom_norm_nonnegative L.
set K := Num.sqrt n%:R * (15 * c ^+ 2).
have hK0 : 0 <= K by rewrite mulr_ge0 ?sqrtr_ge0 // mulr_ge0 // exprn_ge0.
move=> e he.
pose r := Num.min delta (Num.min (1 / (2 * (c + 1))) (e / (K + 1))).
have hc1 : 0 < c + 1 by lra.
have hK1 : 0 < K + 1 by lra.
have hr : 0 < r by rewrite !lt_min hdelta !divr_gt0 // mulr_gt0.
exists r; split=> // h /andP [hh0 hhr].
have hh : h != 0 by rewrite -normr_gt0.
have hr1 : `|h| < delta by apply: (lt_le_trans hhr); rewrite ge_min lexx.
have hr2 : `|h| < 1 / (2 * (c + 1)).
  by apply: (lt_le_trans hhr); rewrite !ge_min lexx orbT.
have hr3 : `|h| < e / (K + 1).
  by apply: (lt_le_trans hhr); rewrite !ge_min lexx !orbT.
have hsmall : c * `|h| <= 1 / 2.
  have h1 : (c + 1) * `|h| <= (c + 1) * (1 / (2 * (c + 1))).
    by rewrite ler_wpM2l ?ltW.
  have h2 : (c + 1) * (1 / (2 * (c + 1))) = 1 / 2 by field; rewrite gt_eqF.
  have h3 : c * `|h| <= (c + 1) * `|h| by rewrite ler_wpM2r //; lra.
  by rewrite -h2; exact: le_trans h3 h1.
rewrite add0r hP0.
have hq := ddg_quotient_estimate hT (hP h hr1) hsmall hh.
apply: (le_lt_trans hq).
have he1 : Num.sqrt n%:R * (15 * (c ^+ 2 * `|h|)) = K * `|h| by rewrite /K; ring.
rewrite he1.
have h1 : K * `|h| <= (K + 1) * `|h| by rewrite ler_wpM2r //; lra.
have h2 : (K + 1) * `|h| < (K + 1) * (e / (K + 1)) by rewrite ltr_pM2l.
have h3 : (K + 1) * (e / (K + 1)) = e by field; rewrite gt_eqF.
by rewrite -h3; exact: le_lt_trans h1 h2.
Qed.

(** Source for [ddg_lemma_A_1_moving_plane]: DDG Lemma A.1, p. 1143, for
    the curve T(t) of the projection formula, blueprint new:projformula
    and ddg:A.lemma1. Direct formalisation. *)
Theorem ddg_lemma_A_1_moving_plane (T L : Hom Rn Rn) :
  G T -> has_normed_curve_derivative NH (ddg_moving_plane L T) 0 (ddg_tangent_direction T L).
Proof.
move=> hT; apply: ddg_lemma_A_1=> //.
exists (1 / (NH L + 1)).
  by rewrite divr_gt0 // ltr_pwDr // ddg_hom_norm_nonnegative.
move=> t ht; apply: ddg_moving_planeP=> //.
have hc0 := ddg_hom_norm_nonnegative L.
have h1 : NH L * `|t| <= (NH L + 1) * `|t| by rewrite ler_wpM2r //; lra.
have h2 : (NH L + 1) * `|t| < (NH L + 1) * (1 / (NH L + 1)).
  by rewrite ltr_pM2l //; lra.
have h3 : (NH L + 1) * (1 / (NH L + 1)) = 1 by field; rewrite gt_eqF //; lra.
by rewrite -h3; exact: le_lt_trans h1 h2.
Qed.
End LemmaA1.
