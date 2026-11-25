(** De Philippis, De Rosa and Ghiraldin (2018), Appendix A, Lemma A.1,
    p. 1143; blueprint new:projformula (item A.3 of the blueprint). For
    T ∈ G(n, d), L ∈ Hom(R^n, R^n) and t ∈ R, DDG let T(t) ∈ G(n, d) be
    the orthogonal projection onto (1_{R^n} + t L)[im T]. The predicate
    [is_ddg_plane_projection] expresses that P ∈ G(n, d) is the orthogonal
    projection onto M[im T]. The projection formula of Allard's
    AllardProjectionFormula.v, P = J ∘ Q^{-1} ∘ J^* with J = M ∘ T and
    Q = J^* ∘ J + T^⊥, supplies such P whenever M | im T is univalent, in
    particular for M = 1_{R^n} + t L and |t| |L| < 1
    ([ddg_moving_planeP]). The principal estimate of this file is

        |(P - T)(v)| ≤ 3 |t| |L| |v|   whenever |t| |L| ≤ 1/2
                                        ([ddg_plane_estimate]),

    from which Lemma A.1 is derived in DdgLemmaA1.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals ring lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities
  LinearBasis Bilinear TensorUP Hom HomInner HomInnerCoordinates AdjointUP AdjointLaws Adjoint
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates EuclideanRectangularAdjoint
  TraceDefinition TraceCyclic HilbertFormCompactness RealNormUP.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardProjectionFormula.
From DPDRG Require Import DdgLinearAlgebra DdgGrassmann.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section MovingPlane.
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

(** Source for [is_ddg_plane_projection]: DDG Lemma A.1, p. 1143: "T(t) ∈
    G(n, d) the orthogonal projection onto (Id + tL)(T)"; blueprint
    new:projformula. The member P of G(n, d) is the orthogonal projection
    onto M[im T], that is, im P = M[im T]. Definition. *)
Definition is_ddg_plane_projection (M T P : Hom Rn Rn) :=
  G P /\ forall y, (exists z, P z = y) <-> (exists x, M (T x) = y).

(** Source for [ddg_moving_plane]: DDG Lemma A.1, p. 1143, and blueprint
    new:projformula: T(t) = J_t ∘ Q_t^{-1} ∘ J_t^* with J_t = (1 + t L) ∘ T
    and Q_t = J_t^* ∘ J_t + T^⊥, the projection formula of Allard's
    [projection_formula_map] for (1 + t L, T), whenever Q_t is univalent.
    For the remaining t, which play no role, the value is T. Definition. *)
Definition ddg_moving_plane (L T : Hom Rn Rn) (t : R) : Hom Rn Rn :=
  match pselect (injective (projection_formula_operator (idn + t *: L) T)) with
  | left hA => projection_formula_map hA
  | right _ => T
  end.

(** Source for [ddg_curve_apply]: (1_{R^n} + t L)(x) = x + t L(x).
    Supporting lemma. *)
Lemma ddg_curve_apply (L : Hom Rn Rn) (t : R) x : (idn + t *: L) x = x + t *: L x.
Proof. by rewrite hom_addE hom_scaleE ddg_hom_idE. Qed.

(** Source for [ddg_curve_injective]: blueprint new:projformula and
    new:flow: if |t| |L| < 1, then 1_{R^n} + t L is univalent, because
    |x + t L(x)| ≥ (1 - |t| |L|) |x|. Supporting lemma. *)
Lemma ddg_curve_injective (L : Hom Rn Rn) (t : R) x :
  NH L * `|t| < 1 -> (idn + t *: L) x = 0 -> x = 0.
Proof.
move=> hs; rewrite ddg_curve_apply=> hx.
have hx' : x = - (t *: L x) by apply/eqP; rewrite -addr_eq0 hx.
have hb : Nn x <= `|t| * (NH L * Nn x).
  rewrite {1}hx' inner_normN inner_normZ ler_wpM2l //; exact: ddg_hom_vector_bound.
have hnn := inner_norm_nonnegative hBn x.
have h0 : Nn x <= 0.
  have hm : `|t| * (NH L * Nn x) = (NH L * `|t|) * Nn x by ring.
  rewrite hm in hb.
  have h1 : (1 - NH L * `|t|) * Nn x <= 0 by rewrite mulrBl mul1r subr_le0.
  have h2 : 0 < 1 - NH L * `|t| by rewrite subr_gt0.
  by rewrite pmulr_rle0 in h1.
by apply/eqP; rewrite -(inner_norm_eq0 hBn) eq_le h0 hnn.
Qed.

(** Source for [ddg_moving_planeP]: blueprint new:projformula: if
    |t| |L| < 1, then T(t) = [[ddg_moving_plane L T t]] is the
    orthogonal projection onto (1_{R^n} + t L)[im T] and belongs to
    G(n, d); by Allard's [projection_formula_orthogonal_projector] and
    [projection_formula_map_image]. Direct formalisation. *)
Theorem ddg_moving_planeP (L T : Hom Rn Rn) (t : R) :
  G T -> NH L * `|t| < 1 -> is_ddg_plane_projection (idn + t *: L) T (ddg_moving_plane L T t).
Proof.
move=> hT hs.
have hidem := orthogonal_projector_idempotent hT.
have hsym := orthogonal_projector_symmetric hT.
have hinj : injective (projection_formula_operator (idn + t *: L) T).
  apply/(projection_formula_operator_injective (idn + t *: L) hidem hsym)=> x _ hx.
  exact: ddg_curve_injective hs hx.
rewrite /ddg_moving_plane; case: pselect=> [hA|hA]; last by exfalso; exact: hA hinj.
split; first exact: (projection_formula_orthogonal_projector hT hA).
exact: (projection_formula_map_image hA hidem).
Qed.

Section Estimate.
Variables T L P : Hom Rn Rn.
Variable t : R.
Hypothesis hT : G T.
Hypothesis hP : is_ddg_plane_projection (idn + t *: L) T P.
Hypothesis hsmall : NH L * `|t| <= 1 / 2.
Local Notation c := (NH L).

(** Source for [ddg_plane_member]: P ∈ G(n, d). Supporting lemma. *)
Lemma ddg_plane_member : G P.
Proof. exact: hP.1. Qed.

(** Source for [ddg_plane_fixed]: DDG proof of Lemma A.1, p. 1143:
    "T(t) ∘ (Id + tL) ∘ T = (Id + tL) ∘ T", pointwise. Direct
    formalisation. *)
Lemma ddg_plane_fixed x : P (T x + t *: L (T x)) = T x + t *: L (T x).
Proof.
apply: (ddg_projector_fixed ddg_plane_member); apply/hP.2.
by exists x; rewrite ddg_curve_apply.
Qed.

(** Source for [ddg_plane_perp_T]: DDG (A.3), p. 1143, pointwise:
    P^⊥(T(x)) = - t P^⊥(L(T(x))). Supporting lemma. *)
Lemma ddg_plane_perp_T x : ddg_perp P (T x) = - (t *: ddg_perp P (L (T x))).
Proof.
have h : ddg_perp P (T x + t *: L (T x)) = 0 by rewrite ddg_perpE ddg_plane_fixed subrr.
apply/eqP; rewrite -addr_eq0; apply/eqP.
by rewrite -ddg_homZ -ddg_homD.
Qed.

(** Source for [ddg_plane_perp_T_bound]: |P^⊥(T(x))| ≤ |t| |L| |x|.
    Supporting lemma. *)
Lemma ddg_plane_perp_T_bound x : Nn (ddg_perp P (T x)) <= `|t| * c * Nn x.
Proof.
rewrite ddg_plane_perp_T inner_normN inner_normZ -mulrA ler_wpM2l //.
apply: (le_trans (ddg_perp_contraction ddg_plane_member _)).
apply: (le_trans (ddg_hom_vector_bound L (T x))).
rewrite ler_wpM2l ?ddg_hom_norm_nonnegative //.
exact: ddg_projector_contraction hT x.
Qed.

(** Source for [ddg_plane_Tperp_P_bound]: blueprint new:projformula:
    |T^⊥(P(w))| ≤ 2 |t| |L| |w|. If P(w) = T(x) + t L(T(x)), then
    T^⊥(P(w)) = t T^⊥(L(T(x))) and |T(x)| ≤ |P(w)| + |t| |L| |T(x)|.
    Supporting lemma. *)
Lemma ddg_plane_Tperp_P_bound w : Nn (ddg_perp T (P w)) <= 2 * (`|t| * c) * Nn w.
Proof.
have [x hx] : exists x, (idn + t *: L) (T x) = P w by apply/hP.2; exists w.
rewrite ddg_curve_apply in hx.
have hc0 : 0 <= c := ddg_hom_norm_nonnegative L.
have hLT : Nn (L (T x)) <= c * Nn (T x) := ddg_hom_vector_bound L (T x).
have hTx : Nn (T x) <= 2 * Nn (P w).
  have he : T x = P w - t *: L (T x) by rewrite -hx addrK.
  have h1 : Nn (T x) <= Nn (P w) + `|t| * (c * Nn (T x)).
    rewrite {1}he; apply: (le_trans (ddg_vector_norm_sub _ _)).
    by rewrite inner_normZ lerD2l ler_wpM2l.
  have hm : `|t| * (c * Nn (T x)) = (c * `|t|) * Nn (T x) by ring.
  rewrite hm in h1.
  have h2 : (c * `|t|) * Nn (T x) <= (1 / 2) * Nn (T x).
    by rewrite ler_wpM2r // inner_norm_nonnegative.
  lra.
have hPw : Nn (P w) <= Nn w := ddg_projector_contraction ddg_plane_member w.
have hval : ddg_perp T (P w) = t *: ddg_perp T (L (T x)).
  by rewrite -hx ddg_homD (ddg_proj_perp hT) add0r ddg_homZ.
rewrite hval inner_normZ.
apply: (le_trans (y := `|t| * (c * (2 * Nn w)))); last by rewrite (_ : forall a b e f : R,
  a * (b * (e * f)) = e * (a * b) * f) // => a b e f; ring.
rewrite ler_wpM2l //.
apply: (le_trans (ddg_perp_contraction hT _)); apply: (le_trans hLT).
rewrite ler_wpM2l //; apply: (le_trans hTx).
by rewrite ler_wpM2l.
Qed.

(** Source for [ddg_plane_P_Tperp_bound]: blueprint new:projformula:
    |P(T^⊥(v))| ≤ 2 |t| |L| |v|. With u = P(T^⊥(v)) one has
    |u|^2 = T^⊥(v) • u = v • T^⊥(P(u)) ≤ |v| 2 |t| |L| |u|. Supporting
    lemma. *)
Lemma ddg_plane_P_Tperp_bound v : Nn (P (ddg_perp T v)) <= 2 * (`|t| * c) * Nn v.
Proof.
set u := P (ddg_perp T v).
have hPu : P u = u by rewrite /u (ddg_projector_idem ddg_plane_member).
have hc0 : 0 <= c := ddg_hom_norm_nonnegative L.
apply: ddg_vector_bound_by_pairing.
  by rewrite mulr_ge0 ?inner_norm_nonnegative // mulr_ge0 // mulr_ge0.
have he : Bn u u = Bn v (ddg_perp T (P u)).
  by rewrite {1}/u (ddg_projector_sym ddg_plane_member) hPu (ddg_perp_sym hT).
rewrite he hPu.
apply: (le_trans (ler_norm _)); apply: (le_trans (ddg_vector_cauchy _ _)).
have h1 := ddg_plane_Tperp_P_bound u; rewrite hPu in h1.
have h2 : Nn v * Nn (ddg_perp T u) <= Nn v * (2 * (`|t| * c) * Nn u).
  by rewrite ler_wpM2l // inner_norm_nonnegative.
apply: (le_trans h2); rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

(** Source for [ddg_plane_difference]: blueprint new:projformula:
    (P - T)(v) = P(T^⊥(v)) - P^⊥(T(v)). Supporting lemma. *)
Lemma ddg_plane_difference v : (P - T) v = P (ddg_perp T v) - ddg_perp P (T v).
Proof.
rewrite ddg_hom_subE !ddg_perpE ddg_homB.
by rewrite opprB addrA subrK.
Qed.

(** Source for [ddg_plane_estimate]: blueprint new:projformula:
    |(P - T)(v)| ≤ 3 |t| |L| |v| whenever |t| |L| ≤ 1/2. Supporting
    lemma for DDG Lemma A.1. *)
Theorem ddg_plane_estimate v : Nn ((P - T) v) <= 3 * (`|t| * c) * Nn v.
Proof.
rewrite ddg_plane_difference.
apply: (le_trans (ddg_vector_norm_sub _ _)).
have h1 := ddg_plane_P_Tperp_bound v.
have h2 := ddg_plane_perp_T_bound v.
have he : 3 * (`|t| * c) * Nn v = 2 * (`|t| * c) * Nn v + `|t| * c * Nn v by ring.
by rewrite he lerD.
Qed.

(** Source for [ddg_plane_hom_estimate]: blueprint new:projformula:
    |P - T| ≤ 3 n^{1/2} |t| |L| for the norm of Allard 2.2. Supporting
    lemma. *)
Theorem ddg_plane_hom_estimate : NH (P - T) <= Num.sqrt n%:R * (3 * (`|t| * c)).
Proof.
apply: ddg_hom_norm_from_vector_bound; last exact: ddg_plane_estimate.
by rewrite mulr_ge0 // mulr_ge0 // ddg_hom_norm_nonnegative.
Qed.
End Estimate.

(** Source for [ddg_plane_zero]: the orthogonal projection onto im T is
    T: if P ∈ G(n, d) and im P = im T, then P = T. Supporting lemma,
    obtained from [ddg_plane_estimate] with t = 0. *)
Lemma ddg_plane_zero (L T P : Hom Rn Rn) :
  G T -> is_ddg_plane_projection (idn + 0 *: L) T P -> P = T.
Proof.
move=> hT hP.
have hs : NH L * `|0 : R| <= 1 / 2 by rewrite normr0 mulr0 divr_ge0.
have h := ddg_plane_hom_estimate hT hP hs.
rewrite normr0 mul0r mulr0 mulr0 in h.
by apply/eqP; rewrite -subr_eq0; apply/eqP; exact: ddg_hom_norm_eq0.
Qed.
End MovingPlane.
