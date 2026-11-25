(** De Philippis, De Rosa and Ghiraldin (2018), proof of Lemma A.2,
    p. 1144; blueprint new:BFderiv and ddg:A.2const: the uniform estimate
    which permits differentiation under the integral sign. For T ∈ G(n, d),
    L ∈ Hom(R^n, R^n) and |t| |L| ≤ 1/2,

        (1 - |t| |L|)^d ≤ ‖∧_d((1 + t L) ∘ T)‖ ≤ (1 + |t| |L|)^d,

    hence | ‖∧_d((1 + t L) ∘ T)‖ - 1 | ≤ 2^d |t| |L|. If F is Lipschitz with
    constant Λ and bounded by Φ on G(n, d), and P is the orthogonal
    projection onto (1 + t L)[im T], then

        | F(P) ‖∧_d((1 + t L) ∘ T)‖ - F(T) | ≤ 2^d (3 n^{1/2} Λ + Φ) |t| |L|.

    The Jacobian is that of Federer 3.2.1, p. 241. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology ring lra.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities LinearBasis TensorUP
  Hom GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates HilbertFormCompactness
  HomInner EuclideanLinearJacobian EuclideanExteriorComposition EuclideanSmallLinearInverse.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann.
From DPDRG Require Import DdgLinearAlgebra DdgGrassmann DdgMovingPlane DdgWeightedJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [ddg_power_le]: 0 ≤ a ≤ b implies a^k ≤ b^k.
    Supporting lemma. *)
Lemma ddg_power_le (R : realType) (a b : R) (k : nat) : 0 <= a -> a <= b -> a ^+ k <= b ^+ k.
Proof.
move=> ha hab; elim: k=> [|k ih]; first by rewrite !expr0.
rewrite !exprS; apply: ler_pM=> //; exact: exprn_ge0.
Qed.

(** Source for [ddg_power_lower]: Bernoulli's inequality
    1 - k c ≤ (1 - c)^k for 0 ≤ c ≤ 1. Supporting lemma. *)
Lemma ddg_power_lower (R : realType) (c : R) (k : nat) :
  0 <= c -> c <= 1 -> 1 - k%:R * c <= (1 - c) ^+ k.
Proof.
move=> hc0 hc1; elim: k=> [|k ih]; first by rewrite expr0 mulr0n mul0r subr0.
have h1 : 0 <= 1 - c by lra.
rewrite exprSr; apply: (le_trans _ (ler_wpM2r h1 ih)).
have hk : 0 <= k%:R * c * c :> R by rewrite mulr_ge0 // mulr_ge0.
rewrite -natr1; nra.
Qed.

(** Source for [ddg_power_upper]: (1 + c)^k ≤ 1 + (2^k - 1) c for
    0 ≤ c ≤ 1. Supporting lemma. *)
Lemma ddg_power_upper (R : realType) (c : R) (k : nat) :
  0 <= c -> c <= 1 -> (1 + c) ^+ k <= 1 + (2 ^+ k - 1) * c.
Proof.
move=> hc0 hc1; elim: k=> [|k ih]; first by rewrite !expr0 subrr mul0r addr0.
have h1 : 0 <= 1 + c by lra.
rewrite [(1 + c) ^+ _]exprSr; apply: (le_trans (ler_wpM2r h1 ih)).
have h2 : 1 <= 2 ^+ k :> R by apply: exprn_ege1; lra.
have h3 : (2 ^+ k - 1) * (c * c) <= (2 ^+ k - 1) * c.
  by apply: ler_wpM2l; [lra|nra].
rewrite [2 ^+ k.+1]exprSr; nra.
Qed.

(** Source for [ddg_two_power]: k ≤ 2^k. Supporting lemma. *)
Lemma ddg_two_power (R : realType) (k : nat) : k%:R <= 2 ^+ k :> R.
Proof.
elim: k=> [|k ih]; first by rewrite expr0 mulr0n ler01.
have h : 1 <= 2 ^+ k :> R by apply: exprn_ege1; lra.
rewrite exprS -natr1; lra.
Qed.

Section WeightedJacobianEstimate.
Variable R : realType.
Variables n d : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation Nn := (inner_norm hBn).
Local Notation NH := (hom_norm hBn hBn hbn).
Local Notation idn := (hom_of_linear (linear_id Rn)).
Local Notation G := (orthogonal_projectors R n d).
Local Notation J := (euclidean_linear_jacobian d).

(** Source for [ddg_curve_vector_bound]: |(1 + t L)(x)| ≤ (1 + |t| |L|) |x|.
    Supporting lemma. *)
Lemma ddg_curve_vector_bound (L : Hom Rn Rn) (t : R) (x : Rn) :
  Nn ((idn + t *: L) x) <= (1 + `|t| * NH L) * Nn x.
Proof.
rewrite ddg_curve_apply mulrDl mul1r -mulrA.
apply: (le_trans (ddg_vector_norm_triangle _ _)); rewrite lerD2l inner_normZ.
exact: (ler_wpM2l (normr_ge0 t) (ddg_hom_vector_bound L x)).
Qed.

(** Source for [ddg_jacobian_upper]: Federer 1.7.6, pp. 33–34, and
    3.2.1, p. 241: ‖∧_d((1 + t L) ∘ T)‖ ≤ ‖∧_d(1 + t L)‖ ‖∧_d T‖
    ≤ (1 + |t| |L|)^d for T ∈ G(n, d). Supporting lemma. *)
Lemma ddg_jacobian_upper (T L : Hom Rn Rn) (t : R) :
  G T -> J (hom_comp (idn + t *: L) T) <= (1 + `|t| * NH L) ^+ d.
Proof.
move=> hT.
apply: (le_trans (euclidean_exterior_jacobian_compose_bound d T (idn + t *: L))).
rewrite (ddg_jacobian_projection hT) mulr1.
apply: euclidean_exterior_jacobian_vector_bound_power; last exact: ddg_curve_vector_bound.
by rewrite addr_ge0 // mulr_ge0 // ddg_hom_norm_nonnegative.
Qed.

(** Source for [ddg_jacobian_lower]: Federer 1.7.6, pp. 33–34, 3.1.23,
    p. 237, and 3.2.1, p. 241: if c = |t| |L| < 1, then 1 + t L has an
    inverse E with |E(w)| ≤ (1 - c)^{-1} |w|, T = E ∘ (1 + t L) ∘ T, hence
    1 = ‖∧_d T‖ ≤ (1 - c)^{-d} ‖∧_d((1 + t L) ∘ T)‖. Supporting lemma. *)
Lemma ddg_jacobian_lower (T L : Hom Rn Rn) (t : R) :
  G T -> `|t| * NH L < 1 -> (1 - `|t| * NH L) ^+ d <= J (hom_comp (idn + t *: L) T).
Proof.
move=> hT; set c := `|t| * NH L; move=> hc.
have hc0 : 0 <= c by rewrite mulr_ge0 // ddg_hom_norm_nonnegative.
have hD v : Nn ((idn + t *: L) v - v) <= c * Nn v.
  rewrite ddg_curve_apply addrAC subrr add0r inner_normZ -mulrA.
  exact: (ler_wpM2l (normr_ge0 t) (ddg_hom_vector_bound L v)).
have [E [_ [hDE hED]]] := euclidean_small_linear_inverse hc hD.
have h1c : 0 < 1 - c by lra.
have hEb w : Nn (E w) <= (1 - c)^-1 * Nn w.
  have e : E w = (idn + t *: L) (E w) - ((idn + t *: L) (E w) - E w).
    by rewrite opprB addrC subrK.
  have h := ddg_vector_norm_sub ((idn + t *: L) (E w)) ((idn + t *: L) (E w) - E w).
  rewrite -e hED in h.
  have h2 := hD (E w); rewrite hED in h2.
  have h3 : Nn (E w) <= Nn w + c * Nn (E w).
    by apply: (le_trans h); rewrite lerD2l; exact: h2.
  have h4 : (1 - c) * Nn (E w) <= Nn w by nra.
  have hi : 0 < (1 - c)^-1 by rewrite invr_gt0.
  have h5 := ler_wpM2l (ltW hi) h4.
  by rewrite mulrA mulVf ?mul1r // in h5; exact: lt0r_neq0.
have hTE : T = hom_comp E (hom_comp (idn + t *: L) T).
  by apply: hom_ext=> x; rewrite !hom_compE hDE.
have h1 : 1 <= J E * J (hom_comp (idn + t *: L) T).
  rewrite -(ddg_jacobian_projection hT) {1}hTE.
  exact: euclidean_exterior_jacobian_compose_bound.
have h2 : J E <= ((1 - c)^-1) ^+ d.
  apply: euclidean_exterior_jacobian_vector_bound_power; last exact: hEb.
  by rewrite invr_ge0 ltW.
have hJ0 := euclidean_linear_jacobian_nonnegative d (hom_comp (idn + t *: L) T).
have h3 : 1 <= ((1 - c)^-1) ^+ d * J (hom_comp (idn + t *: L) T).
  exact: (le_trans h1 (ler_wpM2r hJ0 h2)).
have hp : 0 < (1 - c) ^+ d := exprn_gt0 d h1c.
have h4 := ler_wpM2l (ltW hp) h3.
have hu : (1 - c) * (1 - c)^-1 = 1 by rewrite mulfV // lt0r_neq0.
by rewrite mulr1 mulrA -exprMn hu expr1n mul1r in h4.
Qed.

(** Source for [ddg_jacobian_bound]: ‖∧_d((1 + t L) ∘ T)‖ ≤ 2^d for
    T ∈ G(n, d) and |t| |L| ≤ 1/2. Supporting lemma. *)
Lemma ddg_jacobian_bound (T L : Hom Rn Rn) (t : R) :
  G T -> NH L * `|t| <= 1 / 2 -> J (hom_comp (idn + t *: L) T) <= 2 ^+ d.
Proof.
move=> hT hs.
apply: (le_trans (@ddg_jacobian_upper T L t hT)); apply: ddg_power_le.
  by rewrite addr_ge0 // mulr_ge0 // ddg_hom_norm_nonnegative.
lra.
Qed.

(** Source for [ddg_jacobian_estimate]: proof of DDG Lemma A.2, p. 1144:
    | ‖∧_d((1 + t L) ∘ T)‖ - 1 | ≤ 2^d |t| |L| for T ∈ G(n, d) and
    |t| |L| ≤ 1/2. Supporting lemma. *)
Lemma ddg_jacobian_estimate (T L : Hom Rn Rn) (t : R) :
  G T -> NH L * `|t| <= 1 / 2 -> `|J (hom_comp (idn + t *: L) T) - 1| <= 2 ^+ d * (`|t| * NH L).
Proof.
move=> hT hs.
have hc0 : 0 <= `|t| * NH L by rewrite mulr_ge0 // ddg_hom_norm_nonnegative.
have hc1 : `|t| * NH L <= 1 by lra.
have hlt : `|t| * NH L < 1 by lra.
have hup := le_trans (@ddg_jacobian_upper T L t hT) (@ddg_power_upper R _ d hc0 hc1).
have hlo := le_trans (@ddg_power_lower R _ d hc0 hc1) (ddg_jacobian_lower hT hlt).
have hd := @ddg_two_power R d.
have hdc : d%:R * (`|t| * NH L) <= 2 ^+ d * (`|t| * NH L) by rewrite ler_wpM2r.
rewrite mulrBl mul1r in hup.
by rewrite ler_norml; apply/andP; split; lra.
Qed.

(** Source for [ddg_weighted_jacobian_estimate]: proof of DDG Lemma A.2,
    p. 1144, with the estimate of new:projformula: if Λ ≥ 0,
    |F(S) - F(S')| ≤ Λ |S - S'| and |F(S)| ≤ Φ for S, S' ∈ G(n, d),
    T ∈ G(n, d), P is the orthogonal projection onto (1 + t L)[im T] and
    |t| |L| ≤ 1/2, then
    |F(P) ‖∧_d((1 + t L) ∘ T)‖ - F(T)| ≤ 2^d (3 n^{1/2} Λ + Φ) |t| |L|.
    Direct formalisation. *)
Theorem ddg_weighted_jacobian_estimate (F : Hom Rn Rn -> R) (Lam Phi : R) (T L P : Hom Rn Rn)
    (t : R) :
  0 <= Lam ->
  (forall S S', G S -> G S' -> `|F S - F S'| <= Lam * NH (S - S')) ->
  (forall S, G S -> `|F S| <= Phi) ->
  G T -> is_ddg_plane_projection d (idn + t *: L) T P -> NH L * `|t| <= 1 / 2 ->
  `|F P * J (hom_comp (idn + t *: L) T) - F T| <=
    2 ^+ d * (3 * Num.sqrt n%:R * Lam + Phi) * (`|t| * NH L).
Proof.
move=> hL hFL hFb hT hP hs.
set c := `|t| * NH L.
set j := J (hom_comp (idn + t *: L) T).
have hj0 : 0 <= j := euclidean_linear_jacobian_nonnegative d _.
have hj2 : j <= 2 ^+ d := ddg_jacobian_bound hT hs.
have hj1 : `|j - 1| <= 2 ^+ d * c := ddg_jacobian_estimate hT hs.
have hFP : `|F P - F T| <= Lam * (Num.sqrt n%:R * (3 * c)).
  apply: (le_trans (hFL P T (ddg_plane_member hP) hT)).
  by rewrite ler_wpM2l //; exact: (ddg_plane_hom_estimate hT hP hs).
have hFT := hFb T hT.
have e : F P * j - F T = (F P - F T) * j + F T * (j - 1) by ring.
rewrite e; apply: (le_trans (ler_normD _ _)); rewrite !normrM (ger0_norm hj0).
have h3 : `|F P - F T| * j <= Lam * (Num.sqrt n%:R * (3 * c)) * 2 ^+ d.
  exact: (ler_pM (normr_ge0 _) hj0 hFP hj2).
have h4 : `|F T| * `|j - 1| <= Phi * (2 ^+ d * c).
  exact: (ler_pM (normr_ge0 _) (normr_ge0 _) hFT hj1).
apply: (le_trans (lerD h3 h4)); rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

End WeightedJacobianEstimate.
