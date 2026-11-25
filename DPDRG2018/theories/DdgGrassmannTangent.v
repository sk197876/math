(** De Philippis, De Rosa and Ghiraldin (2018), Appendix A, (A.2) and the
    following display, p. 1143; blueprint ddg:A.tan (item A.4 of the
    blueprint), tangent part, and the membership assertion of Lemma A.1.
    For T ∈ G(n, d) the tangent cone of Federer 3.1.21 of G(n, d) at T,
    taken in Hom(R^n, R^n) with the norm of Allard 2.2, is

        Tan(G(n, d), T) = SymEnd(R^n) ∩ {A : T ∘ A ∘ T = 0, T^⊥ ∘ A ∘ T^⊥ = 0}
                        = SymEnd(R^n) ∩ {A : A = A ∘ T + T ∘ A}
                        = {X + X^* : X ∈ H_T},

    where H_T = {X : X = T^⊥ ∘ X ∘ T}. DDG derive the inclusion ⊂ by
    differentiating the conditions of (A.1) along curves and the equality
    from a dimension count. Here the inclusion ⊂ is obtained from the
    definition of the tangent cone, and the inclusion ⊃ from Lemma A.1:
    for X ∈ H_T the moving plane T(t) of X has T'(0) = X + X^*. The
    submanifold structure and the dimension d(n - d) are not formalised;
    see docs/divergences.md. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals ring lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities
  LinearBasis Bilinear TensorUP Hom HomInner HomInnerCoordinates AdjointUP AdjointLaws Adjoint
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates EuclideanRectangularAdjoint
  TraceDefinition TraceCyclic HilbertFormCompactness RealNormUP NormedCurveDerivativeUP
  TangentConeUP.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardProjectionFormula.
From DPDRG Require Import DdgLinearAlgebra DdgGrassmann DdgMovingPlane DdgLemmaA1.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ddg_curve_tangent_cone]: Federer 3.1.21, p. 233, and
    2.9.22, p. 167: if g(t) ∈ S for 0 < t < δ, g(0) = a and g'(0) = v,
    then v ∈ Tan(S, a). This is the opening step of DDG (A.2), p. 1143.
    Supporting lemma. *)
Lemma ddg_curve_tangent_cone (R : realType) (X : lmodType R) (N : X -> R)
    (hN : is_real_norm N) (S : set X) (g : R -> X) (a v : X) :
  (exists2 delta : R, 0 < delta & forall t, 0 < t -> t < delta -> S (g t)) ->
  g 0 = a -> has_normed_curve_derivative N g 0 v -> norm_tangent_cone N S a v.
Proof.
move=> [delta hdelta hS] hg0 hg e he.
have [r [hr hlim]] := hg e he.
have hN0 : 0 <= N v := real_seminorm_nonnegative hN.1 v.
have hNe : 0 < N v + e by lra.
pose h := Num.min delta (Num.min r (e / (N v + e))) / 2.
have hm : 0 < Num.min delta (Num.min r (e / (N v + e))).
  by rewrite !lt_min hdelta hr divr_gt0.
have hh : 0 < h by rewrite /h divr_gt0.
have hlt : h < Num.min delta (Num.min r (e / (N v + e))) by rewrite /h; lra.
have h1 : h < delta by apply: (lt_le_trans hlt); rewrite ge_min lexx.
have h2 : h < r by apply: (lt_le_trans hlt); rewrite !ge_min lexx orbT.
have h3 : h < e / (N v + e) by apply: (lt_le_trans hlt); rewrite !ge_min lexx !orbT.
have habs : `|h| = h := gtr0_norm hh.
have hq : N (h^-1 *: (g (0 + h) - g 0) - v) < e.
  by apply: hlim; rewrite habs hh h2.
rewrite add0r hg0 in hq.
exists (g h), h^-1; split; first exact: hS.
split; first by rewrite invr_gt0.
split; last exact: hq.
have hx : g h - a = h *: (h^-1 *: (g h - a)) by rewrite scalerA mulfV ?gt_eqF // scale1r.
rewrite hx (real_seminorm_scale hN.1) habs.
have hb : N (h^-1 *: (g h - a)) <= N v + e.
  have hs : h^-1 *: (g h - a) = (h^-1 *: (g h - a) - v) + v by rewrite subrK.
  rewrite hs; apply: (le_trans (real_seminorm_triangle hN.1 _ _)).
  by rewrite addrC lerD2l ltW.
have h4 : h * N (h^-1 *: (g h - a)) <= h * (N v + e) by rewrite ler_wpM2l // ltW.
apply: (le_lt_trans h4).
have h5 : h * (N v + e) < e / (N v + e) * (N v + e) by rewrite ltr_pM2r.
apply: (lt_le_trans h5).
by rewrite divfK ?gt_eqF.
Qed.

(** Source for [ddg_sub_cancel]: (a - b) - (c - b) = a - c in an abelian
    group. Supporting lemma. *)
Lemma ddg_sub_cancel (V : zmodType) (a b c : V) : (a - b) - (c - b) = a - c.
Proof. by rewrite opprB addrA subrK. Qed.

(** Source for [ddg_subrACA]: (x - y) - (z - t) = (x - z) - (y - t) in an
    abelian group. Supporting lemma. *)
Lemma ddg_subrACA (V : zmodType) (x y z t : V) : (x - y) - (z - t) = (x - z) - (y - t).
Proof. by rewrite !opprB addrACA [RHS]addrACA [- z + _]addrC. Qed.

(** Source for [ddg_sub_three]: an identity in an abelian group used in
    [ddg_cone_derivation]. Supporting lemma. *)
Lemma ddg_sub_three (V : zmodType) (a c f p q s : V) :
  (a - p) - (c - q) - (f - s) + (p - q - s) = a - c - f.
Proof. by rewrite (@ddg_subrACA _ a p c q) (@ddg_subrACA _ (a - c) (p - q) f s) subrK. Qed.

Section Tangent.
Variable R : realType.
Variables n d : nat.
Local Notation Rn := (R_n R n).
Local Notation Bn := (@euclidean_inner_product R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation Nn := (inner_norm hBn).
Local Notation NH := (hom_norm hBn hBn hbn).
Local Notation hNH := (inner_norm_real_norm (hom_inner_productP hBn hBn hbn)).
Local Notation adjL L := (euclidean_rectangular_adjoint L).
Local Notation idn := (hom_of_linear (linear_id Rn)).
Local Notation G := (orthogonal_projectors R n d).
Local Notation Tan := (norm_tangent_cone NH G).

(** Source for [ddg_tangent_S1]: DDG p. 1143, display after (A.2):
    SymEnd(R^n) ∩ {A : T ∘ A ∘ T = 0, T^⊥ ∘ A ∘ T^⊥ = 0}; blueprint
    ddg:A.tan. Definition. *)
Definition ddg_tangent_S1 (T : Hom Rn Rn) : set (Hom Rn Rn) :=
  [set A | [/\ adjL A = A, hom_comp T (hom_comp A T) = 0 &
    hom_comp (ddg_perp T) (hom_comp A (ddg_perp T)) = 0]].

(** Source for [ddg_tangent_S2]: DDG (A.2), p. 1143:
    SymEnd(R^n) ∩ {A : A = A ∘ T + T ∘ A}; blueprint ddg:A.tan.
    Definition. *)
Definition ddg_tangent_S2 (T : Hom Rn Rn) : set (Hom Rn Rn) :=
  [set A | adjL A = A /\ A = hom_comp A T + hom_comp T A].

(** Source for [ddg_tangent_H]: blueprint ddg:A.tan:
    H_T = {X : X = T^⊥ ∘ X ∘ T}. Definition. *)
Definition ddg_tangent_H (T : Hom Rn Rn) : set (Hom Rn Rn) :=
  [set X | X = hom_comp (ddg_perp T) (hom_comp X T)].

(** Source for [ddg_tangent_S3]: blueprint ddg:A.tan:
    {X + X^* : X ∈ H_T}. Definition. *)
Definition ddg_tangent_S3 (T : Hom Rn Rn) : set (Hom Rn Rn) :=
  [set A | exists2 X, ddg_tangent_H T X & A = X + adjL X].

Section Member.
Variable T : Hom Rn Rn.
Hypothesis hT : G T.

(** Source for [ddg_perp_adjoint]: (T^⊥)^* = T^⊥. Supporting lemma. *)
Lemma ddg_perp_adjoint : adjL (ddg_perp T) = ddg_perp T.
Proof. by apply: ddg_adjoint_ext=> x y; exact: ddg_perp_sym hT x y. Qed.

(** Source for [ddg_tangent_direction_tangent]: DDG Lemma A.1, p. 1143:
    T^⊥ ∘ L ∘ T + (T^⊥ ∘ L ∘ T)^* ∈ Tan_T G(n, d), the tangent cone of
    Federer 3.1.21. The curve of [ddg_lemma_A_1_moving_plane] lies in
    G(n, d) for |t| |L| < 1. Direct formalisation. *)
Theorem ddg_tangent_direction_tangent (L : Hom Rn Rn) : Tan T (ddg_tangent_direction T L).
Proof.
apply: (ddg_curve_tangent_cone hNH (g := ddg_moving_plane L T)).
- exists (1 / (NH L + 1)).
    by rewrite divr_gt0 // ltr_pwDr // ddg_hom_norm_nonnegative.
  move=> t ht0 ht.
  have hc0 := ddg_hom_norm_nonnegative L.
  have hm : NH L * `|t| < 1.
    rewrite gtr0_norm //.
    have h1 : NH L * t <= (NH L + 1) * t by rewrite ler_wpM2r ?ltW //; lra.
    have h2 : (NH L + 1) * t < (NH L + 1) * (1 / (NH L + 1)).
      by rewrite ltr_pM2l //; lra.
    have h3 : (NH L + 1) * (1 / (NH L + 1)) = 1 by field; rewrite gt_eqF //; lra.
    by rewrite -h3; exact: le_lt_trans h1 h2.
  exact: (ddg_moving_planeP hT hm).1.
- apply: (ddg_plane_zero (L := L) hT).
  apply: ddg_moving_planeP=> //.
  by rewrite normr0 mulr0 ltr01.
- exact: (ddg_lemma_A_1_moving_plane L hT).
Qed.

(** Source for [ddg_tangent_H_S3]: blueprint ddg:A.tan: if X ∈ H_T, then
    X + X^* = T^⊥ ∘ X ∘ T + (T^⊥ ∘ X ∘ T)^*. Supporting lemma. *)
Lemma ddg_tangent_H_direction (X : Hom Rn Rn) :
  ddg_tangent_H T X -> X + adjL X = ddg_tangent_direction T X.
Proof. by move=> hX; rewrite /ddg_tangent_direction -hX. Qed.

(** Source for [ddg_tangent_S3_cone]: blueprint ddg:A.tan:
    {X + X^* : X ∈ H_T} ⊂ Tan(G(n, d), T), by Lemma A.1. Direct
    formalisation. *)
Theorem ddg_tangent_S3_cone : ddg_tangent_S3 T `<=` Tan T.
Proof.
move=> A [X hX ->]; rewrite (ddg_tangent_H_direction hX).
exact: ddg_tangent_direction_tangent.
Qed.

(** Source for [ddg_cone_symmetric]: DDG (A.2), p. 1143, second
    equality: A^* = A for A ∈ Tan(G(n, d), T). Supporting lemma. *)
Lemma ddg_cone_symmetric (A : Hom Rn Rn) : Tan T A -> adjL A = A.
Proof.
move=> hA; apply/eqP; rewrite -subr_eq0; apply/eqP.
apply: (ddg_hom_zero_of_small (K := 2))=> e he _.
have [S [r [hS [hr [_ hrA]]]]] := hA e he.
set w := r *: (S - T).
have hw : adjL w = w.
  rewrite /w ddg_adjointZ ddg_adjointB (ddg_projector_adjoint hS) (ddg_projector_adjoint hT).
  by [].
have he' : adjL A - A = adjL (A - w) - (A - w).
  by rewrite ddg_adjointB hw [RHS]ddg_sub_cancel.
rewrite he'; apply: (le_trans (ddg_hom_norm_sub _ _)).
rewrite ddg_hom_norm_adjoint.
have hAw : NH (A - w) < e.
  by rewrite /hom_norm (real_seminorm_subtract (inner_norm_real_norm _).1).
lra.
Qed.

(** Source for [ddg_cone_derivation]: DDG (A.2), p. 1143, first
    equality: A = A ∘ T + T ∘ A for A ∈ Tan(G(n, d), T). If S ∈ G(n, d),
    k = S - T and w = r k, then w - w ∘ T - T ∘ w = w ∘ k. Supporting
    lemma. *)
Lemma ddg_cone_derivation (A : Hom Rn Rn) : Tan T A -> A = hom_comp A T + hom_comp T A.
Proof.
move=> hA; apply/eqP; rewrite -subr_eq0; apply/eqP.
rewrite opprD addrA.
set K := Num.sqrt n%:R * (4 + NH A).
apply: (ddg_hom_zero_of_small (K := K))=> e he he1.
have [S [r [hS [hr [hST hrA]]]]] := hA e he.
set k := S - T; set w := r *: k; set u := A - w.
have hu : NH u < e.
  by rewrite /u /hom_norm (real_seminorm_subtract (inner_norm_real_norm _).1).
have hk : NH k < e by [].
have hw : NH w <= NH A + 1.
  have he2 : w = A - u by rewrite /u opprB addrC subrK.
  rewrite he2; apply: (le_trans (ddg_hom_norm_sub _ _)); rewrite lerD2l; lra.
have hb := inner_bilinear hBn.
have hkx x : k x - k (T x) - T (k x) = k (k x).
  rewrite /k !ddg_hom_subE !ddg_homB (ddg_projector_idem hT) (ddg_projector_idem hS).
  apply: (inner_vectors_ext hBn)=> z.
  rewrite !(bilBr hb); ring.
have hwx x : w x - w (T x) - T (w x) = w (k x).
  by rewrite /w !hom_scaleE ddg_homZ -!scalerBr hkx.
have hEx x : (A - hom_comp A T - hom_comp T A) x =
    (u x - u (T x) - T (u x)) + w (k x).
  by rewrite -hwx /u !ddg_hom_subE !hom_compE ddg_homB [RHS]ddg_sub_three.
have hcomp : NH (A - hom_comp A T - hom_comp T A) <= Num.sqrt n%:R * ((4 + NH A) * e).
  apply: ddg_hom_norm_from_vector_bound.
    by have hA0 := ddg_hom_norm_nonnegative A; apply: mulr_ge0; [lra|exact: ltW].
  move=> x; rewrite hEx.
  have hx0 := inner_norm_nonnegative hBn x.
  have hu0 := ddg_hom_norm_nonnegative u.
  have h1 : Nn (u x) <= NH u * Nn x := ddg_hom_vector_bound u x.
  have h2 : Nn (u (T x)) <= NH u * Nn x.
    apply: (le_trans (ddg_hom_vector_bound u (T x))).
    by rewrite ler_wpM2l // (ddg_projector_contraction hT).
  have h3 : Nn (T (u x)) <= NH u * Nn x.
    exact: le_trans (ddg_projector_contraction hT _) h1.
  have h4 : Nn (w (k x)) <= NH w * (NH k * Nn x).
    apply: (le_trans (ddg_hom_vector_bound w (k x))).
    by rewrite ler_wpM2l ?ddg_hom_norm_nonnegative // ddg_hom_vector_bound.
  have h5 : NH u * Nn x <= e * Nn x by rewrite ler_wpM2r // ltW.
  have hk0 := ddg_hom_norm_nonnegative k.
  have h6 : NH w * (NH k * Nn x) <= (NH A + 1) * (e * Nn x).
    apply: ler_pM=> //; first exact: ddg_hom_norm_nonnegative.
      by rewrite mulr_ge0.
    by rewrite ler_wpM2r // ltW.
  apply: (le_trans (ddg_vector_norm_triangle _ _)).
  have h7 : Nn (u x - u (T x) - T (u x)) <= Nn (u x) + Nn (u (T x)) + Nn (T (u x)).
    apply: (le_trans (ddg_vector_norm_sub _ _)); rewrite lerD2r.
    exact: ddg_vector_norm_sub.
  have he2 : (4 + NH A) * e * Nn x = e * Nn x + e * Nn x + e * Nn x + (NH A + 1) * (e * Nn x).
    by ring.
  rewrite he2; apply: lerD; last exact: le_trans h4 h6.
  apply: (le_trans h7); apply: lerD; last exact: le_trans h3 h5.
  by apply: lerD; [exact: le_trans h1 h5|exact: le_trans h2 h5].
by rewrite /K -mulrA.
Qed.

(** Source for [ddg_cone_S2]: DDG (A.2), p. 1143: Tan(G(n, d), T) is
    contained in SymEnd(R^n) ∩ {A : A = A ∘ T + T ∘ A}. Direct
    formalisation. *)
Theorem ddg_cone_S2 : Tan T `<=` ddg_tangent_S2 T.
Proof.
move=> A hA; split; [exact: ddg_cone_symmetric|exact: ddg_cone_derivation].
Qed.

(** Source for [ddg_tangent_S2_S1]: DDG p. 1143, "In particular, from
    the first equality above we obtain T ∘ T'(0) ∘ T = 0,
    T^⊥ ∘ T'(0) ∘ T^⊥ = 0"; blueprint ddg:A.tan. Direct formalisation. *)
Theorem ddg_tangent_S2_S1 : ddg_tangent_S2 T `<=` ddg_tangent_S1 T.
Proof.
move=> A [hAs hA].
have hAx x : A x = A (T x) + T (A x).
  by have := congr1 (fun f : Hom Rn Rn => f x) hA; rewrite hom_addE !hom_compE.
split=> //.
- apply: hom_ext=> x; rewrite !hom_compE hom_zeroE.
  have h := hAx (T x); rewrite (ddg_projector_idem hT) in h.
  by apply: (@addrI _ (A (T x))); rewrite addr0 -h.
- apply: hom_ext=> x; rewrite !hom_compE hom_zeroE.
  have h := hAx (ddg_perp T x); rewrite (ddg_perp_proj hT) ddg_hom0 add0r in h.
  by rewrite h (ddg_proj_perp hT).
Qed.

(** Source for [ddg_tangent_S1_S3]: blueprint ddg:A.tan: if
    A ∈ SymEnd(R^n), T ∘ A ∘ T = 0 and T^⊥ ∘ A ∘ T^⊥ = 0, then
    A = X + X^* with X = T^⊥ ∘ A ∘ T ∈ H_T. Direct formalisation. *)
Theorem ddg_tangent_S1_S3 : ddg_tangent_S1 T `<=` ddg_tangent_S3 T.
Proof.
move=> A [hAs h1 h2].
have h1x x : T (A (T x)) = 0.
  by have := congr1 (fun f : Hom Rn Rn => f x) h1; rewrite !hom_compE hom_zeroE.
have h2x x : ddg_perp T (A (ddg_perp T x)) = 0.
  by have := congr1 (fun f : Hom Rn Rn => f x) h2; rewrite !hom_compE hom_zeroE.
exists (hom_comp (ddg_perp T) (hom_comp A T)).
  apply: hom_ext=> x; rewrite !hom_compE.
  by rewrite (ddg_projector_idem hT) (ddg_perp_idem hT).
apply: hom_ext=> x; rewrite hom_addE !ddg_adjoint_comp hAs ddg_perp_adjoint.
rewrite (ddg_projector_adjoint hT) !hom_compE.
rewrite {1}(ddg_perp_decomposition T x) ddg_homD.
rewrite {1}(ddg_perp_decomposition T (A (T x))) h1x add0r.
rewrite {1}(ddg_perp_decomposition T (A (ddg_perp T x))) h2x addr0.
by [].
Qed.

(** Source for [ddg_tangent_S3_S2]: blueprint ddg:A.tan: if X ∈ H_T,
    then B = X + X^* satisfies B^* = B and B ∘ T + T ∘ B = B. Direct
    formalisation. *)
Theorem ddg_tangent_S3_S2 : ddg_tangent_S3 T `<=` ddg_tangent_S2 T.
Proof.
move=> A [X hX ->].
have hXx y : X y = ddg_perp T (X (T y)).
  by have := congr1 (fun f : Hom Rn Rn => f y) hX; rewrite !hom_compE.
have hXs : adjL X = hom_comp T (hom_comp (adjL X) (ddg_perp T)).
  rewrite {1}hX !ddg_adjoint_comp ddg_perp_adjoint (ddg_projector_adjoint hT).
  by apply: hom_ext=> y; rewrite !hom_compE.
have hXsx y : adjL X y = T (adjL X (ddg_perp T y)).
  by have := congr1 (fun f : Hom Rn Rn => f y) hXs; rewrite !hom_compE.
split; first by rewrite ddg_adjointD ddg_adjointK addrC.
apply: hom_ext=> x; rewrite !hom_addE !hom_compE !hom_addE.
have e1 : X (T x) = X x by rewrite [in RHS]hXx [in LHS]hXx (ddg_projector_idem hT).
have e2 : adjL X (T x) = 0 by rewrite hXsx (ddg_proj_perp hT) ddg_hom0 ddg_hom0.
have e3 : T (X x) = 0 by rewrite hXx (ddg_perp_proj hT).
have e4 : T (adjL X x) = adjL X x by rewrite hXsx (ddg_projector_idem hT).
by rewrite e1 e2 ddg_homD e3 e4 addr0 add0r.
Qed.

(** Source for [ddg_grassmann_tangent]: DDG p. 1143, display after (A.2),
    with equality; blueprint ddg:A.tan: Tan(G(n, d), T), the tangent cone
    of Federer 3.1.21 in Hom(R^n, R^n), equals
    SymEnd(R^n) ∩ {A : T ∘ A ∘ T = 0, T^⊥ ∘ A ∘ T^⊥ = 0}, and this set
    equals SymEnd(R^n) ∩ {A : A = A ∘ T + T ∘ A} and {X + X^* : X ∈ H_T}.
    Direct formalisation. *)
Theorem ddg_grassmann_tangent :
  [/\ Tan T = ddg_tangent_S1 T, ddg_tangent_S1 T = ddg_tangent_S2 T &
      ddg_tangent_S2 T = ddg_tangent_S3 T].
Proof.
have h12 := ddg_tangent_S2_S1; have h13 := ddg_tangent_S1_S3.
have h32 := ddg_tangent_S3_S2; have h3c := ddg_tangent_S3_cone.
have hc2 := ddg_cone_S2.
split; apply/seteqP; split=> A hA.
- exact: h12 (hc2 A hA).
- exact: h3c (h13 A hA).
- exact: h32 (h13 A hA).
- exact: h12 A hA.
- exact: h13 (h12 A hA).
- exact: h32 A hA.
Qed.

(** Source for [ddg_tangent_cone_linear]: DDG p. 1143: Tan_T G(n, d) is
    a vector subspace of Hom(R^n, R^n). Supporting lemma. *)
Lemma ddg_tangent_cone_linear (A B : Hom Rn Rn) (c : R) :
  Tan T A -> Tan T B -> Tan T (c *: A + B).
Proof.
have [h1 _ _] := ddg_grassmann_tangent.
rewrite h1=> [[hAs hA1 hA2]] [hBs hB1 hB2].
split.
- by rewrite ddg_adjointD ddg_adjointZ hAs hBs.
- apply: hom_ext=> x; rewrite !hom_compE (hom_addE (c *: A) B) (hom_scaleE c A) ddg_homD ddg_homZ hom_zeroE.
  have := congr1 (fun f : Hom Rn Rn => f x) hA1; rewrite !hom_compE hom_zeroE=> ->.
  have := congr1 (fun f : Hom Rn Rn => f x) hB1; rewrite !hom_compE hom_zeroE=> ->.
  by rewrite scaler0 addr0.
- apply: hom_ext=> x; rewrite !hom_compE (hom_addE (c *: A) B) (hom_scaleE c A) ddg_homD ddg_homZ hom_zeroE.
  have := congr1 (fun f : Hom Rn Rn => f x) hA2; rewrite !hom_compE hom_zeroE=> ->.
  have := congr1 (fun f : Hom Rn Rn => f x) hB2; rewrite !hom_compE hom_zeroE=> ->.
  by rewrite scaler0 addr0.
Qed.
End Member.
End Tangent.
