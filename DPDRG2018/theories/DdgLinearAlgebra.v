(** De Philippis, De Rosa and Ghiraldin (2018), Appendix A, pp. 1143–1144;
    blueprint mr:notation. Supporting linear algebra in End(R^n) =
    Hom(R^n, R^n) for the formalisation of Appendix A: the pointwise
    arithmetic of Hom, the adjoint L^* of Federer 1.7.4
    ([euclidean_rectangular_adjoint]), the inner product A • B and the norm
    |A| of Federer 1.7.9 ([hom_inner], [hom_norm]), the estimate of |A| by a
    pointwise bound, and the estimate |A ∘ B| ≤ n^{1/2} |A| |B|. Nothing in
    this file is a new mathematical object; the lemmas are supporting
    lemmas for the items of Appendix A. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals ring lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities
  LinearBasis Bilinear TensorUP Hom HomInner HomInnerCoordinates AdjointUP AdjointLaws Adjoint
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates EuclideanRectangularAdjoint
  HomNormBound HomSpaceTopology HomOperatorNorm HilbertFormCompactness RealNormUP.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors
  AllardProjectionContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [ddg_rearrange]: commutativity and associativity of
    addition in an abelian group: a + b - e - (x + y) =
    (- e - x) + (a - y) + b. Supporting lemma. *)
Lemma ddg_rearrange (V : zmodType) (a b e x y : V) :
  a + b - e - (x + y) = (- e - x) + (a - y) + b.
Proof.
rewrite opprD !addrA.
rewrite [a + b - e]addrAC [a - e + b - x]addrAC [a - e - x + b - y]addrAC.
by rewrite [- e - x + a]addrC !addrA.
Qed.

(** Source for [ddg_sub_sub]: abelian group arithmetic:
    (y - p) - (y - t) = - (p - t). Supporting lemma. *)
Lemma ddg_sub_sub (V : zmodType) (y p t : V) : (y - p) - (y - t) = - (p - t).
Proof. by rewrite opprB addrC addrA subrK opprB. Qed.

Section LinearAlgebra.
Variable R : realType.
Variable n : nat.
Local Notation Rn := (R_n R n).
Local Notation Bn := (@euclidean_inner_product R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation Nn := (inner_norm hBn).
Local Notation NH := (hom_norm hBn hBn hbn).
Local Notation adjL L := (euclidean_rectangular_adjoint L).
Local Notation idn := (hom_of_linear (linear_id Rn)).

(** Source for [ddg_hom_subE]: Federer 1.4.1: the operations of
    Hom(R^n, R^n) are pointwise, (f - g)(x) = f(x) - g(x). Supporting
    lemma. *)
Lemma ddg_hom_subE (f g : Hom Rn Rn) x : (f - g) x = f x - g x.
Proof. by rewrite hom_addE. Qed.

(** Source for [ddg_hom_oppE]: Federer 1.4.1: (- f)(x) = - f(x).
    Supporting lemma. *)
Lemma ddg_hom_oppE (f : Hom Rn Rn) x : (- f) x = - f x.
Proof. by []. Qed.

(** Source for [ddg_homD]: Federer 1.4.1: members of Hom(R^n, R^n) are
    additive, f(x + y) = f(x) + f(y). Stated with the coercion of Hom so
    that rewriting keeps the head [hom_fun]. Supporting lemma. *)
Lemma ddg_homD (f : Hom Rn Rn) x y : f (x + y) = f x + f y.
Proof. exact: linearD. Qed.

(** Source for [ddg_homB]: Federer 1.4.1: f(x - y) = f(x) - f(y).
    Supporting lemma. *)
Lemma ddg_homB (f : Hom Rn Rn) x y : f (x - y) = f x - f y.
Proof. exact: linearB. Qed.

(** Source for [ddg_homN]: Federer 1.4.1: f(- x) = - f(x). Supporting
    lemma. *)
Lemma ddg_homN (f : Hom Rn Rn) x : f (- x) = - f x.
Proof. exact: linearN. Qed.

(** Source for [ddg_homZ]: Federer 1.4.1: f(c x) = c f(x). Supporting
    lemma. *)
Lemma ddg_homZ (f : Hom Rn Rn) (c : R) x : f (c *: x) = c *: f x.
Proof. exact: linearZ. Qed.

(** Source for [ddg_hom0]: Federer 1.4.1: f(0) = 0. Supporting lemma. *)
Lemma ddg_hom0 (f : Hom Rn Rn) : f 0 = 0.
Proof. exact: linear0. Qed.

(** Source for [ddg_hom_idE]: the identity map 1_{R^n} of Federer
    p. 669. Supporting lemma. *)
Lemma ddg_hom_idE x : idn x = x.
Proof. exact: hom_of_linearE. Qed.

(** Source for [ddg_adjoint_pairing]: the defining identity
    x • L^*(y) = L(x) • y of the adjoint, Federer 1.7.4, p. 30.
    Supporting lemma. *)
Lemma ddg_adjoint_pairing (f : Hom Rn Rn) x y : Bn x (adjL f y) = Bn (f x) y.
Proof. exact: euclidean_rectangular_adjoint_pairing. Qed.

(** Source for [ddg_adjoint_ext]: uniqueness of the adjoint, Federer
    1.7.4, p. 30: if f(x) • y = x • g(y) for all x and y, then
    f^* = g. Supporting lemma. *)
Lemma ddg_adjoint_ext (f g : Hom Rn Rn) :
  (forall x y, Bn (f x) y = Bn x (g y)) -> adjL f = g.
Proof.
move=> h; apply: hom_ext=> y; apply: (inner_vectors_ext hBn)=> x.
by rewrite ddg_adjoint_pairing h.
Qed.

(** Source for [ddg_adjointK]: Federer 1.7.4, p. 30: the adjoint of f^* is f.
    Supporting lemma. *)
Lemma ddg_adjointK (f : Hom Rn Rn) : adjL (adjL f) = f.
Proof.
apply: ddg_adjoint_ext=> x y.
by rewrite (inner_symmetric hBn) ddg_adjoint_pairing (inner_symmetric hBn).
Qed.

(** Source for [ddg_adjoint_comp]: Federer 1.7.4, p. 30:
    (f ∘ g)^* = g^* ∘ f^*. Supporting lemma. *)
Lemma ddg_adjoint_comp (f g : Hom Rn Rn) :
  adjL (hom_comp f g) = hom_comp (adjL g) (adjL f).
Proof.
apply: ddg_adjoint_ext=> x y.
by rewrite !hom_compE !ddg_adjoint_pairing.
Qed.

(** Source for [ddg_adjointD]: Federer 1.7.4, p. 30: the adjoint is
    linear, (f + g)^* = f^* + g^*. Supporting lemma. *)
Lemma ddg_adjointD (f g : Hom Rn Rn) : adjL (f + g) = adjL f + adjL g.
Proof. exact: linearD. Qed.

(** Source for [ddg_adjointB]: Federer 1.7.4, p. 30:
    (f - g)^* = f^* - g^*. Supporting lemma. *)
Lemma ddg_adjointB (f g : Hom Rn Rn) : adjL (f - g) = adjL f - adjL g.
Proof. exact: linearB. Qed.

(** Source for [ddg_adjointZ]: Federer 1.7.4, p. 30:
    (c f)^* = c f^*. Supporting lemma. *)
Lemma ddg_adjointZ (c : R) (f : Hom Rn Rn) : adjL (c *: f) = c *: adjL f.
Proof. exact: linearZ. Qed.

(** Source for [ddg_adjoint_id]: Federer 1.7.4, p. 30: (1_{R^n})^* =
    1_{R^n}. Supporting lemma. *)
Lemma ddg_adjoint_id : adjL idn = idn.
Proof. by apply: ddg_adjoint_ext=> x y; rewrite !ddg_hom_idE. Qed.

(** Source for [ddg_hom_norm_nonnegative]: Federer 1.7.9, p. 35:
    0 ≤ |f|. Supporting lemma. *)
Lemma ddg_hom_norm_nonnegative (f : Hom Rn Rn) : 0 <= NH f.
Proof. exact: inner_norm_nonnegative. Qed.

(** Source for [ddg_hom_norm_adjoint]: Federer 1.7.9, p. 35:
    |f^*| = |f|. Supporting lemma. *)
Lemma ddg_hom_norm_adjoint (f : Hom Rn Rn) : NH (adjL f) = NH f.
Proof.
apply: (inner_norm_value _ (ddg_hom_norm_nonnegative f)).
rewrite inner_norm_sqr.
exact: esym (euclidean_adjoint_hom_inner f).
Qed.

(** Source for [ddg_hom_vector_bound]: Federer 1.7.9, p. 35:
    |f(x)| ≤ |f| |x|. Supporting lemma. *)
Lemma ddg_hom_vector_bound (f : Hom Rn Rn) x : Nn (f x) <= NH f * Nn x.
Proof. exact: hom_norm_vector_bound. Qed.

(** Source for [ddg_hom_norm_from_vector_bound]: Federer 1.7.6 and
    1.7.9, pp. 33–35: if 0 ≤ a and |f(v)| ≤ a |v| for v ∈ R^n, then
    ||f|| ≤ a and |f| ≤ n^{1/2} ||f|| ≤ n^{1/2} a. Supporting lemma. *)
Lemma ddg_hom_norm_from_vector_bound (f : Hom Rn Rn) (a : R) :
  0 <= a -> (forall v, Nn (f v) <= a * Nn v) -> NH f <= Num.sqrt n%:R * a.
Proof.
move=> ha h.
have h1 := @hom_operator_norm_least _ _ _ _ _ hBn hBn _ _ hbn f a ha h.
have [_ h2] := hom_operator_norm_comparison hBn hBn hbn f.
apply: (le_trans h2); rewrite ler_wpM2l //; exact: sqrtr_ge0.
Qed.

(** Source for [ddg_hom_norm_comp]: Federer 1.7.9, p. 35:
    |f ∘ g| ≤ n^{1/2} |f| |g|, because |f(g(v))| ≤ |f| |g| |v|.
    Supporting lemma. *)
Lemma ddg_hom_norm_comp (f g : Hom Rn Rn) :
  NH (hom_comp f g) <= Num.sqrt n%:R * (NH f * NH g).
Proof.
apply: ddg_hom_norm_from_vector_bound.
  by rewrite mulr_ge0 // ddg_hom_norm_nonnegative.
move=> v; rewrite hom_compE.
apply: (le_trans (ddg_hom_vector_bound f (g v))).
rewrite -mulrA ler_wpM2l ?ddg_hom_norm_nonnegative //.
exact: ddg_hom_vector_bound.
Qed.

(** Source for [ddg_hom_norm_triangle]: Federer 1.7.1, p. 28:
    |f + g| ≤ |f| + |g|. Supporting lemma. *)
Lemma ddg_hom_norm_triangle (f g : Hom Rn Rn) : NH (f + g) <= NH f + NH g.
Proof. exact: inner_norm_triangle. Qed.

(** Source for [ddg_hom_norm_sub]: Federer 1.7.1, p. 28:
    |f - g| ≤ |f| + |g|. Supporting lemma. *)
Lemma ddg_hom_norm_sub (f g : Hom Rn Rn) : NH (f - g) <= NH f + NH g.
Proof.
apply: (le_trans (ddg_hom_norm_triangle f (- g))).
by rewrite /hom_norm inner_normN.
Qed.

(** Source for [ddg_hom_norm_eq0]: Federer 1.7.1, p. 28: |f| = 0
    implies f = 0. Supporting lemma. *)
Lemma ddg_hom_norm_eq0 (f : Hom Rn Rn) : NH f <= 0 -> f = 0.
Proof.
move=> h; have h0 : NH f = 0 by apply/eqP; rewrite eq_le h ddg_hom_norm_nonnegative.
by apply/eqP; rewrite -(inner_norm_eq0 (hom_inner_productP hBn hBn hbn)); apply/eqP; exact: h0.
Qed.

(** Source for [ddg_vector_norm_triangle]: Federer 1.7.1, p. 28:
    |x + y| ≤ |x| + |y| in R^n. Supporting lemma. *)
Lemma ddg_vector_norm_triangle (x y : Rn) : Nn (x + y) <= Nn x + Nn y.
Proof. exact: inner_norm_triangle. Qed.

(** Source for [ddg_vector_norm_sub]: Federer 1.7.1, p. 28:
    |x - y| ≤ |x| + |y| in R^n. Supporting lemma. *)
Lemma ddg_vector_norm_sub (x y : Rn) : Nn (x - y) <= Nn x + Nn y.
Proof.
apply: (le_trans (ddg_vector_norm_triangle x (- y))).
by rewrite inner_normN.
Qed.

(** Source for [ddg_vector_cauchy]: Cauchy's inequality, Federer
    1.7.1, p. 28: |x • y| ≤ |x| |y|. Supporting lemma. *)
Lemma ddg_vector_cauchy (x y : Rn) : `|Bn x y| <= Nn x * Nn y.
Proof. exact: inner_cauchy. Qed.

(** Source for [ddg_vector_bound_by_pairing]: Federer 1.7.1, p. 28:
    if 0 ≤ a and |u|^2 = u • u ≤ a |u|, then |u| ≤ a. Supporting lemma
    for the estimates of DDG Lemma A.1. *)
Lemma ddg_vector_bound_by_pairing (u : Rn) (a : R) :
  0 <= a -> Bn u u <= a * Nn u -> Nn u <= a.
Proof.
move=> ha h.
have hu := inner_norm_nonnegative hBn u.
rewrite -(inner_norm_sqr hBn) in h.
have [hz|hp] := eqVneq (Nn u) 0; first by rewrite hz.
have hpos : 0 < Nn u by rewrite lt_def hp hu.
by rewrite expr2 ler_pM2r // in h.
Qed.

(** Source for [ddg_nonpositive_of_small]: elementary real analysis:
    if a ≤ K e for 0 < e ≤ 1, then a ≤ 0. Supporting lemma. *)
Lemma ddg_nonpositive_of_small (a K : R) :
  (forall e : R, 0 < e -> e <= 1 -> a <= K * e) -> a <= 0.
Proof.
move=> h; rewrite leNgt; apply/negP=> ha.
have [hK|hK] := lerP K 0.
  have h1 := h 1 ltr01 (lexx 1); rewrite mulr1 in h1.
  by have := lt_le_trans ha (le_trans h1 hK); rewrite ltxx.
pose e := Num.min 1 (a / (2 * K)).
have hK2 : 0 < 2 * K by rewrite mulr_gt0.
have he : 0 < e by rewrite lt_min ltr01 divr_gt0.
have he1 : e <= 1 by rewrite ge_min lexx.
have he2 : e <= a / (2 * K) by rewrite ge_min lexx orbT.
have h1 := h e he he1.
have h2 : K * e <= K * (a / (2 * K)) by rewrite ler_pM2l.
have h3 : K * (a / (2 * K)) = a / 2 by field; rewrite gt_eqF.
have : a <= a / 2 by rewrite -h3; exact: le_trans h1 h2.
lra.
Qed.

(** Source for [ddg_hom_zero_of_small]: if |f| ≤ K e for 0 < e ≤ 1,
    then f = 0. Supporting lemma. *)
Lemma ddg_hom_zero_of_small (f : Hom Rn Rn) (K : R) :
  (forall e : R, 0 < e -> e <= 1 -> NH f <= K * e) -> f = 0.
Proof. by move=> h; apply: ddg_hom_norm_eq0; exact: ddg_nonpositive_of_small h. Qed.

End LinearAlgebra.
