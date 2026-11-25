(** De Philippis, De Rosa and Ghiraldin (2018), Appendix A, (A.1), p. 1143;
    blueprint ddg:A.1 (item A.2 of the blueprint). Identifying a d plane
    with the orthogonal projection onto it, G(n, d) is the set

        { T ∈ Hom(R^n, R^n) : T ∘ T = T, T^* = T, trace T = d },

    which is Allard's [orthogonal_projectors R n d] (Allard 2.3), with the
    metric space [projection_grassmann R n d]. This file gives the
    DDG-facing statement [ddg_A_1] and the assertions of the blueprint on
    T^⊥ = 1_{R^n} - T: T^⊥ ∈ G(n, n - d), im T^⊥ = ker T,
    T ∘ T^⊥ = T^⊥ ∘ T = 0 and |T| = d^{1/2}. It also collects pointwise
    identities for orthogonal projections used throughout Appendix A. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals ring lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities
  LinearBasis Bilinear TensorUP Hom HomInner HomInnerCoordinates AdjointUP AdjointLaws Adjoint
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates EuclideanRectangularAdjoint
  TraceDefinition TraceCyclic HilbertFormCompactness RealNormUP.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann.
From DPDRG Require Import DdgLinearAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Grassmann.
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
Local Notation tr := (@trace_Hom R (real_two_nonzero R) Rn (Finite.clone 'I_n _)
  (@coordinate_basis R n) hbn).

(** Source for [ddg_perp]: DDG Appendix A, p. 1143, and blueprint
    mr:notation: T^⊥ = 1_{R^n} - T for T ∈ G(n, d). Definition. *)
Definition ddg_perp (T : Hom Rn Rn) : Hom Rn Rn := idn - T.

(** Source for [ddg_perpE]: T^⊥(x) = x - T(x). Supporting lemma. *)
Lemma ddg_perpE (T : Hom Rn Rn) x : ddg_perp T x = x - T x.
Proof. by rewrite /ddg_perp ddg_hom_subE ddg_hom_idE. Qed.

(** Source for [ddg_perp_decomposition]: x = T(x) + T^⊥(x).
    Supporting lemma. *)
Lemma ddg_perp_decomposition (T : Hom Rn Rn) x : x = T x + ddg_perp T x.
Proof. by rewrite ddg_perpE addrC subrK. Qed.

Section Projector.
Variable k : nat.
Variable S : Hom Rn Rn.
Hypothesis hS : orthogonal_projectors R n k S.

(** Source for [ddg_projector_comp]: DDG (A.1): S ∘ S = S for
    S ∈ G(n, k). Supporting lemma. *)
Lemma ddg_projector_comp : hom_comp S S = S.
Proof. by have [h _ _] := hS. Qed.

(** Source for [ddg_projector_adjoint]: DDG (A.1): S^* = S for
    S ∈ G(n, k). Supporting lemma. *)
Lemma ddg_projector_adjoint : adjL S = S.
Proof. by have [_ h _] := hS. Qed.

(** Source for [ddg_projector_trace]: DDG (A.1): trace S = k for
    S ∈ G(n, k). Supporting lemma. *)
Lemma ddg_projector_trace : tr S = k%:R.
Proof. by have [_ _ h] := hS. Qed.

(** Source for [ddg_projector_idem]: S(S(x)) = S(x). Supporting lemma. *)
Lemma ddg_projector_idem x : S (S x) = S x.
Proof. exact: orthogonal_projector_idempotent hS x. Qed.

(** Source for [ddg_projector_sym]: S(x) • y = x • S(y). Supporting
    lemma. *)
Lemma ddg_projector_sym x y : Bn (S x) y = Bn x (S y).
Proof. exact: orthogonal_projector_symmetric hS x y. Qed.

(** Source for [ddg_perp_proj]: S(S^⊥(x)) = 0. Supporting lemma. *)
Lemma ddg_perp_proj x : S (ddg_perp S x) = 0.
Proof. by rewrite ddg_perpE linearB /= ddg_projector_idem subrr. Qed.

(** Source for [ddg_proj_perp]: S^⊥(S(x)) = 0. Supporting lemma. *)
Lemma ddg_proj_perp x : ddg_perp S (S x) = 0.
Proof. by rewrite ddg_perpE ddg_projector_idem subrr. Qed.

(** Source for [ddg_perp_idem]: S^⊥(S^⊥(x)) = S^⊥(x). Supporting
    lemma. *)
Lemma ddg_perp_idem x : ddg_perp S (ddg_perp S x) = ddg_perp S x.
Proof. by rewrite [in LHS]ddg_perpE ddg_perp_proj subr0. Qed.

(** Source for [ddg_perp_sym]: S^⊥(x) • y = x • S^⊥(y). Supporting
    lemma. *)
Lemma ddg_perp_sym x y : Bn (ddg_perp S x) y = Bn x (ddg_perp S y).
Proof.
rewrite !ddg_perpE (bilBl (inner_bilinear hBn)) (bilBr (inner_bilinear hBn)).
by rewrite ddg_projector_sym.
Qed.

(** Source for [ddg_projector_orthogonal]: S(x) • S^⊥(y) = 0.
    Supporting lemma. *)
Lemma ddg_projector_orthogonal x y : Bn (S x) (ddg_perp S y) = 0.
Proof. by rewrite ddg_projector_sym ddg_perp_proj (bil0r (inner_bilinear hBn)). Qed.

(** Source for [ddg_projector_pythagoras]: Allard 2.3(2), p. 422:
    |x|^2 = |S(x)|^2 + |S^⊥(x)|^2. Supporting lemma. *)
Lemma ddg_projector_pythagoras x : Nn x ^+ 2 = Nn (S x) ^+ 2 + Nn (ddg_perp S x) ^+ 2.
Proof.
have hx : x = S x + ddg_perp S x by rewrite ddg_perpE addrC subrK.
rewrite !inner_norm_sqr {1 2}hx (inner_sum_square hBn) ddg_projector_orthogonal.
by rewrite addr0 addr0.
Qed.

(** Source for [ddg_projector_contraction]: |S(x)| ≤ |x|. Supporting
    lemma. *)
Lemma ddg_projector_contraction x : Nn (S x) <= Nn x.
Proof.
rewrite -(ler_pXn2r (n := 2)) ?nnegrE ?inner_norm_nonnegative //.
rewrite (ddg_projector_pythagoras x) lerDl.
exact: exprn_ge0 (inner_norm_nonnegative _ _).
Qed.

(** Source for [ddg_perp_contraction]: |S^⊥(x)| ≤ |x|. Supporting
    lemma. *)
Lemma ddg_perp_contraction x : Nn (ddg_perp S x) <= Nn x.
Proof.
rewrite -(ler_pXn2r (n := 2)) ?nnegrE ?inner_norm_nonnegative //.
rewrite (ddg_projector_pythagoras x) lerDr.
exact: exprn_ge0 (inner_norm_nonnegative _ _).
Qed.

(** Source for [ddg_projector_fixed]: S(y) = y whenever y = S(z).
    Supporting lemma. *)
Lemma ddg_projector_fixed y : (exists z, S z = y) -> S y = y.
Proof. by move=> [z <-]; exact: ddg_projector_idem. Qed.
End Projector.

(** Source for [ddg_trace_identity]: Federer 1.4.5: trace 1_{R^n} = n.
    Supporting lemma. *)
Lemma ddg_trace_identity : tr idn = n%:R.
Proof.
rewrite (trace_orthonormal hBn hbn hbn (@coordinate_basis_orthonormal R n)).
under eq_bigr do rewrite hom_of_linearE /= (@coordinate_basis_orthonormal R n) eqxx.
by rewrite sumr_const card_ord.
Qed.

Variable d : nat.
Local Notation G := (orthogonal_projectors R n d).

(** Source for [ddg_A_1]: DDG (A.1), p. 1143: "G(n, d) ≃ {T ∈ R^n ⊗ R^n :
    T ∘ T = T, T^* = T, tr T = d}"; blueprint ddg:A.1. Allard's
    G(n, d) is defined by these three conditions, so the statement is
    an unfolding. Direct formalisation. *)
Theorem ddg_A_1 (T : Hom Rn Rn) :
  G T <-> [/\ hom_comp T T = T, adjL T = T & tr T = d%:R].
Proof. by []. Qed.

Section Member.
Variable T : Hom Rn Rn.
Hypothesis hT : G T.

(** Source for [ddg_A_1_norm]: blueprint ddg:A.1 and Allard 2.3(3):
    |T| = d^{1/2} for T ∈ G(n, d). Direct formalisation. *)
Theorem ddg_A_1_norm : NH T = Num.sqrt d%:R.
Proof.
have [_ h] := allard_2_3_3 hT.
rewrite -h sqrtr_sqr ger0_norm //; exact: ddg_hom_norm_nonnegative.
Qed.

(** Source for [ddg_A_1_dimension]: blueprint ddg:A.1: d ≤ n, because
    d = |T|^2 = Σ_i |T(e_i)|^2 ≤ Σ_i |e_i|^2 = n for the standard basis
    e of R^n. Supporting lemma. *)
Lemma ddg_A_1_dimension : (d <= n)%N.
Proof.
have [_ h] := allard_2_3_3 hT.
have hsum : NH T ^+ 2 = \sum_i Bn (T (@coordinate_basis R n i)) (T (@coordinate_basis R n i)).
  rewrite inner_norm_sqr.
  exact: (hom_inner_orthonormal_sum hBn hBn hbn hbn (@coordinate_basis_orthonormal R n)).
have hle : NH T ^+ 2 <= n%:R.
  rewrite hsum; apply: (@le_trans _ _ (\sum_(i < n) (1 : R))); last first.
    by rewrite sumr_const card_ord.
  apply: ler_sum=> i _.
  have he : Nn (@coordinate_basis R n i) = 1.
    by apply: inner_norm_value=> //; rewrite (@coordinate_basis_orthonormal R n) eqxx expr1n.
  have h1 := ddg_projector_contraction hT (@coordinate_basis R n i).
  rewrite he in h1; rewrite -(inner_norm_sqr hBn).
  by rewrite exprn_ile1 // inner_norm_nonnegative.
by rewrite h ler_nat in hle.
Qed.

(** Source for [ddg_A_1_perp]: blueprint ddg:A.1: T^⊥ ∈ G(n, n - d).
    Direct formalisation. *)
Theorem ddg_A_1_perp : orthogonal_projectors R n (n - d) (ddg_perp T).
Proof.
split.
- apply: hom_ext=> x; rewrite hom_compE; exact: ddg_perp_idem hT x.
- apply: ddg_adjoint_ext=> x y; exact: ddg_perp_sym hT x y.
- rewrite /ddg_perp linearB ddg_trace_identity (ddg_projector_trace hT).
  by rewrite natrB //; exact: ddg_A_1_dimension.
Qed.

(** Source for [ddg_A_1_composition]: blueprint ddg:A.1:
    T ∘ T^⊥ = T^⊥ ∘ T = 0. Direct formalisation. *)
Theorem ddg_A_1_composition : hom_comp T (ddg_perp T) = 0 /\ hom_comp (ddg_perp T) T = 0.
Proof.
split; apply: hom_ext=> x; rewrite hom_compE hom_zeroE.
- exact: ddg_perp_proj hT x.
- exact: ddg_proj_perp hT x.
Qed.

(** Source for [ddg_A_1_image]: blueprint ddg:A.1: im T^⊥ = ker T.
    Direct formalisation. *)
Theorem ddg_A_1_image y : (exists x, ddg_perp T x = y) <-> T y = 0.
Proof.
split.
- by move=> [x <-]; exact: ddg_perp_proj hT x.
- by move=> hy; exists y; rewrite ddg_perpE hy subr0.
Qed.
End Member.
End Grassmann.
