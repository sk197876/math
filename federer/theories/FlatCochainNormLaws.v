(** Federer (1969), 4.1.19, p. 377: the
    least common flat bound is a norm
    on the actual cochain space. All arguments
    use only the original compact-index inequalities
    and the opaque least-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Bilinear Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  FlatCurrentUnionSpace FlatCochainUP FlatCochainSpace
  LinearSubspaceRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section NormLaws.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation W := (@flat_cochain_space R h2 n m U hU).
Local Notation E := (@flat_cochain_evaluation R h2 n m U hU).
Local Notation hW := (@flat_cochain_space_laws R h2 n m U hU).
Local Notation N := (@flat_cochain_norm R h2 n m U hU).
Local Notation hN := (@flat_cochain_norm_laws R h2 n m U hU).

(** Source for [flat_cochain_norm_scale_le]: the
    scalar estimate for the original cochain norm,
    supporting Federer 4.1.19, p. 377.
    The original common bound scales by |c|. *)
Lemma flat_cochain_norm_scale_le (c : R) (alpha : W) :
  N (c*:alpha)%R <= `|c|*N alpha.
Proof.
apply: ((hN (c*:alpha)%R).2).
rewrite (linZ (hom_linear E)).
exact: (@flat_cochain_scale_bound R h2 n m U hU
  (E alpha) (N alpha) c (hN alpha).1).
Qed.

(** Source for [flat_cochain_norm_is_norm]: the
    original F(alpha) is a norm on all
    flat cochains, Federer 4.1.19, p. 377.
    Definiteness uses each flat current's own compact
    index, not one index fixed for the cochain. *)
Theorem flat_cochain_norm_is_norm : is_real_norm N.
Proof.
have hNonnegative (alpha : W) : 0 <= N alpha := (hN alpha).1.1.
have hZero : N (0:W) = 0.
  have hBound : @is_flat_cochain_bound R h2 n m U hU (E 0) 0.
    rewrite linear0; exact: (@flat_cochain_zero_bound R h2 n m U hU).
  apply/eqP; rewrite eq_le hNonnegative andbT.
  exact: ((hN 0).2 0 hBound).
split.
- constructor.
  + exact: hNonnegative.
  + move=> c alpha; have [->|hC] := eqVneq c 0.
      by rewrite scale0r hZero normr0 mul0r.
    apply/eqP; rewrite eq_le; apply/andP; split.
    * exact: flat_cochain_norm_scale_le.
    * have hReverse := flat_cochain_norm_scale_le c^-1 (c*:alpha)%R.
      rewrite scalerA mulVf // scale1r normfV mulrC in hReverse.
      have hPositive : 0 < `|c| by rewrite normr_gt0.
      by rewrite ler_pdivlMr // mulrC in hReverse.
  + move=> alpha beta; apply: ((hN (alpha+beta)%R).2).
    rewrite (linD (hom_linear E)).
    exact: (@flat_cochain_add_bound R h2 n m U hU
      (E alpha) (E beta) (N alpha) (N beta)
      (hN alpha).1 (hN beta).1).
- move=> alpha hAlpha; apply: (subspace_representation_injective hW).
  apply: hom_ext=> T; rewrite linear0 hom_zeroE.
  have [K hFlat] :=
    @flat_current_union_inclusion_member R h2 n m U hU T.
  have hBound := (hN alpha).1.2 K T hFlat.
  rewrite hAlpha mul0r in hBound.
  have hAbsolute : `|E alpha T| = 0.
    apply/eqP; by rewrite eq_le hBound normr_ge0.
  by move/eqP: hAbsolute; rewrite normr_eq0=> /eqP.
Qed.
End NormLaws.
