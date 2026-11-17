(** Federer (1969), 3.4.8(14), p. 336:
    the rotated vanishing ideal of a finite union
    is the intersection of its rotated component ideals.
    The existing injectivity of orthogonal germ pullback
    gives this exact binary intersection identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology AnalyticGermRing AnalyticOrthogonalPullback AnalyticRotatedGermIdeal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_rotated_ideal_intersection]: the ideal
    membership of the original product witness in
    3.4.8(14), p. 336. This supporting identity
    holds for arbitrary original subsets of the germ ring. *)
Theorem analytic_rotated_ideal_intersection (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (I J:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
    (g:@orthogonal_group R X B hB n e he):
  @analytic_rotated_germ_ideal R X B hB n e he (I `&` J) g=
    @analytic_rotated_germ_ideal R X B hB n e he I g `&`
    @analytic_rotated_germ_ideal R X B hB n e he J g.
Proof.
apply/seteqP;split=>phi.
- move/analytic_rotated_germ_ideal_membership=>[alpha [[hI hJ] hMap]].
  split;apply/analytic_rotated_germ_ideal_membership;exists alpha;by split.
- move=>[/analytic_rotated_germ_ideal_membership[alpha [hI hAlpha]]
    /analytic_rotated_germ_ideal_membership[beta [hJ hBeta]]].
  have hEqual:alpha=beta.
    apply:(@analytic_orthogonal_germ_map_injective R X B hB n e he g).
    exact:eq_trans hAlpha (esym hBeta).
  apply/analytic_rotated_germ_ideal_membership;exists alpha;split;last exact:hAlpha.
  split;first exact:hI;by rewrite hEqual.
Qed.
