(** Federer (1969), 3.4.8(11), p. 334:
    the strict vanishing-ideal inclusion remains strict
    after the original orthogonal coordinate change.
    Injectivity of the already proved actual pullback
    reflects membership of the original witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology AnalyticGermRing AnalyticOrthogonalPullback AnalyticRotatedGermIdeal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_rotated_strict_ideal_witness]:
    the proper enlarged ideal in rotated
    coordinates, 3.4.8(11), p. 334. *)
Theorem analytic_rotated_strict_ideal_witness (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (I J:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
    (g:@orthogonal_group R X B hB n e he):
  (exists f,J f /\ ~I f) ->exists beta,
    @analytic_rotated_germ_ideal R X B hB n e he J g beta /\
    ~@analytic_rotated_germ_ideal R X B hB n e he I g beta.
Proof.
move=>[f [hJ hNotI]].
pose M:=@analytic_orthogonal_germ_map R X B hB n e he g.
exists (M f);split.
- apply/analytic_rotated_germ_ideal_membership;by exists f.
- move/analytic_rotated_germ_ideal_membership=>[alpha [hAlpha hValue]].
  have hEqual:alpha = f:=@analytic_orthogonal_germ_map_injective R X B hB n e he g alpha f hValue.
  apply:hNotI;by rewrite -hEqual.
Qed.
