(** Federer (1969), 3.4.8(5), printed p. 328, proof:
    all original A_j(I), B_j(I), C_m(I), E_m(I) are countable unions
    of compact subsets of O(n). The original ideal is arbitrary
    and proper. Preserve the original empty and full indices. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HomInner LinearGroupTopology HilbertFormCompactness LinearBasis
  OrthonormalFamilies OrthogonalGroupTopology AnalyticGermRing CommutativeIdealUP AnalyticReductionActual
  IncreasingCompactCoverUP AnalyticReductionABCCompactCover AnalyticReductionECompactCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_8_5_sigma_compact]: stronger auxiliary
    assertion in the proof of Federer 3.4.8(5), p. 328. Every original
    A_j, B_j, C_m and E_m is a countable union of compact subsets
    of O(n), for every original proper ideal. The covers are increasing;
    the assertions assume no primeness, reducedness, geometric ideal
    representation, generic-rotation conclusion or additional exclusion. *)
Theorem federer_3_4_8_5_sigma_compact (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
    (hDual:forall i j,omega i (e j) = if i==j then 1 else 0)
    (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)):
  is_commutative_ideal I ->~I 1 ->
  (forall j:'I_n.+1,exists K:nat->set (@orthogonal_group R X B hB n e he),
    is_increasing_compact_cover (@analytic_reduction_actual_A R X B hB n e he omega I j) K) /\
  (forall j:'I_n,exists K:nat->set (@orthogonal_group R X B hB n e he),
    is_increasing_compact_cover (@analytic_reduction_actual_B R X B hB n e he omega I j) K) /\
  (forall m:'I_n,exists K:nat->set (@orthogonal_group R X B hB n e he),
    is_increasing_compact_cover (@analytic_reduction_actual_C R X B hB n e he omega I m) K) /\
  (forall m:'I_n.+1,exists K:nat->set (@orthogonal_group R X B hB n e he),
    is_increasing_compact_cover (@analytic_reduction_actual_E R X B hB n e he omega I m) K).
Proof.
move=>hI hProper;split.
- exact:(@analytic_reduction_actual_A_compact_cover R X B hB n e he omega hDual I hI).
- split.
  + exact:(@analytic_reduction_actual_B_compact_cover R X B hB n e he omega hDual I hI).
  + split.
    * exact:(@analytic_reduction_actual_C_compact_cover R X B hB n e he omega hDual I hI).
    * move=>m;exact:(@analytic_reduction_actual_E_compact_cover R X B hB n e he hON omega hDual I m hI hProper).
Qed.
