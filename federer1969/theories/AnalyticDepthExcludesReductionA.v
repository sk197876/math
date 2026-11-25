(** Federer (1969), 3.4.8(11), p. 334:
    at the least reduction depth, a direction
    retaining all later B_j cannot belong to A_m.
    Original (6) would supply the missing B_m;
    prefix transport preserves every later witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthogonalGroupTopology AnalyticGermRing CommutativeIdealUP
  AnalyticReductionActual AnalyticDepthSealed AnalyticReductionATailDepthDrop.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_depth_excludes_reduction_A]:
    the minimal-depth contradiction in 3.4.8(11),
    p. 334. All group and Haar objects
    are local existence witnesses. *)
Theorem analytic_depth_excludes_reduction_A (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
    (hDual:forall i k,omega i (e k) = if i==k then 1 else 0)
    (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
    (j:'I_n) (g:@orthogonal_group R X B hB n e he):
  is_commutative_ideal I ->~I 1 ->
  @AnalyticDepth.value R X B hB n e he omega I = (j:nat).+1 ->
  (forall k:'I_n,((j:nat).+1<=k)%N ->
    @analytic_reduction_actual_B R X B hB n e he omega I k g) ->
  ~@analytic_reduction_actual_A R X B hB n e he omega I
    (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) g.
Proof.
move=>hI hProper hDepth hLater hA.
have hDrop:=@analytic_reduction_A_tail_depth_drop R X B hB n e he hON omega hDual
  I j g hI hProper hLater hA.
by rewrite hDepth ltnn in hDrop.
Qed.
