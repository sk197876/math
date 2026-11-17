(** Supporting Federer (1969), 3.4.8(5), p. 328:
    the original minimum-depth tail excludes A at every index,
    including both endpoints. The positive case reuses the
    proved depth-drop argument of 3.4.8(11), p. 334. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthonormalFamilies OrthogonalGroupTopology AnalyticGermRing CommutativeIdealUP
  AnalyticReductionActual AnalyticReductionLociUP AnalyticDepthSealed AnalyticDepthExcludesReductionA.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_minimum_tail_excludes_A]: supporting the
    original E_m compact-cover sentence in Federer 3.4.8(5), p. 328.
    At minimum depth the original B-tail excludes A_m. Degree zero
    uses A_0 empty; every positive index uses the existing depth drop. *)
Theorem analytic_minimum_tail_excludes_A (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
    (hDual:forall i j,omega i (e j) = if i==j then 1 else 0)
    (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
    (m:'I_n.+1) (g:@orthogonal_group R X B hB n e he):
  is_commutative_ideal I ->~I 1 ->
  @AnalyticDepth.value R X B hB n e he omega I = (m:nat) ->
  (forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g) ->
  ~@analytic_reduction_actual_A R X B hB n e he omega I m g.
Proof.
move=>hI hProper hDepth hTail.
case hM:(m:nat)=>[|p].
- have hLoci:=@analytic_reduction_actual_laws R X B hB n e he omega I.
  move/(analytic_reduction_A_membership hLoci m g)=>[hPositive _].
  by rewrite hM in hPositive.
- have hPN:(p<n)%N.
    have hh:=ltn_ord m;rewrite hM in hh;exact:hh.
  pose j:'I_n:=Ordinal hPN.
  have hIndex:@Ordinal n.+1 (j:nat).+1 (ltn_ord j) = m.
    apply:val_inj;exact:esym hM.
  have hD:@AnalyticDepth.value R X B hB n e he omega I = (j:nat).+1.
    by rewrite hDepth hM.
  have hLater (k:'I_n):((j:nat).+1<=k)%N ->@analytic_reduction_actual_B R X B hB n e he omega I k g.
    move=>hK;apply:hTail;by rewrite hM.
  have hNot:=@analytic_depth_excludes_reduction_A R X B hB n e he hON omega hDual I j g
    hI hProper hD hLater.
  by rewrite hIndex in hNot.
Qed.
