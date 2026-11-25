(** Federer (1969), 3.4.11, p. 338:
    every original B_j witness gives original A_j
    membership. This elementary connection uses the already
    specified reduction loci and the actual zero-jet law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermRing AnalyticGermJetsSealed AnalyticGermJetZeroNegate AnalyticReductionLociUP AnalyticReductionActual.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_reduction_B_contained_A]: the
    original inclusion B_(j+1) contained in A_(j+1)
    used with the reduction tail in 3.4.11,
    p. 338. Every original ideal and index remain. *)
Theorem analytic_reduction_B_contained_A (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o)
  (I:classical_sets.set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
  (j:'I_n) g:
  @analytic_reduction_actual_B R X B hB n e he omega I j g ->
  @analytic_reduction_actual_A R X B hB n e he omega I
    (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) g.
Proof.
have hLaws:=@analytic_reduction_actual_laws R X B hB n e he omega I.
move/(analytic_reduction_B_membership hLaws j g)=>[alpha [hAlpha [hQ [k [hPositive hDirection]]]]].
apply/(analytic_reduction_A_membership hLaws _ g).
split;first exact:ltn0Sn.
exists alpha;split;first exact:hAlpha.
split;first exact:hQ.
move=>hZero;apply:hDirection.
change (@ContinuousMultilinear.evaluation R k X R^o (inner_norm hB) (fun t:R^o=>`|t|)
  (inner_norm_real_norm hB) (@scalar_absolute_value_norm R) [ffun _=>e j]
  (@AnalyticGermJets.value R X (inner_norm hB) (inner_norm_real_norm hB) 0 k alpha)=0).
by rewrite hZero analytic_germ_jet_zero linear0.
Qed.
