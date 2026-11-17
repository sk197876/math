(** Federer (1969), 3.4.8(11), pp. 334–335:
    apply the checked analytic monic-root control
    to the original finite prepared tail family.
    The same actual equations and coefficients
    occur in the laws and the radius estimates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology NormAnalyticUP
  AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives AnalyticPrefixCoordinatesSealed AnalyticRotatedGermIdeal
  AnalyticPreparedTailUP AnalyticMonicRootControl.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TailRootControl.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation Y:=(fun j:'I_n=>R_n R j).
Local Notation NY:=(fun j:'I_n=>inner_norm (@euclidean_inner_productP R j)).
Local Notation hNY:=(fun j:'I_n=>inner_norm_real_norm (@euclidean_inner_productP R j)).
Variable I:set (@analytic_germ_ring R X NX hNX 0).
Variable g:@orthogonal_group R X B hB n e he.
Variable m:nat.
Variable degree:'I_n->nat.
Variable U:forall j:'I_n,set (Y j).
Variable b:forall j:'I_n,'I_(degree j)->@analytic_representative_type R (Y j) (NY j) (hNY j) 0.
Variable f:'I_n->@analytic_representative_type R X NX hNX 0.

Hypothesis hLaws:@is_analytic_prepared_reduction_tail R X B hB n e he omega I g m degree U b f.

(** Source for [analytic_prepared_tail_root_control]:
    every original prepared W_j gives its
    smaller prefix radius in 3.4.8(11),
    pp. 334–335. The actual zero equations
    on D and the independent coefficient laws
    supply all hypotheses of the proved monic-root theorem. *)
Theorem analytic_prepared_tail_root_control (D:set X):
  (forall j:'I_n,(m<=j)%N ->forall x,D x ->analytic_representative_value (f j) x = 0) ->
  forall j:'I_n,(m<=j)%N ->forall r:R,0<r ->exists s:R,0<s /\s<r/2 /\
    forall x,D x ->
      NY j (@AnalyticPrefixCoordinates.projection R X n omega (j:nat)
        (leq_trans (leqnSn (j:nat)) (ltn_ord j)) x)<=s ->`|omega j x|<r/2.
Proof.
move=>hVanish j hMJ.
case:hLaws=>hIdeal hPositive hDomains hAnalytic hZero hFormula.
have hEquation x (hx:D x):(omega j x)^+(degree j)+
    \sum_(i<degree j) analytic_representative_value (@b j i)
      (@AnalyticPrefixCoordinates.projection R X n omega (j:nat)
        (leq_trans (leqnSn (j:nat)) (ltn_ord j)) x)*(omega j x)^+(i:nat) = 0.
  rewrite -(hFormula j hMJ);exact:hVanish j hMJ x hx.
exact:(@analytic_monic_root_radius_control R X (Y j) (NY j) (hNY j) (degree j) (@U j)
  (fun i=>analytic_representative_value (@b j i))
  (@AnalyticPrefixCoordinates.projection R X n omega (j:nat)
    (leq_trans (leqnSn (j:nat)) (ltn_ord j))) (omega j) D
  (hPositive j hMJ) (hDomains j hMJ).1 (hAnalytic j hMJ) (hZero j hMJ) hEquation).
Qed.
End TailRootControl.
