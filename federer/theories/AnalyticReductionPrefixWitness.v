(** Federer (1969), 3.4.8(6), p. 329:
    original A_j membership supplies an actual
    nonzero prefix germ with a positive first
    nonzero derivative. Properness, actual coordinate
    pullback and Taylor injectivity prove the witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology AnalyticGermRing
  AnalyticGermRingLaws AnalyticGermJetsSealed AnalyticGermFirstNonzeroJet AnalyticGermValueSealed
  AnalyticGermValueZerothJet AnalyticVanishingIdealSealed AnalyticVanishingIdealLaws
  CommutativeIdealUP AnalyticRotatedGermIdeal AnalyticReductionLociUP AnalyticReductionActual
  AnalyticPrefixCoordinatesSealed AnalyticPrefixGermMap AnalyticPrefixGermMapLaws
  AnalyticPrefixGermSubring AnalyticCoordinateSubringFamilyUP AnalyticCoordinateSubringFamilySealed
  PointedAnalyticPullbackValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_prefix_witness]: the
    original nonzero germ and positive order chosen
    in the proof of 3.4.8(6), p. 329.
    The prefix representative is an actual analytic
    germ; no regular-direction conclusion is assumed. *)
Theorem analytic_reduction_prefix_witness (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o)
  (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
  (j:'I_n.+1) (g:@orthogonal_group R X B hB n e he):
  is_commutative_ideal I ->~I 1 ->
  @analytic_reduction_actual_A R X B hB n e he omega I j g ->
  exists beta:@analytic_germ_ring R (R_n R j)
    (inner_norm (@euclidean_inner_productP R j)) (inner_norm_real_norm (@euclidean_inner_productP R j)) 0,
    @analytic_rotated_germ_ideal R X B hB n e he I g
      (@analytic_prefix_germ_map R X (inner_norm hB) (inner_norm_real_norm hB) n e he omega j (ltn_ord j) beta) /\
    beta<>0 /\exists k,(0<k)%N /\
      @AnalyticGermJets.value R (R_n R j) (inner_norm (@euclidean_inner_productP R j))
        (inner_norm_real_norm (@euclidean_inner_productP R j)) 0 k beta<>0 /\
      forall i,(i<k)%N ->@AnalyticGermJets.value R (R_n R j) (inner_norm (@euclidean_inner_productP R j))
        (inner_norm_real_norm (@euclidean_inner_productP R j)) 0 i beta = 0.
Proof.
move=>hI hProper hA.
pose NX:=inner_norm hB.
pose hNX:=inner_norm_real_norm hB.
pose Y:=R_n R j.
pose NY:=inner_norm (@euclidean_inner_productP R j).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R j).
pose P:=@analytic_prefix_germ_map R X NX hNX n e he omega j (ltn_ord j).
have hLaws:=@analytic_reduction_actual_laws R X B hB n e he omega I.
have [_ [alpha [hAlpha [hQ hNonzero]]]]:=(analytic_reduction_A_membership hLaws j g).1 hA.
have hQLaws:=@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega.
rewrite (analytic_coordinate_subring_family_member hQLaws (ltn_ord j)) in hQ.
have [beta hBeta]:=(@analytic_prefix_germ_subring_membership R X NX hNX n e he omega j (ltn_ord j) alpha).1 hQ.
have hBetaNonzero:beta<>0.
  move=>hZero;apply:hNonzero;by rewrite -hBeta hZero rmorph0.
have hRotated:=@analytic_rotated_germ_ideal_is_ideal R X B hB n e he I g hI.
have hRotatedProper:=@analytic_rotated_germ_ideal_proper R X B hB n e he I g hProper.
have hValue:@AnalyticGermValue.map R X NX hNX 0 alpha = 0.
  apply/(@AnalyticVanishingIdeal.laws R X NX hNX 0 alpha).
  exact:(@analytic_proper_ideal_vanishes R X NX hNX 0 _ hRotated hRotatedProper alpha hAlpha).
have hPullValue:=@pointed_analytic_pullback_centre_value R X Y NX NY hNX hNY 0 0
  (@AnalyticPrefixCoordinates.projection R X n omega j (ltn_ord j)) P
  (@analytic_prefix_germ_map_specification R X NX hNX n e he omega j (ltn_ord j))
  (@analytic_prefix_projection_zero R X n omega j (ltn_ord j)) beta.
have hBetaValue:@AnalyticGermValue.map R Y NY hNY 0 beta = 0.
  by rewrite -hPullValue hBeta.
have hBetaZeroJet:=(@analytic_germ_value_zeroth_jet R Y NY hNY 0 beta).1 hBetaValue.
have [k [hTop hLower]]:=@analytic_germ_first_nonzero_jet R Y NY hNY 0 beta hBetaNonzero.
have hPositive:(0<k)%N.
  case:k hTop hLower=>[|k] hTop hLower;last by [].
  exfalso;apply:hTop;exact:hBetaZeroJet.
exists beta;split;first by rewrite hBeta.
split;first exact:hBetaNonzero.
exists k;by split;last split.
Qed.
