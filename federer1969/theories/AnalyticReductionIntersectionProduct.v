(** Federer (1969), 3.4.8(14), p. 336:
    multiply the original directional witnesses for two
    component ideals. The product lies in their intersection,
    remains in the original coordinate subring, and has
    a positive nonzero derivative in the same direction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology AnalyticGermRing AnalyticRotatedGermIdeal AnalyticRotatedIdealIntersection
  AnalyticReductionActual AnalyticReductionLociUP AnalyticCoordinateSubringFamilySealed
  AnalyticCoordinateSubringFamilyUP AnalyticPrefixGermSubringLaws CommutativeSubringUP CommutativeIdealUP
  AnalyticVanishingIdealSealed AnalyticVanishingIdealLaws AnalyticGermValueSealed
  AnalyticGermValueZerothJet AnalyticGermJetsSealed AnalyticDirectionalProductNonzero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_intersection_product]: the product
    argument for B_j in 3.4.8(14), p. 336.
    Both original ideals are proper, so their actual
    witnesses vanish at the original centre. *)
Theorem analytic_reduction_intersection_product (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (omega:'I_n->Hom X R^o)
    (I J:set [the comNzRingType of (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)])
    (j:'I_n) (g:@orthogonal_group R X B hB n e he):
  is_commutative_ideal I ->~I 1 ->is_commutative_ideal J ->~J 1 ->
  @analytic_reduction_actual_B R X B hB n e he omega I j g ->
  @analytic_reduction_actual_B R X B hB n e he omega J j g ->
  @analytic_reduction_actual_B R X B hB n e he omega (I `&` J) j g.
Proof.
move=>hI hIProper hJ hJProper hBI hBJ.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
pose Ig:=@analytic_rotated_germ_ideal R X B hB n e he I g.
pose Jg:=@analytic_rotated_germ_ideal R X B hB n e he J g.
pose Q:=@AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega.
have hILaws:=@analytic_reduction_actual_laws R X B hB n e he omega I.
have hJLaws:=@analytic_reduction_actual_laws R X B hB n e he omega J.
have [alpha [hAlpha [hAlphaQ hAlphaJet]]]:=(analytic_reduction_B_membership hILaws j g).1 hBI.
have [beta [hBeta [hBetaQ hBetaJet]]]:=(analytic_reduction_B_membership hJLaws j g).1 hBJ.
have hIg:=@analytic_rotated_germ_ideal_is_ideal R X B hB n e he I g hI.
have hJg:=@analytic_rotated_germ_ideal_is_ideal R X B hB n e he J g hJ.
have hIgProper:=@analytic_rotated_germ_ideal_proper R X B hB n e he I g hIProper.
have hJgProper:=@analytic_rotated_germ_ideal_proper R X B hB n e he J g hJProper.
have hZeroth (K:set A) (hK:is_commutative_ideal K) (hKProper:~K 1) phi (hPhi:K phi):
    @AnalyticGermJets.value R X NX hNX 0 0%N phi=0.
  apply:(@analytic_germ_value_zeroth_jet R X NX hNX 0 phi).1.
  apply/(@AnalyticVanishingIdeal.laws R X NX hNX 0 phi).
  exact:(@analytic_proper_ideal_vanishes R X NX hNX 0 K hK hKProper phi hPhi).
have hProductJet:=@analytic_directional_product_nonzero R X NX hNX alpha beta (e j)
  (hZeroth Ig hIg hIgProper alpha hAlpha) (hZeroth Jg hJg hJgProper beta hBeta) hAlphaJet hBetaJet.
have hProductQ:Q (j:nat).+1 (alpha*beta).
  have hFamily:=@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega.
  have hSubring:is_commutative_subring (Q (j:nat).+1).
    rewrite /Q (analytic_coordinate_subring_family_member hFamily (ltn_ord j)).
    exact:(@analytic_prefix_germ_subring_laws R X NX hNX n e he omega (j:nat).+1 (ltn_ord j)).
  exact:(@commutative_subring_multiply A (Q (j:nat).+1) hSubring alpha beta hAlphaQ hBetaQ).
apply:(analytic_reduction_B_membership (@analytic_reduction_actual_laws R X B hB n e he omega (I `&` J)) j g).2.
exists (alpha*beta);split.
- rewrite analytic_rotated_ideal_intersection;split.
  + rewrite mulrC;exact:(@commutative_ideal_mul A Ig hIg beta alpha hAlpha).
  + exact:(@commutative_ideal_mul A Jg hJg alpha beta hBeta).
by split.
Qed.
