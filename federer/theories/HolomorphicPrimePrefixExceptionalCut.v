(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), p. 334:
    choose the original prefix germ chi in the
    strictly enlarged ideal, set Phi=chi*Delta, and
    generate K from I_g and its pullback.
    The prefix image laws, prime product argument
    and original depth theorem prove every cut assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthogonalGroupTopology HolomorphicGermUP HolomorphicGermRing HolomorphicGermRingLaws
  HolomorphicGermRepresentatives HolomorphicGermNoetherian CommutativeIdealUP HolomorphicRotatedGermIdeal
  HolomorphicReductionActual HolomorphicCoordinateSubringFamilyUP HolomorphicCoordinateSubringFamilySealed
  HolomorphicPrefixGermSubring HolomorphicPrefixGermMap GrassmannAbbreviations EuclideanInnerProduct
  SetGermUP HolomorphicGermVanishingSealed HolomorphicIdealVarietyGermSealed HolomorphicDepthSealed PrimeIdealProductCut
  HolomorphicEnlargedIdealVarietyDepth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrefixExceptionalCut.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable Herm:X->X->ComplexScalars.C R.
Hypothesis hHerm:is_hermitian_product Herm.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable hON:orthonormal_family Herm e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hHerm).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Variable I:set A.
Variable g:@unitary_group R X Herm hHerm (n+n) eR heR.
Variable m:'I_n.
Variable hMN:(m<=n)%N.
Local Notation Y:=(coordinate_space (ComplexScalars.C R) m).
Local Notation NY:=(@holomorphic_coordinate_norm R m).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R m)).
Local Notation C:=[the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)].
Local Notation PY:=(@holomorphic_representative_type R Y NY hNY 0).
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega m hMN).
Local Notation Ig:=(@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g).
Local Notation Q:=(@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega m).
Local Notation T:=(Topological.clone (real_norm_metric_space hNXR) _).
Local Notation depth:=(@HolomorphicDepth.value R X Herm hHerm n e he omega).

(** Source for [holomorphic_prime_prefix_exceptional_cut]:
    the actual chi, Phi and enlarged K of
    3.4.8(11), p. 334. The larger-ideal
    intersection is precisely the preceding conclusion
    of original (10); all representatives, generated
    ideal laws and smaller-dimensional alternatives are proved. *)
Theorem holomorphic_prime_prefix_exceptional_cut (J:set A) (delta:PY):
  (0<m)%N ->is_prime_commutative_ideal Ig ->is_commutative_ideal J ->Ig `<=` J ->
  ~Ig (E (holomorphic_germ delta)) ->
  (exists theta,J theta /\Q theta /\~Ig theta) ->
  (forall j:'I_n,(m<=j)%N ->@holomorphic_reduction_actual_B R X Herm hHerm n e he omega I j g) ->
  exists chi:PY,exists K:set A,exists hK:is_finitely_generated_commutative_ideal K,
    J (E (holomorphic_germ chi)) /\~Ig (E (holomorphic_germ chi)) /\
    is_generated_commutative_ideal
      (Ig `|` [set phi:A|phi = E ((holomorphic_germ chi:C)*holomorphic_germ delta)]) K /\
    Ig `<=` K /\K `<=` J /\
    K (E ((holomorphic_germ chi:C)*holomorphic_germ delta)) /\
    ~Ig (E ((holomorphic_germ chi:C)*holomorphic_germ delta)) /\
    (let alpha:=@HolomorphicIdealVarietyGerm.value R X NX hNXR 0 K hK in
      alpha = @set_germ T 0 set0 \/
      (depth (@HolomorphicSetIdeal.value R X NX hNXR 0 alpha)<m)%N).
Proof.
move=>hPositive hPrime hJ hIJ hDelta [theta [hTheta [hQ hNotTheta]]] hTail.
have hFamily:=@HolomorphicCoordinateSubringFamily.laws R X NX hNXR n e he omega.
rewrite (holomorphic_coordinate_subring_family_member hFamily hMN) in hQ.
have [eta hEta]:=(@holomorphic_prefix_germ_subring_membership R X NX hNXR n e he omega m hMN theta).1 hQ.
have [chi hChi]:=@holomorphic_germ_has_representative R Y NY hNY 0 eta.
have hChiEquation:E (holomorphic_germ chi) = theta by rewrite hChi.
have [K [hGenerated [hIK [hKJ [hPhi hNotPhi]]]]]:=
  @prime_ideal_product_cut A Ig J theta (E (holomorphic_germ delta)) hPrime hJ hIJ hTheta hNotTheta hDelta.
have hKIdeal:=generated_commutative_ideal_laws hGenerated.
have hK:=@finite_holomorphic_germ_ring_noetherian R X NX hNX n e 0 he K hKIdeal.
have hProduct:E ((holomorphic_germ chi:C)*holomorphic_germ delta) = theta*E (holomorphic_germ delta).
  by rewrite rmorphM hChiEquation.
have hPhiQ:Q (theta*E (holomorphic_germ delta)).
  rewrite -hProduct (holomorphic_coordinate_subring_family_member hFamily hMN).
  apply/holomorphic_prefix_germ_subring_membership;by exists ((holomorphic_germ chi:C)*holomorphic_germ delta).
have hNonzero:theta*E (holomorphic_germ delta)<>0.
  move=>hZero;apply:hNotPhi;rewrite hZero;exact:commutative_ideal_zero hPrime.1.
have hDimension:=@holomorphic_enlarged_ideal_variety_depth_drop R X Herm hHerm n e he omega hDual hON
  I K hK g m hPositive hIK hTail (ex_intro _ _ (conj hPhi (conj hPhiQ hNonzero))).
exists chi,K,hK;split;first by rewrite hChiEquation.
split;first by rewrite hChiEquation.
split;first by rewrite hProduct.
split;first exact:hIK.
split;first exact:hKJ.
split;first by rewrite hProduct.
split;first by rewrite hProduct.
exact:hDimension.
Qed.
End PrefixExceptionalCut.
