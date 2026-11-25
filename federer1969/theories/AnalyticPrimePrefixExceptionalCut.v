(** Federer (1969), 3.4.8(11), p. 334:
    choose the original prefix germ chi in the
    strictly enlarged ideal, set Phi=chi*Delta, and
    generate K from I_g and its pullback.
    The prefix image laws, prime product argument
    and original depth theorem prove every cut assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthogonalGroupTopology AnalyticGermUP AnalyticGermRing AnalyticGermRingLaws
  AnalyticGermRepresentatives AnalyticGermNoetherian CommutativeIdealUP AnalyticRotatedGermIdeal
  AnalyticReductionActual AnalyticCoordinateSubringFamilyUP AnalyticCoordinateSubringFamilySealed
  AnalyticPrefixGermSubring AnalyticPrefixGermMap GrassmannAbbreviations EuclideanInnerProduct
  SetGermUP GermVanishingSealed IdealVarietyGermSealed AnalyticDepthSealed PrimeIdealProductCut
  AnalyticEnlargedIdealVarietyDepth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrefixExceptionalCut.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Variable I:set A.
Variable g:@orthogonal_group R X B hB n e he.
Variable m:'I_n.
Variable hMN:(m<=n)%N.
Local Notation Y:=(R_n R m).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation C:=[the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)].
Local Notation PY:=(@analytic_representative_type R Y NY hNY 0).
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation Ig:=(@analytic_rotated_germ_ideal R X B hB n e he I g).
Local Notation Q:=(@AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega m).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).

(** Source for [analytic_prime_prefix_exceptional_cut]:
    the actual chi, Phi and enlarged K of
    3.4.8(11), p. 334. The larger-ideal
    intersection is precisely the preceding conclusion
    of original (10); all representatives, generated
    ideal laws and smaller-dimensional alternatives are proved. *)
Theorem analytic_prime_prefix_exceptional_cut (J:set A) (delta:PY):
  (0<m)%N ->is_prime_commutative_ideal Ig ->is_commutative_ideal J ->Ig `<=` J ->
  ~Ig (E (analytic_germ delta)) ->
  (exists theta,J theta /\Q theta /\~Ig theta) ->
  (forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g) ->
  exists chi:PY,exists K:set A,exists hK:is_finitely_generated_commutative_ideal K,
    J (E (analytic_germ chi)) /\~Ig (E (analytic_germ chi)) /\
    is_generated_commutative_ideal
      (Ig `|` [set phi:A|phi = E ((analytic_germ chi:C)*analytic_germ delta)]) K /\
    Ig `<=` K /\K `<=` J /\
    K (E ((analytic_germ chi:C)*analytic_germ delta)) /\
    ~Ig (E ((analytic_germ chi:C)*analytic_germ delta)) /\
    (let alpha:=@IdealVarietyGerm.value R X NX hNX 0 K hK in
      alpha = @set_germ T 0 set0 \/
      (depth (@AnalyticSetIdeal.value R X NX hNX 0 alpha)<m)%N).
Proof.
move=>hPositive hPrime hJ hIJ hDelta [theta [hTheta [hQ hNotTheta]]] hTail.
have hFamily:=@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega.
rewrite (analytic_coordinate_subring_family_member hFamily hMN) in hQ.
have [eta hEta]:=(@analytic_prefix_germ_subring_membership R X NX hNX n e he omega m hMN theta).1 hQ.
have [chi hChi]:=@analytic_germ_has_representative R Y NY hNY 0 eta.
have hChiEquation:E (analytic_germ chi) = theta by rewrite hChi.
have [K [hGenerated [hIK [hKJ [hPhi hNotPhi]]]]]:=
  @prime_ideal_product_cut A Ig J theta (E (analytic_germ delta)) hPrime hJ hIJ hTheta hNotTheta hDelta.
have hKIdeal:=generated_commutative_ideal_laws hGenerated.
have hK:=@finite_analytic_germ_ring_noetherian R X NX hNX n e 0 he K hKIdeal.
have hProduct:E ((analytic_germ chi:C)*analytic_germ delta) = theta*E (analytic_germ delta).
  by rewrite rmorphM hChiEquation.
have hPhiQ:Q (theta*E (analytic_germ delta)).
  rewrite -hProduct (analytic_coordinate_subring_family_member hFamily hMN).
  apply/analytic_prefix_germ_subring_membership;by exists ((analytic_germ chi:C)*analytic_germ delta).
have hNonzero:theta*E (analytic_germ delta)<>0.
  move=>hZero;apply:hNotPhi;rewrite hZero;exact:commutative_ideal_zero hPrime.1.
have hDimension:=@analytic_enlarged_ideal_variety_depth_drop R X B hB n e he hON omega hDual
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
