(** Federer (1969), 3.4.8(8), p. 329:
    each original prefix quotient is finite over
    the preceding coefficient ring and generated
    by its last coordinate. The existing
    preparation and division theorems supply this
    assertion through the actual image quotient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  EuclideanScalarCoordinateMaps EuclideanStiefelInnerSplitting OrthogonalGroupTopology
  AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives AnalyticCoordinateGermsSealed
  AnalyticPrefixCoordinatesSealed AnalyticPrefixGermMap AnalyticPrefixGermMapLaws
  AnalyticPrefixNestedComposition AnalyticPrefixCoordinateGerm AnalyticPrefixWeierstrassSplit
  AnalyticRotatedGermIdeal AnalyticReductionActual AnalyticReductionCoordinateRegularWitness
  CommutativeIdealUP CommutativeQuotientUP CommutativeFieldKernel
  CommutativeSubringUP CommutativeSubringRealisationUP CommutativeRingImageQuotient
  RingScalarRestriction RingSubmoduleUP WeierstrassFunctionalPower RegularAnalyticQuotientAtZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrefixStep.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Variable I:set G.
Hypothesis hI:is_commutative_ideal I.
Hypothesis hProper:~I 1.
Variable g:@orthogonal_group R X B hB n e he.
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Hypothesis hPi:is_commutative_ideal_quotient (@analytic_rotated_germ_ideal R X B hB n e he I g) pi.
Variable j:'I_n.
Local Notation Y:=(R_n R (j:nat).+1).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R (j:nat).+1)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R (j:nat).+1)).
Local Notation Z:=(R_n R (j:nat)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R (j:nat))).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (j:nat))).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R Z NZ hNZ 0)].
Local Notation A1:=[the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)].
Local Notation hJN:=(leq_trans (leqnSn (j:nat)) (ltn_ord j)).
Local Notation E0:=(@analytic_prefix_germ_map R X NX hNX n e he omega (j:nat) hJN).
Local Notation E1:=(@analytic_prefix_germ_map R X NX hNX n e he omega (j:nat).+1 (ltn_ord j)).
Local Notation Gamma:=(@AnalyticCoordinateGerms.value R X NX hNX n e he omega j).
Variable D:comNzRingType.
Variable inclusion:{rmorphism D->C}.
Hypothesis hImage:is_commutative_subring_realisation
  (fun y:C=>exists beta:A1,y = pi (E1 beta)) inclusion.

(** Source for [analytic_reduction_prefix_image_step]:
    the original p(Q_(j+1)) is a finite
    simple algebra over the original Q_j,
    with generator p(gamma_j), 3.4.8(8), p. 329.
    Its coefficient and generator equations identify
    the actual original classes. All witnesses
    are local; no finite-module conclusion is assumed. *)
Theorem analytic_reduction_prefix_image_step:
  @analytic_reduction_actual_B R X B hB n e he omega I j g ->
  exists scalar:{rmorphism A->D},exists coordinate:D,
    (forall a:A,inclusion (scalar a) = pi (E0 a)) /\
    inclusion coordinate = pi Gamma /\
    is_finitely_generated_ring_submodule
      (setT:set [the lmodType A of ring_restricted_space scalar D^o]) /\
    is_generated_commutative_subring
      (fun d:D=>d = coordinate \/exists a:A,d = scalar a) setT.
Proof.
move=>hMember.
pose f1:{rmorphism A1->C}:=GRing.RMorphism.clone A1 C (pi \o E1) _.
have [rho [hTriangle hRho]]:=@commutative_ring_image_quotient A1 C D f1 inclusion hImage.
have [beta [hBeta [k hRegular]]]:=@analytic_reduction_coordinate_regular_witness
  R X B hB n e he omega hDual I j g hI hProper hMember.
have hKernel:f1 beta = 0:= (commutative_quotient_kernel hPi (E1 beta)).2 hBeta.
pose omegaY:=fun i:'I_(j:nat).+1=>@euclidean_scalar_coordinate_map R (j:nat).+1 i.
pose P:=@AnalyticPrefixCoordinates.projection R Y (j:nat).+1 omegaY (j:nat) (leqnSn (j:nat)).
pose S:=@AnalyticPrefixCoordinates.inclusion R Y (j:nat).+1 (@coordinate_basis R (j:nat).+1)
  (j:nat) (leqnSn (j:nat)).
have hP:=@AnalyticPrefixCoordinates.projection_laws R Y (j:nat).+1 omegaY (j:nat) (leqnSn (j:nat)).
have hS:=@AnalyticPrefixCoordinates.inclusion_laws R Y (j:nat).+1 (@coordinate_basis R (j:nat).+1)
  (j:nat) (leqnSn (j:nat)).
have hDualY i l:omegaY i (@coordinate_basis R (j:nat).+1 l) = if i==l then 1 else 0.
  by rewrite /omegaY /euclidean_scalar_coordinate_map /= /coordinate_basis ffunE eq_sym.
have hSplit:=@analytic_last_coordinate_prefix_split R Y (@euclidean_inner_product R (j:nat).+1)
  (@euclidean_inner_productP R (j:nat).+1) (j:nat) (@coordinate_basis R (j:nat).+1)
  (@coordinate_basisP R (j:nat).+1) (@euclidean_coordinate_orthonormal_family R (j:nat).+1)
  omegaY hDualY P S hP hS.
pose xi:=omegaY ord_max.
have hXi:=@euclidean_scalar_coordinate_bounded R (j:nat).+1 ord_max.
have [fXi [hXiValues _]]:=@weierstrass_functional_power_representative R Y NY hNY xi 1 hXi.
have hValues y:analytic_representative_value fXi y = xi y by rewrite hXiValues expr1.
have [EB [hEB [hFinite hGenerated]]]:=@regular_analytic_quotient_original_centre
  R Y Z NY NZ hNY hNZ (@coordinate_basis R (j:nat).+1 ord_max) xi S P hSplit
  fXi hXi hValues D (fun a:A1=>f1 a = 0) rho
  (@commutative_ring_kernel_ideal A1 C f1) hRho beta k hKernel hRegular.
pose scalar:{rmorphism A->D}:=GRing.RMorphism.clone A D (rho \o EB) _.
pose coordinate:D:=rho (analytic_germ fXi).
have hComposition a:E0 a = E1 (EB a).
  exact:(@analytic_adjacent_prefix_germ_composition R X NX hNX n omega (j:nat) hJN (ltn_ord j)
    (@AnalyticPrefixCoordinates.projection R X n omega (j:nat) hJN)
    (@AnalyticPrefixCoordinates.projection R X n omega (j:nat).+1 (ltn_ord j)) P E0 E1 EB
    (@AnalyticPrefixCoordinates.projection_laws R X n omega (j:nat) hJN)
    (@AnalyticPrefixCoordinates.projection_laws R X n omega (j:nat).+1 (ltn_ord j)) hP
    (@analytic_prefix_germ_map_specification R X NX hNX n e he omega (j:nat) hJN)
    (@analytic_prefix_germ_map_specification R X NX hNX n e he omega (j:nat).+1 (ltn_ord j)) hEB a).
have hCoordinate:E1 (analytic_germ fXi) = Gamma.
  apply:(@analytic_prefix_last_coordinate_germ R X NX hNX n e he omega j fXi)=>y.
  exact:hValues y.
exists scalar,coordinate;split.
- move=>a;change (inclusion (rho (EB a)) = pi (E0 a)).
  rewrite hTriangle;change (pi (E1 (EB a)) = pi (E0 a)).
  by rewrite -hComposition.
- split.
  + change (inclusion (rho (analytic_germ fXi)) = pi Gamma).
    rewrite hTriangle;change (pi (E1 (analytic_germ fXi)) = pi Gamma).
    by rewrite hCoordinate.
  by split.
Qed.
End PrefixStep.
