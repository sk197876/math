(** Federer (1969), 4.1.8, p. 360: differentiating
    the whole-space test used for the slice agrees with
    zero-extending the original differentiated test. This supporting
    equality reuses the actual zero-extension and equal-degree laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading ExteriorHomogeneousProducts AlternatingForms CurrentCoefficientNorms
  CurrentSpaces CurrentDegreeTransport SmoothTestSpaces SmoothTestEvaluation
  SmoothGlobalTranslationSealed TestGlobalTranslation TestZeroExtensionUP TestZeroExtensionSealed
  CurrentCartesianDomain CurrentCartesianCompactProjections CurrentCartesianProbe
  CurrentCartesianVerticalTranslation CurrentCartesianTranslatedSlice CurrentCartesianSliceTestSealed
  DistributionDirectionalDerivative TestZeroExtensionDirectional CurrentDegreeTransportDirectional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianExtendedTestDirectional.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation Full := (fun _:Z=>True).
Local Notation hFull := (fun z (_:True)=>norm_full_domain_interior NZ z).
Local Notation EC := (fun k=>@current_smooth_space R h2 (m+n) AB hAB k).
Local Notation vc := (fun k=>@current_smooth_value R h2 (m+n) AB hAB k).
Local Notation hEC := (fun k=>@current_smooth_space_laws R h2 (m+n) AB hAB k).
Local Notation DC := (fun k=>@current_test_space R h2 (m+n) AB hAB k).
Local Notation E := (@current_smooth_space R h2 (m+n) Full hFull (j+i)).
Local Notation ev := (@current_smooth_value R h2 (m+n) Full hFull (j+i)).
Local Notation hE := (@current_smooth_space_laws R h2 (m+n) Full hFull (j+i)).
Local Notation FN := (@current_form_comass R h2 (m+n) (j+i)).
Local Notation hFN := (@current_form_comass_real_norm R h2 (m+n) (j+i)).
Local Notation Q := (@euclidean_last_injection_map R m n).
Local Notation L := (@SmoothGlobalTranslation.operator R Z (A_m Z R^o (j+i)) NZ FN hNZ hFN E ev hE).
Local Notation hL := (@SmoothGlobalTranslation.laws R Z (A_m Z R^o (j+i)) NZ FN hNZ hFN E ev hE).
Local Notation Tr := (fun c=>@test_global_translation R Z (A_m Z R^o (j+i)) NZ FN hNZ hFN
  E ev hE c (L c) (hL c)).
Local Notation F := (fun (b:R_n R n) (hb:B b)=>@CartesianSliceTest.value R h2 m n A B hA hB i j b hb).

Local Notation Cast := (@current_test_degree_transport R h2 (m+n) AB hAB (i+j) (j+i) (addnC i j)).
Local Notation Ext := (@TestZeroExtension.operator R Z (A_m Z R^o (j+i)) NZ FN hNZ hFN AB Full
  hFull (fun _ _=>I) (EC (j+i)) E (vc (j+i)) ev (hEC (j+i)) hE).
Local Notation DiffC := (fun k v=>@distribution_test_directional_derivative R Z (A_m Z R^o k)
  NZ (@current_form_comass R h2 (m+n) k) hNZ (@current_form_comass_real_norm R h2 (m+n) k)
  AB hAB (EC k) (vc k) (hEC k) (@current_smooth_derivatives R h2 (m+n) AB hAB k)
  (@current_smooth_derivative_laws R h2 (m+n) AB hAB k) v).
Local Notation Diff := (fun v=>@distribution_test_directional_derivative R Z (A_m Z R^o (j+i))
  NZ FN hNZ hFN Full hFull E ev hE (@current_smooth_derivatives R h2 (m+n) Full hFull (j+i))
  (@current_smooth_derivative_laws R h2 (m+n) Full hFull (j+i)) v).

(** Source for [current_cartesian_extended_test_directional]: the
    original test, cast to the equal contraction degree
    and zero-extended, retains every directional derivative needed
    for phi_S in Federer 4.1.8, p. 360.
    No domain value or support is changed by the identification. *)
Theorem current_cartesian_extended_test_directional (phi:DC (i+j)) v:
  Ext (Cast (DiffC (i+j) v phi))=Diff v (Ext (Cast phi)).
Proof.
have hCast:=@current_test_degree_transport_directional R h2 (m+n) AB hAB
  (i+j) (j+i) (addnC i j) phi v.
have hExt:=@TestZeroExtension.laws R Z (A_m Z R^o (j+i)) NZ FN hNZ hFN AB Full
  hFull (fun _ _=>I) (EC (j+i)) E (vc (j+i)) ev (hEC (j+i)) hE.
have hDerivative:=@test_zero_extension_directional_commutes R Z (A_m Z R^o (j+i)) NZ FN
  hNZ hFN AB Full hAB (fun _ _=>I) (EC (j+i)) E (vc (j+i)) ev (hEC (j+i)) hE
  (@current_smooth_derivatives R h2 (m+n) AB hAB (j+i))
  (@current_smooth_derivatives R h2 (m+n) Full hFull (j+i))
  (@current_smooth_derivative_laws R h2 (m+n) AB hAB (j+i))
  (@current_smooth_derivative_laws R h2 (m+n) Full hFull (j+i)) Ext hExt hFull v (Cast phi).
exact:(eq_trans (congr1 Ext hCast) hDerivative).
Qed.
End CurrentCartesianExtendedTestDirectional.
