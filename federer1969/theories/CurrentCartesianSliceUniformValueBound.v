(** Federer (1969), 4.1.8, p. 360: the original
    first-current slice has a finite-order bound uniform in b
    and the input within one compact support step. The proof
    combines the actual cutoff smooth-dual bound with the original
    zero extension, translation and equal-degree seminorm laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading ExteriorHomogeneousProducts AlternatingForms CurrentCoefficientNorms
  CurrentSpaces CurrentDegreeTransport SmoothTestSpaces SmoothTestEvaluation
  SmoothGlobalTranslationSealed TestGlobalTranslation TestZeroExtensionUP TestZeroExtensionSealed
  CurrentCartesianDomain CurrentCartesianCompactProjections CurrentCartesianProbe
  CurrentCartesianVerticalTranslation CurrentCartesianTranslatedSlice CurrentCartesianSliceTestSealed
  SmoothCompactSet SmoothCompactDomainInclusion SmoothFunctionSupport SmoothDerivativeSeminormUP SmoothFunctionTopology
  SmoothTranslatedSupportedSeminorm TestZeroExtensionLaws
  TestZeroExtensionSupportedSeminorm CurrentDegreeTransportSeminorm CurrentCartesianProbeBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSliceUniformValueBound.
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

(** Source for [current_cartesian_slice_uniform_value_bound]:
    the scalar pairings defining phi_S have one finite-order
    input bound on every original fixed support step, supporting
    Federer 4.1.8, p. 360. The current S and
    multivector eta are arbitrary; the constant and order are
    independent of b and of the input test in that step. *)
Theorem current_cartesian_slice_uniform_value_bound
    (S:@current_space R h2 m A hA i) (K:smooth_compact_set hNZ AB)
    (eta:exterior_power Y j):
  exists r:nat,exists M0:R,0<=M0 /\forall phi:DC (i+j),
    @smooth_function_support R Z (A_m Z R^o (i+j)) NZ hNZ AB (EC (i+j)) (vc (i+j))
      (smooth_test_inclusion (hEC (i+j)) phi) `<=` smooth_compact_carrier K->
    forall b (hb:B b),`|@current_value R h2 m A hA i S (F b hb eta phi)|<=
      M0*smooth_function_derivative_seminorm
        (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)) K r
        (smooth_test_inclusion (hEC (i+j)) phi).
Proof.
have[KA [KB [hKA hKB]]]:=@current_cartesian_compact_projections R m n A B hA hB K.
have[r [J [M0 [hM0 hBound]]]]:=@current_cartesian_probe_smooth_bound R h2 m n i j A hA KA S eta.
exists r,M0;split;first exact:hM0.
move=>phi hPhi b hb.
pose cast:=@current_test_degree_transport R h2 (m+n) AB hAB (i+j) (j+i) (addnC i j).
pose Ext:=@TestZeroExtension.operator R Z (A_m Z R^o (j+i)) NZ FN hNZ hFN AB Full
  hFull (fun _ _=>I) (EC (j+i)) E (vc (j+i)) ev (hEC (j+i)) hE.
have hExt:=@TestZeroExtension.laws R Z (A_m Z R^o (j+i)) NZ FN hNZ hFN AB Full
  hFull (fun _ _=>I) (EC (j+i)) E (vc (j+i)) ev (hEC (j+i)) hE.
pose psi:=Ext (cast phi).
pose KV:=@smooth_compact_domain_inclusion R Z NZ hNZ AB Full (fun _ _=>I) K.
have hCastSupport:@smooth_function_support R Z (A_m Z R^o (j+i)) NZ hNZ AB
    (EC (j+i)) (vc (j+i)) (smooth_test_inclusion (hEC (j+i)) (cast phi))
    `<=` smooth_compact_carrier K.
  rewrite (@current_test_degree_transport_support R h2 (m+n) AB hAB (i+j) (j+i) (addnC i j) phi).
  exact:hPhi.
have hSupport:@smooth_function_support R Z (A_m Z R^o (j+i)) NZ hNZ Full E ev
    (smooth_test_inclusion hE psi) `<=` smooth_compact_carrier KV.
  exact:(@test_zero_extension_preserves_compact_bound R Z (A_m Z R^o (j+i)) NZ FN hNZ hFN
    AB Full (fun _ _=>I) (EC (j+i)) E (vc (j+i)) ev (hEC (j+i)) hE Ext hExt K
    (cast phi) hCastSupport).
have hPsi z (hz:AB z):ev (smooth_test_inclusion hE psi) z=
    form_reindex (addnC i j) (vc (i+j) (smooth_test_inclusion (hEC (i+j)) phi) z).
  have hOriginal:=@test_zero_extension_original R Z (A_m Z R^o (j+i))
    (DC (j+i)) (@current_test_space R h2 (m+n) Full hFull (j+i)) AB Full
    (@current_test_value R h2 (m+n) AB hAB (j+i))
    (@current_test_value R h2 (m+n) Full hFull (j+i)) Ext hExt (cast phi) z hz.
  exact:(eq_trans hOriginal
    (@current_test_degree_transport_values R h2 (m+n) AB hAB (i+j) (j+i) (addnC i j) phi z)).
have hCut:=@current_cartesian_translated_slice_cutoff_identity R h2 m n i j A B hA hB
  K KA phi psi hKA hPhi hPsi b hb eta.
have hFirst:=hBound (smooth_test_inclusion hE (Tr (Q b) psi)).
rewrite hCut in hFirst.
have hTranslate:=@smooth_translated_supported_seminorm_bound R Z (A_m Z R^o (j+i)) NZ FN
  hNZ hFN E ev hE (@current_smooth_derivatives R h2 (m+n) Full hFull (j+i))
  (@current_smooth_derivative_laws R h2 (m+n) Full hFull (j+i)) KV J r
  (smooth_test_inclusion hE psi) hSupport (Q b).
rewrite -(@test_global_translation_inclusion R Z (A_m Z R^o (j+i)) NZ FN hNZ hFN
  E ev hE (Q b) (L (Q b)) (hL (Q b)) psi) in hTranslate.
have hExtension:=@test_zero_extension_supported_seminorm_bound R Z (A_m Z R^o (j+i)) NZ FN
  hNZ hFN AB Full hAB hFull (fun _ _=>I) (EC (j+i)) E (vc (j+i)) ev
  (hEC (j+i)) hE (@current_smooth_derivatives R h2 (m+n) AB hAB (j+i))
  (@current_smooth_derivatives R h2 (m+n) Full hFull (j+i))
  (@current_smooth_derivative_laws R h2 (m+n) AB hAB (j+i))
  (@current_smooth_derivative_laws R h2 (m+n) Full hFull (j+i)) Ext hExt K KV r
  (cast phi) hCastSupport.
rewrite (@current_test_degree_transport_seminorm R h2 (m+n) AB hAB (i+j) (j+i)
  (addnC i j) K r phi) in hExtension.
exact:(le_trans hFirst (ler_wpM2l hM0 (le_trans hTranslate hExtension))).
Qed.
End CurrentCartesianSliceUniformValueBound.
