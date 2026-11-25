(** Federer (1969), 4.1.8, p. 360: the scalar pairing
    defining phi_S is smooth in b. The proof localises S once
    on the first projection of the actual input support and uses
    a genuine zero-extended test. No integral representation of S
    or vector continuity of the literal test topology is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading ExteriorHomogeneousProducts AlternatingForms CurrentCoefficientNorms
  CurrentSpaces CurrentDegreeTransport SmoothTestSpaces SmoothTestEvaluation
  SmoothGlobalTranslationSealed TestGlobalTranslation TestZeroExtensionUP TestZeroExtensionSealed
  CurrentCartesianDomain CurrentCartesianCompactProjections CurrentCartesianProbe
  CurrentCartesianVerticalTranslation CurrentCartesianTranslatedSlice CurrentCartesianSliceTestSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianSliceScalarSmooth.
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

(** Source for [current_cartesian_slice_scalar_smooth]: every
    original eta pairing of phi_S has a smooth scalar
    representative on B, supporting Federer 4.1.8, p. 360.
    Its values are exactly S applied to the original slice
    tests. Every current and every original test is retained. *)
Theorem current_cartesian_slice_scalar_smooth
    (S:@current_space R h2 m A hA i) (phi:DC (i+j)) (eta:exterior_power Y j):
  exists h:Y->R^o,norm_class_all_orders hNY (@scalar_absolute_value_norm R) B h /\
    forall b (hb:B b),h b=@current_value R h2 m A hA i S (F b hb eta phi).
Proof.
have[K hK]:=smooth_test_support_bound (hEC (i+j)) phi.
have[KA [KB [hKA hKB]]]:=@current_cartesian_compact_projections R m n A B hA hB K.
pose cast:=@current_test_degree_transport R h2 (m+n) AB hAB (i+j) (j+i) (addnC i j).
pose Ext:=@TestZeroExtension.operator R Z (A_m Z R^o (j+i)) NZ FN hNZ hFN AB Full
  hFull (fun _ _=>I) (EC (j+i)) E (vc (j+i)) ev (hEC (j+i)) hE.
have hExt:=@TestZeroExtension.laws R Z (A_m Z R^o (j+i)) NZ FN hNZ hFN AB Full
  hFull (fun _ _=>I) (EC (j+i)) E (vc (j+i)) ev (hEC (j+i)) hE.
pose psi:=Ext (cast phi).
have hPsi z (hz:AB z):ev (smooth_test_inclusion hE psi) z=
    form_reindex (addnC i j) (vc (i+j) (smooth_test_inclusion (hEC (i+j)) phi) z).
  have hOriginal:=@test_zero_extension_original R Z (A_m Z R^o (j+i))
    (DC (j+i)) (@current_test_space R h2 (m+n) Full hFull (j+i)) AB Full
    (@current_test_value R h2 (m+n) AB hAB (j+i))
    (@current_test_value R h2 (m+n) Full hFull (j+i)) Ext hExt (cast phi) z hz.
  exact:(eq_trans hOriginal
    (@current_test_degree_transport_values R h2 (m+n) AB hAB (i+j) (j+i) (addnC i j) phi z)).
have[T hT]:=@current_cartesian_probe_exists R h2 m n i j A hA KA S eta.
exists (fun b=>@current_value R h2 (m+n) Full hFull (j+i) T (Tr (Q b) psi));split.
- exact:(@current_cartesian_vertical_translation_smooth R h2 m n (j+i) B hB T psi).
- move=>b hb.
  have hCut:=@current_cartesian_translated_slice_cutoff_identity R h2 m n i j A B hA hB
    K KA phi psi hKA hK hPsi b hb eta.
  have hAction:=hT (Tr (Q b) psi).
  exact:(eq_trans hAction (congr1 (@current_value R h2 m A hA i S) hCut)).
Qed.
End CurrentCartesianSliceScalarSmooth.
