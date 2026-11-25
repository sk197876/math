(** Federer (1969), 4.1.8, p. 360: the original
    linear slice operator commutes with vertical test derivatives.
    The proof uses its independent scalar pairing law, the actual
    first differential of the smooth output, the preceding distribution
    quotient and one common support-step probe. It assumes no
    continuity of the slice operator or vector topology on D. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading ExteriorHomogeneousProducts AlternatingForms CurrentCoefficientNorms
  CurrentSpaces CurrentDegreeTransport SmoothTestSpaces SmoothTestEvaluation
  SmoothGlobalTranslationSealed TestGlobalTranslation TestZeroExtensionUP TestZeroExtensionSealed
  CurrentCartesianDomain CurrentCartesianCompactProjections CurrentCartesianProbe
  CurrentCartesianVerticalTranslation CurrentCartesianTranslatedSlice CurrentCartesianSliceTestSealed
  CurrentCartesianSliceSealed CurrentCartesianSliceStepProbe CurrentCartesianVerticalDirectional
  CurrentCartesianExtendedTestDirectional TestDirectionalDifferentialValue
  DistributionDirectionalDerivative TestDirectionalValues CurrentCoefficientCompleteness
  ExteriorDifferentialCoefficients NormFiniteLinearBound SmoothCurrentExteriorDerivative
  NormDifferentialFiniteCalculus NormDifferentialLocal LinearBasis AlternatingPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianSliceDirectional.
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
Local Notation EB := (@current_smooth_space R h2 n B hB j).
Local Notation vb := (@current_smooth_value R h2 n B hB j).
Local Notation hEB := (@current_smooth_space_laws R h2 n B hB j).
Local Notation DB := (@current_test_space R h2 n B hB j).
Local Notation FB := (A_m Y R^o j).
Local Notation NB := (@current_form_comass R h2 n j).
Local Notation hNB := (@current_form_comass_real_norm R h2 n j).
Local Notation H := (fun S=>@CartesianSlice.value R h2 m n i j A B hA hB S).
Local Notation DiffC := (fun v=>@distribution_test_directional_derivative R Z (A_m Z R^o (i+j))
  NZ (@current_form_comass R h2 (m+n) (i+j)) hNZ (@current_form_comass_real_norm R h2 (m+n) (i+j))
  AB hAB (EC (i+j)) (vc (i+j)) (hEC (i+j)) (@current_smooth_derivatives R h2 (m+n) AB hAB (i+j))
  (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)) v).
Local Notation DiffB := (fun v=>@distribution_test_directional_derivative R Y FB NY NB hNY hNB
  B hB EB vb hEB (@current_smooth_derivatives R h2 n B hB j)
  (@current_smooth_derivative_laws R h2 n B hB j) v).
Local Notation Diff := (fun v=>@distribution_test_directional_derivative R Z (A_m Z R^o (j+i))
  NZ FN hNZ hFN Full hFull E ev hE (@current_smooth_derivatives R h2 (m+n) Full hFull (j+i))
  (@current_smooth_derivative_laws R h2 (m+n) Full hFull (j+i)) v).

(** Source for [current_cartesian_slice_directional_commutation]:
    differentiating the original phi_S in direction v equals
    slicing the original test differentiated in direction Qv,
    supporting Federer 4.1.8, p. 360. This equality
    holds in the genuine compact test space for every current,
    every test and every direction in the second factor. *)
Theorem current_cartesian_slice_directional_commutation
    (S:@current_space R h2 m A hA i) (phi:DC (i+j)) v:
  DiffB v (H S phi)=H S (DiffC (Q v) phi).
Proof.
apply:(smooth_test_values_extensional hEB)=>b hb.
apply:pairing_ext=>eta.
have[K hK]:=smooth_test_support_bound (hEC (i+j)) phi.
have[T hT]:=@current_cartesian_slice_step_probe_exists R h2 m n i j A B hA hB S K eta.
pose psi:=Ext (Cast phi).
have[dg [hDG hExterior]]:=@smooth_current_exterior_derivative_actual R h2 n j B hB
  (smooth_test_inclusion hEB (H S phi)) b hb.
pose coefficient:=@original_form_coefficient_map R Y R^o j eta.
have[k [basis hBasis]]:=@current_form_finite_basis R h2 n j.
have hCoefficient:=@norm_finite_linear_bounded R FB R^o NB (fun t:R^o=>`|t|) hNB
  (@scalar_absolute_value_norm R) k basis hBasis coefficient.
have hPost:=@norm_differential_postcompose R Y FB R^o NY NB (fun t:R^o=>`|t|) hNY
  B (vb (smooth_test_inclusion hEB (H S phi))) b dg coefficient hDG hCoefficient.
have hAgreement y (hy:B y):coefficient (vb (smooth_test_inclusion hEB (H S phi)) y)=
    @current_value R h2 (m+n) Full hFull (j+i) T (Tr (Q y) psi).
  exact:(eq_trans (@CartesianSlice.laws R h2 m n i j A B hA hB S phi y hy eta)
    (esym (@hT phi hK y hy))).
have hOrbit:has_norm_differential NY (fun t:R^o=>`|t|) B
    (fun y=>@current_value R h2 (m+n) Full hFull (j+i) T (Tr (Q y) psi)) b
    (hom_comp coefficient dg).
  exact:(@norm_differential_domain_agreement R Y R^o NY (fun t:R^o=>`|t|) hNY B
    (fun y=>coefficient (vb (smooth_test_inclusion hEB (H S phi)) y))
    (fun y=>@current_value R h2 (m+n) Full hFull (j+i) T (Tr (Q y) psi)) b
    (hom_comp coefficient dg) hAgreement hPost).
have hVertical:=@current_cartesian_vertical_translation_differential R h2 m n (j+i) B
  T psi b (hom_comp coefficient dg) hOrbit v.
have hDerivativeSupport:=@distribution_test_directional_derivative_compact_support R Z
  (A_m Z R^o (i+j)) NZ (@current_form_comass R h2 (m+n) (i+j)) hNZ
  (@current_form_comass_real_norm R h2 (m+n) (i+j)) AB hAB
  (EC (i+j)) (vc (i+j)) (hEC (i+j)) (@current_smooth_derivatives R h2 (m+n) AB hAB (i+j))
  (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)) (Q v) K phi hK.
have hExtension:=@current_cartesian_extended_test_directional R h2 m n i j A B hA hB phi (Q v).
have hInputAction:@current_value R h2 (m+n) Full hFull (j+i) T
    (Tr (Q b) (Diff (Q v) psi))=@current_value R h2 m A hA i S (F b hb eta (DiffC (Q v) phi)).
  have hStep:=@hT (DiffC (Q v) phi) hDerivativeSupport b hb.
  rewrite hExtension in hStep;exact:hStep.
have hOutputDerivative:=@test_directional_derivative_actual_differential R Y FB NY NB hNY hNB
  B hB EB vb hEB (@current_smooth_derivatives R h2 n B hB j)
  (@current_smooth_derivative_laws R h2 n B hB j) (H S phi) b dg hb hDG v.
have hLeft:=congr1 (pairing eta) hOutputDerivative.
have hOutput:=@CartesianSlice.laws R h2 m n i j A B hA hB S (DiffC (Q v) phi) b hb eta.
exact:(eq_trans hLeft (eq_trans hVertical (eq_trans hInputAction (esym hOutput)))).
Qed.
End CurrentCartesianSliceDirectional.
