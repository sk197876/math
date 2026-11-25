(** Federer (1969), 4.1.8, p. 360: the original first
    slice is recovered from a vertical translate of a whole-space
    extension. This supporting identity uses the actual sealed test
    slice and the original smooth interior and pullback. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormOpenDomainLaws NormFiniteLinearBound InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading ExteriorMaps ExteriorHomogeneousProducts AlternatingForms AlternatingDual
  CurrentCoefficientNorms CurrentSpaces CurrentVectorSpaces CurrentVectorFormInterior
  SmoothConstantSealed SmoothCurrentVectorInterior SmoothFormPullbackUP SmoothFormPullbackSealed
  SmoothCompactSet SmoothCutoffReplacement SmoothCutoffSupportedTest SmoothTestSpaces
  SmoothFunctionSpaceLaws SmoothFunctionSupport SmoothGlobalTranslationSealed
  TestGlobalTranslation TestGlobalTranslationLaws CurrentCartesianDomain
  CurrentCartesianAffineSlice CurrentCartesianProbe CurrentCartesianSliceTestSealed
  CurrentCartesianSliceTestSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianTranslatedSlice.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation Full := (fun _:Z=>True).
Local Notation hFull := (fun z (_:True)=>norm_full_domain_interior NZ z).
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation P := (@euclidean_first_injection_map R m n).
Local Notation Q := (@euclidean_last_injection_map R m n).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation EA := (@current_smooth_space R h2 m A hA i).
Local Notation va := (@current_smooth_value R h2 m A hA i).
Local Notation hEA := (@current_smooth_space_laws R h2 m A hA i).
Local Notation E := (fun k=>@current_smooth_space R h2 (m+n) Full hFull k).
Local Notation ev := (fun k=>@current_smooth_value R h2 (m+n) Full hFull k).
Local Notation hE := (fun k=>@current_smooth_space_laws R h2 (m+n) Full hFull k).
Local Notation D := (fun k=>@current_test_space R h2 (m+n) Full hFull k).
Local Notation EC := (@current_smooth_space R h2 (m+n) AB hAB (i+j)).
Local Notation vc := (@current_smooth_value R h2 (m+n) AB hAB (i+j)).
Local Notation hEC := (@current_smooth_space_laws R h2 (m+n) AB hAB (i+j)).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation VN := (@current_vector_mass R h2 (m+n) j).
Local Notation hVN := (@current_vector_mass_real_norm R h2 (m+n) j).
Local Notation V := (@current_vector_smooth_space R h2 (m+n) Full hFull j).
Local Notation vv := (@current_vector_smooth_value R h2 (m+n) Full hFull j).
Local Notation hV := (@current_vector_smooth_space_laws R h2 (m+n) Full hFull j).
Local Notation C0 := (@SmoothConstant.operator R Z (exterior_power Z j) NZ VN hNZ hVN
  Full hFull V vv hV).
Local Notation M := (@smooth_current_vector_interior R h2 (m+n) j i Full hFull).
Local Notation hImage := (fun a (_:A a)=>I).
Local Notation hPSmooth := (@current_cartesian_first_injection_smooth R m n A hA).
Local Notation Pull := (@SmoothFormPullback.operator R h2 m (m+n) i A Full hA hFull P
  hImage hPSmooth).
Local Notation L := (@SmoothGlobalTranslation.operator R Z (A_m Z R^o (j+i)) NZ
  (@current_form_comass R h2 (m+n) (j+i)) hNZ
  (@current_form_comass_real_norm R h2 (m+n) (j+i)) (E (j+i)) (ev (j+i)) (hE (j+i))).
Local Notation hL := (@SmoothGlobalTranslation.laws R Z (A_m Z R^o (j+i)) NZ
  (@current_form_comass R h2 (m+n) (j+i)) hNZ
  (@current_form_comass_real_norm R h2 (m+n) (j+i)) (E (j+i)) (ev (j+i)) (hE (j+i))).
Local Notation Tr := (fun c=>@test_global_translation R Z (A_m Z R^o (j+i)) NZ
  (@current_form_comass R h2 (m+n) (j+i)) hNZ
  (@current_form_comass_real_norm R h2 (m+n) (j+i)) (E (j+i)) (ev (j+i)) (hE (j+i))
  c (L c) (hL c)).
Local Notation F := (fun (b:R_n R n) (hb:B b)=>@CartesianSliceTest.value R h2 m n A B hA hB i j b hb).

(** Source for [current_cartesian_translated_slice_smooth_identity]:
    the original first-variable form in Federer 4.1.8, p. 360,
    is the constant-vector interior of a vertical translate,
    pulled back under P. Any actual whole-space test agreeing
    with the input on A times B gives this same identity. *)
Theorem current_cartesian_translated_slice_smooth_identity (phi:DC) (psi:D (j+i)):
  (forall z,AB z->ev (j+i) (smooth_test_inclusion (hE (j+i)) psi) z=
    form_reindex (addnC i j) (vc (smooth_test_inclusion hEC phi) z))->
  forall b (hb:B b) eta,
    Pull (M (C0 (exterior_power_map (hom_as_linear Q) j eta))
      (smooth_test_inclusion (hE (j+i)) (Tr (Q b) psi)))=
    smooth_test_inclusion hEA (F b hb eta phi).
Proof.
move=>hPsi b hb eta.
apply:(smooth_function_extensional hEA)=>a ha.
pose xi:=C0 (exterior_power_map (hom_as_linear Q) j eta).
pose input:=smooth_test_inclusion (hE (j+i)) (Tr (Q b) psi).
have hDifferential:=@norm_differential_linear R X Z NX NZ hNX hNZ A a P (@hA a ha)
  (@norm_finite_linear_bounded R X Z NX NZ hNX hNZ m
    (@coordinate_basis R m) (@coordinate_basisP R m) P).
have hPull:=@smooth_form_pullback_values R m (m+n) i A Full (E i) EA (ev i) va P Pull
  (@SmoothFormPullback.laws R h2 m (m+n) i A Full hA hFull P hImage hPSmooth)
  (M xi input) a P ha hDifferential.
have hInterior:=@smooth_current_vector_interior_values R h2 (m+n) j i Full hFull
  xi input (P a) I.
have hConstant:vv xi (P a)=exterior_power_map (hom_as_linear Q) j eta.
  exact:(@SmoothConstant.laws R Z (exterior_power Z j) NZ VN hNZ hVN Full hFull
    V vv hV (exterior_power_map (hom_as_linear Q) j eta) (P a) I).
have hInput:ev (j+i) input (P a)=form_reindex (addnC i j)
    (vc (smooth_test_inclusion hEC phi) (@euclidean_block_join R m n (a,b))).
  rewrite /input (@test_global_translation_values R Z (A_m Z R^o (j+i)) NZ
    (@current_form_comass R h2 (m+n) (j+i)) hNZ
    (@current_form_comass_real_norm R h2 (m+n) (j+i)) (E (j+i)) (ev (j+i))
    (hE (j+i)) (Q b) psi (P a)) -current_cartesian_join_affine.
  exact:(hPsi _ (@current_cartesian_affine_slice_image R m n A B b hb a ha)).
rewrite hConstant hInput in hInterior.
rewrite hInterior in hPull.
exact:(eq_trans hPull (esym ((@CartesianSliceTest.laws R h2 m n A B hA hB i j b hb).2
  eta phi a ha))).
Qed.

(** Source for [current_cartesian_translated_slice_cutoff_identity]:
    a single first-projection cutoff preserves all original
    first-variable tests in a fixed support step, supporting
    Federer 4.1.8, p. 360. The equality is in the actual
    test space, before applying an arbitrary current S. *)
Theorem current_cartesian_translated_slice_cutoff_identity
    (K:smooth_compact_set hNZ AB) (KA:smooth_compact_set hNX A)
    (phi:DC) (psi:D (j+i)):
  smooth_compact_carrier KA=p @` smooth_compact_carrier K->
  @smooth_function_support R Z (A_m Z R^o (i+j)) NZ hNZ AB EC vc
    (smooth_test_inclusion hEC phi) `<=` smooth_compact_carrier K->
  (forall z,AB z->ev (j+i) (smooth_test_inclusion (hE (j+i)) psi) z=
    form_reindex (addnC i j) (vc (smooth_test_inclusion hEC phi) z))->
  forall b (hb:B b) eta,
    @smooth_cutoff_replacement R X (A_m X R^o i) NX (@current_form_comass R h2 m i)
      hNX (@current_form_comass_real_norm R h2 m i) m (@coordinate_basis R m)
      (@coordinate_basisP R m) A hA EA va hEA KA
      (Pull (M (C0 (exterior_power_map (hom_as_linear Q) j eta))
        (smooth_test_inclusion (hE (j+i)) (Tr (Q b) psi))))=F b hb eta phi.
Proof.
move=>hKA hPhi hPsi b hb eta.
rewrite (@current_cartesian_translated_slice_smooth_identity phi psi hPsi b hb eta).
apply:(@smooth_cutoff_replacement_fixes_supported_test R X (A_m X R^o i) NX
  (@current_form_comass R h2 m i) hNX (@current_form_comass_real_norm R h2 m i)
  m (@coordinate_basis R m) (@coordinate_basisP R m) A hA EA va hEA KA (F b hb eta phi)).
exact:(@current_cartesian_slice_test_fixed_support R h2 m n i j A B hA hB K KA
  hKA phi hPhi b hb eta).
Qed.
End CurrentCartesianTranslatedSlice.
