(** Federer (1969), 4.1.8, p. 360: the complete
    original mixed separated tests determine a current on
    A x B. Use the existing full-space tensor density,
    actual compact cutoffs and actual zero extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom Tensor TensorUP TensorSealed RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormRegularityOperations NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  AlternatingForms CurrentCoefficientNorms CurrentSpaces CurrentEvaluation CurrentPointEvaluation
  SmoothFunctionSpaceSealed SmoothCompactSet SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  SmoothTestTopology SmoothFunctionTopology SmoothCompactCutoffUP SmoothCompactCutoffSealed
  CompactSupportFunctionUP SmoothOpenCutoffExistence CurrentCartesianCutoff CurrentCartesianCompactProjections
  TestTensorMapSealed TestZeroExtensionSealed TestZeroExtensionUP
  CurrentCartesianDomain CurrentCartesianTestProductSealed CurrentDegreeTransport
  CurrentCartesianLocalisedAnnihilator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianMixedAnnihilator.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n d:nat.
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set (R_n R m)) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation EC := (@current_smooth_space R h2 (m+n) AB hAB d).
Local Notation vc := (@current_smooth_value R h2 (m+n) AB hAB d).
Local Notation hEC := (@current_smooth_space_laws R h2 (m+n) AB hAB d).
Local Notation hDC := (@current_smooth_derivative_laws R h2 (m+n) AB hAB d).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB d).
Local Notation X := (R_n R m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
(** Source for [current_cartesian_mixed_annihilator_zero]: a
    current on the original open product that vanishes on
    every separated mixed test is zero, supporting the
    uniqueness in Federer 4.1.8, p. 360. The proof
    uses 4.1.3 after genuine compact localisation and zero
    extension, retaining empty domains and zero dimensions. *)
Theorem current_cartesian_mixed_annihilator_zero
    (C:@current_space R h2 (m+n) AB hAB d):
  (forall k l (e:(k+l)%N=d)
    (a:@current_test_space R h2 m A hA k) (b:@current_test_space R h2 n B hB l),
    @current_value R h2 (m+n) AB hAB d C
      (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) d e (Pure k l a b))=0)->
  forall phi:DC,@current_value R h2 (m+n) AB hAB d C phi=0.
Proof.
move=>hZero phi.
have[K hK]:=smooth_test_support_bound hEC phi.
have[KA [KB [hKA hKB]]]:=@current_cartesian_compact_projections R m n A B hA hB K.
pose u:=@SmoothCompactCutoff.value R X NX hNX m (@coordinate_basis R m) (@coordinate_basisP R m) A KA hA.
pose v:=@SmoothCompactCutoff.value R Y NY hNY n (@coordinate_basis R n) (@coordinate_basisP R n) B KB hB.
have hu:=@SmoothCompactCutoff.laws R X NX hNX m (@coordinate_basis R m) (@coordinate_basisP R m) A KA hA.
have hv:=@SmoothCompactCutoff.laws R Y NY hNY n (@coordinate_basis R n) (@coordinate_basisP R n) B KB hB.
pose CA:=@Build_smooth_compact_set R X NX hNX A
  (@real_function_support R (real_norm_metric_space hNX) u)
  (smooth_cutoff_support_in_domain hu) (smooth_cutoff_compact hu).
pose CB:=@Build_smooth_compact_set R Y NY hNY B
  (@real_function_support R (real_norm_metric_space hNY) v)
  (smooth_cutoff_support_in_domain hv) (smooth_cutoff_compact hv).
have[KC hKC]:=@current_cartesian_compact_rectangle R m n A B CA CB.
have hSupport:@real_function_support R (real_norm_metric_space hNZ)
    (fun z=>u (p z)*v (q z)) `<=` smooth_compact_carrier KC.
  rewrite hKC.
  exact:(@current_cartesian_scalar_product_support R m n A B u v CA CB
    (fun _ h=>h) (fun _ h=>h)).
pose hFull:=fun z (_:True)=>@norm_full_domain_interior R Z NZ z.
pose CF:=A_m Z R^o d.
pose NF:=@current_form_comass R h2 (m+n) d.
pose hNF:=@current_form_comass_real_norm R h2 (m+n) d.
pose Whole:=@current_smooth_space R h2 (m+n) (fun _=>True) hFull d.
pose wholeValue:=@current_smooth_value R h2 (m+n) (fun _=>True) hFull d.
pose hWhole:=@current_smooth_space_laws R h2 (m+n) (fun _=>True) hFull d.
pose DWhole:=@current_smooth_derivatives R h2 (m+n) (fun _=>True) hFull d.
pose hDWhole:=@current_smooth_derivative_laws R h2 (m+n) (fun _=>True) hFull d.
have hScalar:=@current_cartesian_scalar_product_class R m n A B hA hB u v
  (smooth_cutoff_class hu) (smooth_cutoff_class hv).
have[localise [hLocalise hContinuous]]:=@smooth_open_cutoff_exists R Z CF NZ NF hNZ hNF AB hAB
  EC Whole vc wholeValue hEC hWhole (@current_smooth_derivatives R h2 (m+n) AB hAB d)
  DWhole hDC hDWhole (fun z=>u (p z)*v (q z)) hScalar KC hSupport.
pose hR:=@scalar_absolute_value_norm R.
pose hLineFull:=fun t (_:True)=>@norm_full_domain_interior R R^o (fun t:R^o=>`|t|) t.
pose Line:=@SmoothFunctionSpace.space R R^o R^o (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
  hR hR (fun _=>True) hLineFull.
pose lineValue:=@SmoothFunctionSpace.value R R^o R^o (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
  hR hR (fun _=>True) hLineFull.
pose hLine:=@SmoothFunctionSpace.laws R R^o R^o (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
  hR hR (fun _=>True) hLineFull.
pose T:=@tensor_family R (m+n) (fun _=>smooth_test_space hLine).
pose mu:=@tensor_family_mul R (m+n) (fun _=>smooth_test_space hLine).
pose hMu:=@tensor_familyP R (m+n) (fun _=>smooth_test_space hLine).
pose W:=tensor_space T CF.
pose nu:=@tensor_inj R T CF.
pose hNu:=tensor_exists T CF.
pose F:=@TestTensorMap.value R (m+n) Line lineValue hLine CF NF hNF Whole wholeValue hWhole
  T W mu nu hMu hNu.
have hF:=@TestTensorMap.laws R (m+n) Line lineValue hLine CF NF hNF Whole wholeValue hWhole
  T W mu nu hMu hNu.
have hAll:=@current_cartesian_localised_annihilator_zero R h2 m n A B hA hB
  Line lineValue hLine d Whole wholeValue hWhole T W mu nu F hF
  u v (smooth_cutoff_class hu) (smooth_cutoff_class hv) CA CB (fun _ h=>h) (fun _ h=>h)
  localise hLocalise DWhole hDWhole hContinuous hMu hNu C hZero.
pose extension:=@TestZeroExtension.operator R Z CF NZ NF hNZ hNF AB (fun _=>True)
  hFull (fun _ _=>I) EC Whole vc wholeValue hEC hWhole.
have hExtension:=@TestZeroExtension.laws R Z CF NZ NF hNZ hNF AB (fun _=>True)
  hFull (fun _ _=>I) EC Whole vc wholeValue hEC hWhole.
have hRecover:localise (smooth_test_inclusion hWhole (extension phi))=phi.
  have[WA [hWA [hKWA hOneA]]]:=smooth_cutoff_neighbourhood_plateau hu.
  have[WB [hWB [hKWB hOneB]]]:=smooth_cutoff_neighbourhood_plateau hv.
  apply:(smooth_test_values_extensional hEC)=>z hz.
  change (smooth_test_value hEC (localise (smooth_test_inclusion hWhole (extension phi))) z=
    @current_test_value R h2 (m+n) AB hAB d phi z).
  rewrite (@hLocalise _ z hz).
  have hOriginal:=@test_zero_extension_original R Z CF (smooth_test_space hEC)
    (smooth_test_space hWhole) AB (fun _=>True) (smooth_test_value hEC) (smooth_test_value hWhole)
    extension hExtension phi z hz.
  change (wholeValue (smooth_test_inclusion hWhole (extension phi)) z=
    @current_test_value R h2 (m+n) AB hAB d phi z) in hOriginal.
  rewrite hOriginal.
  case:(pselect (smooth_compact_carrier K z))=>hKz.
  - have hFirst:smooth_compact_carrier KA (p z).
      rewrite hKA;by exists z.
    have hLast:smooth_compact_carrier KB (q z).
      rewrite hKB;by exists z.
    by rewrite /u /v (hOneA _ (hKWA _ hFirst)) (hOneB _ (hKWB _ hLast)) mul1r scale1r.
  - have hOff:=((smooth_function_compact_support_iff hEC K (smooth_test_inclusion hEC phi)).1 hK) z hKz.
    change (@current_test_value R h2 (m+n) AB hAB d phi z=0) in hOff.
    by rewrite hOff scaler0.
have hValue:=hAll (extension phi).
by rewrite hRecover in hValue.
Qed.
End CurrentCartesianMixedAnnihilator.
