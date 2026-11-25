(** Federer (1969), 4.1.18, p. 375: the
    corresponding form homotopy exists on every
    original smooth form. Compose only the old
    opaque parameter transgression and compact form
    average, and prove its independent literal law.
    This composition is confined to existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal.
From Federer Require Import EuclideanBlockCoordinates Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap ExteriorGrading AlternatingForms AlternatingPairing
  CurrentSpaces CurrentDiracDensity CurrentCartesianDomain CurrentCartesianVectorProduct
  CurrentAmbientCartesianProduct CurrentEqualDomainSmooth CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyTransgressionSealed CurrentTranslationParameterHomotopy
  CurrentTranslationHomotopy CurrentTranslationTransgressionFibre
  CurrentCompactKernelFormAverageUP CurrentCompactSmoothingFormAverage
  CurrentSmoothingFormHomotopyUP SmoothingKernelUP SmoothingDilationUP
  EuclideanLebesgueDimensions SummableRealFunctionUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSmoothingFormHomotopyExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!= 0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R (n+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation FullZ:=(fun _:Z=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation AB:=(@euclidean_cartesian_set R n n Full Full).
Local Notation hAB:=(@current_cartesian_domain_open R n n Full Full hFull hFull).
Local Notation H:=(@current_translation_parameter_homotopy R n).
Local Notation q:=(@euclidean_last_block_map R n n).
Local Notation End:=(@current_translation_parameter_end R n).
Local Notation hH:=(@current_translation_parameter_homotopy_laws R n).
Local Notation hSource:=(@current_homotopy_source_open R (n+n)%N n
  (fun _=>True) FullZ Full q End H hH.1).
Local Notation hTarget:=(@current_homotopy_target_open R (n+n)%N n
  (fun _=>True) FullZ Full q End H hH.1).
Local Notation E:=(fun d=>@current_smooth_space R h2 n Full hFull d).
Local Notation ev:=(fun d=>@current_smooth_value R h2 n Full hFull d).
Local Notation ToTarget:=(@current_smooth_equal_domain R h2 n (1+m)%N
  Full Full hFull hTarget (erefl _)).
Local Notation ToProduct:=(@current_smooth_equal_domain R h2 (n+n)%N m
  FullZ AB hSource hAB (esym (@current_cartesian_full_domain R n n))).
Local Notation KH:=(@CurrentHomotopyTransgression.value R h2 (n+n)%N n m
  (fun _=>True) FullZ Full q End H hH).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation A:=(@current_compact_smoothing_form_average R h2 n
  phi family hPhi hFamily epsilon hEpsilon m).
Local Notation unit:=(@current_scalar_multivector_unit R n).

(** Source for [current_smoothing_form_homotopy_witness]:
    existence witness from the preceding opaque
    operators, supporting 4.1.18, p. 375.
    Consumers use the independently specified seal. *)
Definition current_smoothing_form_homotopy_witness:Hom (E (1+m)%N) (E m):=
  hom_comp A (hom_comp ToProduct (hom_comp KH ToTarget)).

(** Source for [current_smoothing_form_homotopy_witness_laws]:
    the smooth witness has exactly the original
    reflected-kernel fixed-z transgression integral,
    Federer 4.1.18, p. 375. *)
Theorem current_smoothing_form_homotopy_witness_laws:
  @is_current_smoothing_form_homotopy R h2 n m family epsilon
    current_smoothing_form_homotopy_witness.
Proof.
move=>omega x eta.
have hIntegral:=@current_compact_smoothing_form_average_laws R h2 n
  phi family hPhi hFamily epsilon hEpsilon m
  (ToProduct (KH (ToTarget omega))) x Logic.I eta.
have hFunction:(fun z=>family epsilon (-z)*
    pairing (@current_cartesian_vector_product R n n 0%N m unit eta)
      (@current_smooth_value R h2 (n+n)%N AB hAB m
        (ToProduct (KH (ToTarget omega))) (euclidean_block_join (z,x))))=
    @current_smoothing_form_homotopy_integrand R h2 n m family epsilon omega x eta.
  apply:funext=>z.
  rewrite current_smooth_equal_domain_values /current_smoothing_form_homotopy_integrand.
  congr (_*_).
  apply:(@current_translation_transgression_fibre R h2 n m z (ToTarget omega)).
  move=>y;by rewrite !current_smooth_equal_domain_values.
change (is_measure_integral (@euclidean_lebesgue_measure R n)
  (real_total_integrand (fun z=>family epsilon (-z)*
    pairing (@current_cartesian_vector_product R n n 0%N m unit eta)
      (@current_smooth_value R h2 (n+n)%N AB hAB m
        (ToProduct (KH (ToTarget omega))) (euclidean_block_join (z,x)))))
  (pairing eta (ev m (current_smoothing_form_homotopy_witness omega) x))%:E) in hIntegral.
by rewrite hFunction in hIntegral.
Qed.

(** Source for [current_smoothing_form_homotopy_exists]:
    the independent original form-homotopy law
    has an actual smooth linear solution,
    Federer 4.1.18, p. 375. *)
Theorem current_smoothing_form_homotopy_exists:
  exists K:Hom (E (1+m)%N) (E m),
    @is_current_smoothing_form_homotopy R h2 n m family epsilon K.
Proof.
exists current_smoothing_form_homotopy_witness.
exact:current_smoothing_form_homotopy_witness_laws.
Qed.
End CurrentSmoothingFormHomotopyExistence.
