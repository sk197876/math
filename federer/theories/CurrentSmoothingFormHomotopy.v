(** Federer (1969), 4.1.18, p. 375: the
    corresponding original smoothing homotopy formulas
    for differential forms. Apply the compact kernel
    average to the old form homotopy, using
    its original endpoint identities and exterior
    commutation. Every smooth form is retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Bilinear Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap CurrentSpaces CurrentCartesianDomain
  CurrentAmbientCartesianProduct CurrentCartesianProjections
  CurrentEqualDomainSmooth CurrentSmoothPullbackEqualDomain
  SmoothFormPullbackSealed SmoothCurrentExteriorDerivative CurrentAboveDimension
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyGeometry CurrentHomotopySliceClass
  CurrentHomotopyTransgressionSealed CurrentHomotopyPositiveFormFormula CurrentHomotopyZeroFormFormula
  CurrentTranslationParameterHomotopy CurrentAdditionZeroFactorPullback
  CurrentCompactSmoothingFormAverage CurrentSmoothingFormAverageEndpoints
  CurrentSmoothingOperators CurrentSmoothingFormHomotopySealed CurrentSmoothingFormParameterLaw
  SmoothingKernelUP SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentSmoothingFormHomotopy.
Variable R:realType.
Hypothesis h2:(1+1:R)!= 0.
Variable n:nat.
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
Local Notation endpoints:=(@current_homotopy_endpoint_images R (n+n)%N n
  (fun _=>True) FullZ Full q End H hH.1).
Local Notation classes:=(@current_smooth_homotopy_endpoint_classes R (n+n)%N n
  (fun _=>True) FullZ Full q End H hH).
Local Notation Image:=(fun (z:Z) (_:AB z)=>Logic.I).
Local Notation E:=(fun d=>@current_smooth_space R h2 n Full hFull d).
Local Notation ToTarget:=(fun d=>@current_smooth_equal_domain R h2 n d
  Full Full hFull hTarget (erefl _)).
Local Notation ToProduct:=(fun d=>@current_smooth_equal_domain R h2 (n+n)%N d
  FullZ AB hSource hAB (esym (@current_cartesian_full_domain R n n))).
Local Notation KH:=(fun d=>@CurrentHomotopyTransgression.value R h2 (n+n)%N n d
  (fun _=>True) FullZ Full q End H hH).
Local Notation PullF:=(fun d=>@SmoothFormPullback.operator R h2 (n+n)%N n d
  FullZ Full hSource hTarget q endpoints.1 classes.1).
Local Notation PullG:=(fun d=>@SmoothFormPullback.operator R h2 (n+n)%N n d
  FullZ Full hSource hTarget End endpoints.2 classes.2).
Local Notation PullQ:=(fun d=>@SmoothFormPullback.operator R h2 (n+n)%N n d
  AB Full hAB hFull q Image
    (@current_cartesian_last_projection_smooth R n n Full Full hFull hFull)).
Local Notation PullAdd:=(fun d=>@SmoothFormPullback.operator R h2 (n+n)%N n d
  AB Full hAB hFull End Image (@current_addition_product_smooth R n)).

(** Source for [current_smoothing_form_initial_presentation]:
    the original starting pullback is unchanged
    by its canonical domain presentation, supporting
    the form homotopy of 4.1.18, p. 375. *)
Lemma current_smoothing_form_initial_presentation d (omega:E d):
  ToProduct d (PullF d (ToTarget d omega))= PullQ d omega.
Proof.
exact:(@current_smooth_pullback_equal_domain_reverse R h2 (n+n)%N n d
  FullZ AB Full Full hSource hAB hTarget hFull
  (esym (@current_cartesian_full_domain R n n)) (erefl _) q endpoints.1 Image
  classes.1 (@current_cartesian_last_projection_smooth R n n Full Full hFull hFull) omega).
Qed.

(** Source for [current_smoothing_form_final_presentation]:
    the original addition pullback is unchanged
    by its canonical domain presentation, supporting
    4.1.18, p. 375. *)
Lemma current_smoothing_form_final_presentation d (omega:E d):
  ToProduct d (PullG d (ToTarget d omega))= PullAdd d omega.
Proof.
exact:(@current_smooth_pullback_equal_domain_reverse R h2 (n+n)%N n d
  FullZ AB Full Full hSource hAB hTarget hFull
  (esym (@current_cartesian_full_domain R n n)) (erefl _) End endpoints.2 Image
  classes.2 (@current_addition_product_smooth R n) omega).
Qed.

Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation A:=(fun d=>@current_compact_smoothing_form_average R h2 n
  phi family hPhi hFamily epsilon hEpsilon d).
Local Notation K:=(fun d=>@CurrentSmoothingFormHomotopy.value R h2 n d
  phi family hPhi hFamily epsilon hEpsilon).
Local Notation P:=(fun d=>@current_smooth_smoothing R h2 n d phi family hPhi hFamily epsilon).
Local Notation d:=(fun j=>@smooth_current_exterior_derivative R h2 n j Full hFull).

(** Source for [current_smoothing_form_homotopy_positive]:
    Phi_epsilon*omega−omega= K(d omega)+d(K omega)
    in positive form degree, the corresponding
    original identity indicated in 4.1.18, p. 375,
    by 4.1.9, p. 363. *)
Theorem current_smoothing_form_homotopy_positive j (omega:E j.+1):
  P j.+1 omega-omega= K j.+1 (d j.+1 omega)+d j (K j omega).
Proof.
have hOriginal:=@current_homotopy_positive_form_formula R h2 (n+n)%N n j
  (fun _=>True) FullZ Full q End H hH (ToTarget j.+1 omega).
pose Average:=hom_comp (A j.+1) (ToProduct j.+1).
have hAverage:=congr1 Average hOriginal.
rewrite (Bilinear.linB (hom_linear Average))
  (Bilinear.linD (hom_linear Average)) in hAverage.
rewrite /Average !hom_compE current_smoothing_form_final_presentation
  current_smoothing_form_initial_presentation current_smoothing_form_average_final
  current_smoothing_form_average_initial in hAverage.
rewrite (@current_smooth_equal_domain_exterior_derivative R h2 n j.+1
  Full Full hFull hTarget (erefl _) omega) in hAverage.
rewrite -(@current_smooth_equal_domain_exterior_derivative R h2 (n+n)%N j
  FullZ AB hSource hAB (esym (@current_cartesian_full_domain R n n))
  (KH j (ToTarget j.+1 omega))) in hAverage.
rewrite -current_compact_smoothing_form_average_exterior in hAverage.
rewrite (@CurrentSmoothingFormHomotopy.parameter_average R h2 n j.+1
  phi family hPhi hFamily epsilon hEpsilon (d j.+1 omega))
  (@CurrentSmoothingFormHomotopy.parameter_average R h2 n j
  phi family hPhi hFamily epsilon hEpsilon omega).
exact:hAverage.
Qed.

(** Source for [current_smoothing_form_homotopy_zero]:
    Phi_epsilon*omega−omega= K(d omega) in zero
    form degree, the original zero-degree case
    of the form statement in 4.1.18, p. 375. *)
Theorem current_smoothing_form_homotopy_zero (omega:E 0%N):
  P 0%N omega-omega= K 0%N (d 0%N omega).
Proof.
have hOriginal:=@current_homotopy_zero_form_formula R h2 (n+n)%N n
  (fun _=>True) FullZ Full q End H hH (ToTarget 0%N omega).
pose Average:=hom_comp (A 0%N) (ToProduct 0%N).
have hAverage:=congr1 Average hOriginal.
rewrite (Bilinear.linB (hom_linear Average)) in hAverage.
rewrite /Average !hom_compE current_smoothing_form_final_presentation
  current_smoothing_form_initial_presentation current_smoothing_form_average_final
  current_smoothing_form_average_initial in hAverage.
rewrite (@current_smooth_equal_domain_exterior_derivative R h2 n 0%N
  Full Full hFull hTarget (erefl _) omega) in hAverage.
rewrite (@CurrentSmoothingFormHomotopy.parameter_average R h2 n 0%N
  phi family hPhi hFamily epsilon hEpsilon (d 0%N omega)).
exact:hAverage.
Qed.

(** Source for [current_smoothing_form_homotopy_top]: in
    positive top form degree the next exterior
    differential is zero, so only d(K omega)
    remains, supporting the full corresponding
    form statement of 4.1.18, p. 375. *)
Theorem current_smoothing_form_homotopy_top j (hTop:n= j.+1) (omega:E j.+1):
  P j.+1 omega-omega= d j (K j omega).
Proof.
rewrite current_smoothing_form_homotopy_positive.
have hAbove:(n<j.+2)%N by rewrite hTop ltnSn.
have hZero:=@current_smooth_above_dimension R h2 n j.+2 hAbove Full hFull (d j.+1 omega).
by rewrite hZero linear0 add0r.
Qed.
End CurrentSmoothingFormHomotopy.
