(** Federer (1969), 4.1.18, p. 375: public
    parameter-average characterisation of the original
    form homotopy. This is a relation between
    already opaque operators; it selects no witness
    and assumes no existence or formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap CurrentSpaces CurrentCartesianDomain
  CurrentAmbientCartesianProduct CurrentEqualDomainSmooth CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyTransgressionSealed CurrentTranslationParameterHomotopy
  CurrentCompactSmoothingFormAverage SmoothingKernelUP SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSmoothingFormParameterLaw.
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

(** Source for [is_current_smoothing_form_parameter_average]:
    averaging the original time transgression over
    the compact kernel, the corresponding form
    construction of 4.1.18, p. 375. *)
Definition is_current_smoothing_form_parameter_average
    (K:Hom (E (1+m)%N) (E m)):Prop:=
  forall omega,K omega= A (ToProduct (KH (ToTarget omega))).
End CurrentSmoothingFormParameterLaw.
