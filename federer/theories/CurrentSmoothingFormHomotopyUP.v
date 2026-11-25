(** Federer (1969), 4.1.18, p. 375: independently
    specify the corresponding smoothing homotopy for
    differential forms by the original compact-kernel
    average of the old fixed-z transgression. The
    specification assumes no construction, derivative
    commutation or desired homotopy identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing CurrentSpaces
  CurrentEqualDomainSmooth CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTransgressionSealed
  CurrentTranslationHomotopy CurrentTranslations EuclideanAdditiveGroup
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws EuclideanLebesgueDimensions SummableRealFunctionUP
  MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSmoothingFormHomotopyUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!= 0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation E:=(fun d=>@current_smooth_space R h2 n Full hFull d).
Local Notation ev:=(fun d=>@current_smooth_value R h2 n Full hFull d).
Variable family:R->X->R.
Variable epsilon:R.

(** Source for [current_smoothing_form_homotopy_integrand]:
    the original fixed-z transgression coefficient
    in the corresponding form smoothing homotopy,
    Federer 4.1.18, p. 375. *)
Definition current_smoothing_form_homotopy_integrand
    (omega:E (1+m)%N) x (eta:exterior_power X m) z:R:=
  let Hz:=@current_translation_homotopy R n z in
  let hHz:=@current_translation_homotopy_laws R n z in
  let tau:=@euclidean_translation R n z in
  let hSource:=@current_homotopy_source_open R n n (fun _=>True)
    Full Full (fun y:X=>y) tau Hz hHz.1 in
  let hTarget:=@current_homotopy_target_open R n n (fun _=>True)
    Full Full (fun y:X=>y) tau Hz hHz.1 in
  family epsilon (-z)*pairing eta
    (@current_smooth_value R h2 n Full hSource m
      (@CurrentHomotopyTransgression.value R h2 n n m (fun _=>True)
        Full Full (fun y:X=>y) tau Hz hHz
        (@current_smooth_equal_domain R h2 n (1+m)%N Full Full hFull hTarget
          (erefl _) omega)) x).

(** Source for [is_current_smoothing_form_homotopy]: the
    original literal averaged-transgression law for
    the form homotopy, Federer 4.1.18, p. 375.
    Every smooth target form and point is retained. *)
Definition is_current_smoothing_form_homotopy
    (K:Hom (E (1+m)%N) (E m)):Prop:=
  forall omega x (eta:exterior_power X m),
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (real_total_integrand (current_smoothing_form_homotopy_integrand omega x eta))
      (pairing eta (ev m (K omega) x))%:E.

(** Source for [current_smoothing_form_homotopy_unique]:
    the original scalar coefficient integrals fix
    every smooth form value, so the form
    homotopy of 4.1.18, p. 375, is unique. *)
Theorem current_smoothing_form_homotopy_unique (K L:Hom (E (1+m)%N) (E m)):
  is_current_smoothing_form_homotopy K->is_current_smoothing_form_homotopy L->K= L.
Proof.
move=>hK hL;apply:hom_ext=>omega.
apply:(smooth_function_extensional (@current_smooth_space_laws R h2 n Full hFull m))=>x _.
apply:pairing_ext=>eta.
exact:(EFin_inj (measure_integral_unique (@hK omega x eta) (@hL omega x eta))).
Qed.
End CurrentSmoothingFormHomotopyUP.
