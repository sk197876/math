(** Federer (1969), 4.1.18, p. 374: independent
    original scalar integral law for averaging smooth
    product-form coefficients over the compact kernel.
    Continuity, smoothness and existence are proved later. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap EuclideanBlockCoordinates ExteriorGrading AlternatingForms AlternatingPairing
  CurrentSpaces CurrentDiracDensity CurrentCartesianDomain CurrentCartesianVectorProduct
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws MeasureIntegralUP MeasureIntegralUniqueness
  EuclideanLebesgueDimensions SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCompactKernelFormAverageUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n q j:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R q).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R q)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variable U:set Y.
Hypothesis hU:forall x,U x->norm_domain_interior NY U x.
Local Notation AB:=(@euclidean_cartesian_set R n q Full U).
Local Notation hAB:=(@current_cartesian_domain_open R n q Full U hFull hU).
Local Notation F:=(@current_smooth_space R h2 (n+q) AB hAB (0+j)).
Local Notation fv:=(@current_smooth_value R h2 (n+q) AB hAB (0+j)).
Local Notation E:=(@current_smooth_space R h2 q U hU j).
Local Notation ev:=(@current_smooth_value R h2 q U hU j).
Local Notation unit:=(@current_scalar_multivector_unit R n).
Variable w:X->R.

(** Source for [current_compact_kernel_form_integrand]: the
    literal parameter coefficient of the averaged original
    transgression, supporting 4.1.18, p. 374. *)
Definition current_compact_kernel_form_integrand (phi:F) x
    (eta:exterior_power Y j) z:R:=
  w z*pairing (@current_cartesian_vector_product R n q 0%N j unit eta)
    (fv phi (euclidean_block_join (z,x))).

(** Source for [is_current_compact_kernel_form_average]:
    original smooth product-form averaging for 4.1.18,
    p. 374, specified without a chosen current,
    cutoff, convolution representation or desired bounds. *)
Definition is_current_compact_kernel_form_average (A:Hom F E):Prop:=
  forall phi x,U x->forall eta:exterior_power Y j,
    is_measure_integral (@euclidean_lebesgue_measure R n)
      (real_total_integrand (current_compact_kernel_form_integrand phi x eta))
      (pairing eta (ev (A phi) x))%:E.

(** Source for [current_compact_kernel_form_average_unique]:
    scalar integral uniqueness and exterior separation
    determine the original averaged form, supporting
    Federer 4.1.18, p. 374. *)
Theorem current_compact_kernel_form_average_unique (A B:Hom F E):
  is_current_compact_kernel_form_average A ->
  is_current_compact_kernel_form_average B ->A=B.
Proof.
move=>hA hB;apply:hom_ext=>phi.
apply:(smooth_function_extensional (@current_smooth_space_laws R h2 q U hU j))=>x hx.
apply:pairing_ext=>eta.
have hEqual:=measure_integral_unique (@hA phi x hx eta) (@hB phi x hx eta).
by injection hEqual.
Qed.
End CurrentCompactKernelFormAverageUP.
