(** Federer (1969), 4.1.8, p. 360: vertical derivatives
    of the original slice pairing are obtained by differentiating
    the input test in the corresponding last-block direction.
    These supporting laws reuse the original distribution quotient
    and uniqueness of actual directional derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormFiniteLinearBound NormRegularity NormRegularityOperations InnerNorm
  HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanBlockLinearMaps AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothTestSpaces SmoothGlobalTranslationSealed TestGlobalTranslation
  DistributionTranslationSmoothness DistributionTranslationDirectional DistributionDirectionalDerivative
  NormDifferentialDirectional NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianVerticalDirectional.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n d:nat.
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNS := (@scalar_absolute_value_norm R).
Local Notation Full := (fun _:Z=>True).
Local Notation hFull := (fun z (_:True)=>norm_full_domain_interior NZ z).
Local Notation Q := (@euclidean_last_injection_map R m n).
Local Notation E := (@current_smooth_space R h2 (m+n) Full hFull d).
Local Notation ev := (@current_smooth_value R h2 (m+n) Full hFull d).
Local Notation hE := (@current_smooth_space_laws R h2 (m+n) Full hFull d).
Local Notation D := (@current_test_space R h2 (m+n) Full hFull d).
Local Notation FN := (@current_form_comass R h2 (m+n) d).
Local Notation hFN := (@current_form_comass_real_norm R h2 (m+n) d).
Local Notation L := (@SmoothGlobalTranslation.operator R Z (A_m Z R^o d) NZ FN hNZ hFN E ev hE).
Local Notation hL := (@SmoothGlobalTranslation.laws R Z (A_m Z R^o d) NZ FN hNZ hFN E ev hE).
Local Notation Tr := (fun c=>@test_global_translation R Z (A_m Z R^o d) NZ FN hNZ hFN
  E ev hE c (L c) (hL c)).
Variable B:set Y.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.

Local Notation Diff := (fun v=>@distribution_test_directional_derivative R Z (A_m Z R^o d)
  NZ FN hNZ hFN Full hFull E ev hE
  (@current_smooth_derivatives R h2 (m+n) Full hFull d)
  (@current_smooth_derivative_laws R h2 (m+n) Full hFull d) v).

(** Source for [current_cartesian_vertical_translation_directional]:
    the exact vertical difference quotient used to differentiate
    phi_S in Federer 4.1.8, p. 360. It applies to
    every whole-space current and actual test, in every direction. *)
Theorem current_cartesian_vertical_translation_directional
    (T:@current_space R h2 (m+n) Full hFull d) (psi:D) (b v:Y):
  punctured_norm_limit (fun t:R^o=>`|t|)
    (fun t=>t^-1*(@current_value R h2 (m+n) Full hFull d T (Tr (Q (b+t*:v)) psi)-
      @current_value R h2 (m+n) Full hFull d T (Tr (Q b) psi)))
    (@current_value R h2 (m+n) Full hFull d T (Tr (Q b) (Diff (Q v) psi))).
Proof.
have h:=@distribution_translation_orbit_directional R Z (A_m Z R^o d) NZ FN hNZ hFN
  (m+n) (@coordinate_basis R (m+n)) (@coordinate_basisP R (m+n)) E ev hE
  (@current_smooth_derivatives R h2 (m+n) Full hFull d)
  (@current_smooth_derivative_laws R h2 (m+n) Full hFull d) T psi (Q b) (Q v).
move=>epsilon hEpsilon.
have[r [hr hSmall]]:=h epsilon hEpsilon.
exists r;split;first exact:hr.
move=>t ht.
have hAt:=hSmall t ht.
have hLinear:Q (b+t*:v)=(Q b:Z)+t*:(Q v:Z) by rewrite linearD linearZ.
rewrite hLinear;exact:hAt.
Qed.

(** Source for [current_cartesian_vertical_translation_differential]:
    any actual differential of the scalar vertical pairing
    has the original differentiated-test value, supporting Federer
    4.1.8, p. 360. The hypothesis specifies an actual
    differential, whose existence is supplied separately by smoothness. *)
Theorem current_cartesian_vertical_translation_differential
    (T:@current_space R h2 (m+n) Full hFull d) (psi:D) (b:Y) (P:Hom Y R^o):
  has_norm_differential NY (fun t:R^o=>`|t|) B
    (fun y=>@current_value R h2 (m+n) Full hFull d T (Tr (Q y) psi)) b P->
  forall v,P v=@current_value R h2 (m+n) Full hFull d T (Tr (Q b) (Diff (Q v) psi)).
Proof.
move=>hP v.
have hActual:=@norm_differential_directional_limit R Y R^o NY (fun t:R^o=>`|t|)
  hNY hNS B (fun y=>@current_value R h2 (m+n) Full hFull d T (Tr (Q y) psi)) b P hP v.
have hPrinted:=@current_cartesian_vertical_translation_directional T psi b v.
exact:(punctured_norm_limit_unique hNS hActual hPrinted).
Qed.
End CurrentCartesianVerticalDirectional.
