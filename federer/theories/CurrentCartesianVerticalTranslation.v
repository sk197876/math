(** Federer (1969), 4.1.8, p. 360: evaluation of an
    arbitrary whole-space current on vertically translated tests is
    smooth in the second variables. This supporting result reuses
    the original distributional test-quotient theorem and the bounded
    linear composition law, with every exterior degree retained. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormFiniteLinearBound NormRegularity NormRegularityOperations InnerNorm
  HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanBlockLinearMaps AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothTestSpaces SmoothGlobalTranslationSealed TestGlobalTranslation
  DistributionTranslationSmoothness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianVerticalTranslation.
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

(** Source for [current_cartesian_vertical_translation_smooth]:
    the vertical-parameter current pairing is of every finite
    class, supporting phi_S in Federer 4.1.8, p. 360.
    The current need not be representable by integration, and
    the second open domain need not contain zero. *)
Theorem current_cartesian_vertical_translation_smooth
    (T:@current_space R h2 (m+n) Full hFull d) (psi:D):
  norm_class_all_orders hNY hNS B
    (fun b=>@current_value R h2 (m+n) Full hFull d T (Tr (Q b) psi)).
Proof.
have hOrbit:=@distribution_translation_orbit_smooth R (m+n) (A_m Z R^o d) FN hFN E ev hE
  (@current_smooth_derivatives R h2 (m+n) Full hFull d)
  (@current_smooth_derivative_laws R h2 (m+n) Full hFull d) T psi.
move=>k.
have hQ:norm_class hNY hNZ B Q k.
  apply:(@norm_class_linear R Y Z NY NZ hNY hNZ B Q k hB).
  exact:(@norm_finite_linear_bounded R Y Z NY NZ hNY hNZ n
    (@coordinate_basis R n) (@coordinate_basisP R n) Q).
exact:(@norm_class_compose_on R Y Z R^o NY NZ (fun t:R^o=>`|t|) hNY hNZ hNS
  B Full Q (fun c=>@current_value R h2 (m+n) Full hFull d T (Tr c psi)) k
  (fun _ _=>I) hQ (hOrbit k)).
Qed.
End CurrentCartesianVerticalTranslation.
