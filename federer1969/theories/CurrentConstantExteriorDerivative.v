(** Federer (1969), 4.1.6–4.1.7, pp. 353–356,
    used in 4.1.12, p. 368: the exterior
    derivative of an actual constant form vanishes.
    Reuse the original coordinate expansion and the
    already proved constant directional derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms Alternating AlternatingProduct ScalarCoefficients
  CurrentSpaces CurrentConstantFields CurrentConstantFieldDirectional SmoothFunctionSpaceLaws
  SmoothCurrentExteriorDerivative SmoothCurrentExteriorCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_constant_form_exterior_zero]:
    d of a constant original smooth form is zero,
    by the original coordinate formula in Federer
    4.1.6, p. 353, and 4.1.7, p. 356.
    This includes degree zero and empty coordinate families. *)
Theorem current_constant_form_exterior_zero (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x) phi:
  @smooth_current_exterior_derivative R h2 n m U hU
    (@current_constant_form R h2 n U hU m phi)=0.
Proof.
apply:(smooth_function_extensional (@current_smooth_space_laws R h2 n U hU m.+1))=>x hx.
apply:(can_inj (@form_includeK R (R_n R n) R^o m.+1)).
rewrite (@smooth_current_exterior_coordinate_values R h2 n m U hU _ x hx)
  (smooth_function_zero_value (@current_smooth_space_laws R h2 n U hU m.+1)) linear0.
apply:big1=>j _.
rewrite current_constant_form_directional_zero
  (smooth_function_zero_value (@current_smooth_space_laws R h2 n U hU m))
  (bil0r (@form_wedge_bilinear R h2 (R_n R n) R^o
    (fun a b=>a*b) (@scalar_bilinear R) 1%N m)).
exact:linear0.
Qed.
