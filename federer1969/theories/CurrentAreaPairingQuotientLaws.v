(** Federer (1969), 4.1.25, p. 383: the scalar
    area quotient agrees with the original normalized
    vector pairing on its domain. At a critical
    differential both the raw exterior image and the
    auxiliary scalar quotient are zero. This keeps the
    original vector summand's exceptional domain distinct. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal ring.
From Federer Require Import Hom Bilinear RealNormUP RealFunctionalNormUP
  NormDifferentialUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness ExteriorGrading ExteriorMaps AlternatingForms
  AlternatingPairing CurrentCoefficientNorms CurrentDualNorm
  EuclideanLinearJacobian PartialFunctionUP
  CurrentTopImageMass CurrentAreaNormalisedImageUP
  CurrentAreaNormalisedImageSealed CurrentAreaNormalisedImageLaws
  CurrentAreaNormalisedImageMass CurrentAreaPairingQuotientUP
  CurrentAreaPairingQuotientSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section AreaPairingQuotientLaws.
Variable R : realType.
Variables m n : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Variables (f:X->Y) (xi:X->exterior_power X m) (a:A_m Y R^o m).
Local Notation q := (@CurrentAreaPairingQuotient.value R m n f xi a).
Local Notation u := (@CurrentAreaNormalisedImage.value R m n f xi).
Local Notation coefficient := (@current_area_pairing_quotient_coefficient R m n xi a).

(** Source for [current_area_pairing_quotient_at_differential]:
    every actual differential gives the prescribed scalar
    quotient used in 4.1.25, p. 383. No
    nonzero-Jacobian condition is imposed on this auxiliary. *)
Lemma current_area_pairing_quotient_at_differential x (D:Hom X Y) :
  has_norm_differential NX NY setT f x D ->
  partial_function_graph q x (coefficient x D)%:E.
Proof.
move=>hD;apply:(@CurrentAreaPairingQuotient.laws R m n f xi a x _).2.
by exists D;split.
Qed.

(** Source for [current_area_pairing_quotient_domain]:
    the auxiliary's full original differential domain,
    supporting the weighted-area application in 4.1.25,
    p. 383, even on a critical set of positive measure. *)
Theorem current_area_pairing_quotient_domain x :
  partial_function_domain q x <-> norm_differentiable_at NX NY setT f x.
Proof.
split.
- move=>[z hz].
  have [D [hD _]]:=(@CurrentAreaPairingQuotient.laws R m n f xi a x z).1 hz.
  by exists D.
- move=>[D hD];exists (coefficient x D)%:E.
  exact:current_area_pairing_quotient_at_differential hD.
Qed.

(** Source for [current_area_pairing_quotient_critical]:
    scalar zero is assigned at critical differentials
    solely in the auxiliary quotient of the proof
    of 4.1.25, p. 383. *)
Lemma current_area_pairing_quotient_critical x (D:Hom X Y) :
  has_norm_differential NX NY setT f x D ->
  @euclidean_linear_jacobian R m n m D=0 -> partial_function_graph q x 0%E.
Proof.
move=>hD hZero.
have h:=current_area_pairing_quotient_at_differential hD.
by rewrite /current_area_pairing_quotient_coefficient hZero invr0 mul0r in h.
Qed.

(** Source for [current_area_pairing_quotient_normalised_value]:
    pairing the original valid normalized summand agrees
    with the auxiliary scalar quotient, supporting the
    full-fibre sum in 4.1.25, p. 383. *)
Theorem current_area_pairing_quotient_normalised_value x v :
  partial_function_graph u x v -> partial_function_graph q x (pairing v a)%:E.
Proof.
move=>hValue.
have [D [hD [hNonzero <-]]]:=
  (@CurrentAreaNormalisedImage.laws R m n f xi x v).1 hValue.
have h:=current_area_pairing_quotient_at_differential hD.
rewrite /current_area_normalised_image_coefficient
  (Bilinear.bilZl (@pairing_bilinear R Y R^o m));exact:h.
Qed.

(** Source for [current_area_pairing_quotient_times_jacobian]:
    multiplying the auxiliary by J_m f recovers the
    original paired exterior image at every differential,
    including critical differentials, in 4.1.25, p. 383. *)
Theorem current_area_pairing_quotient_times_jacobian
    (h2:(1+1:R)!=0) x (D:Hom X Y) :
  coefficient x D*@euclidean_linear_jacobian R m n m D =
    pairing (exterior_power_map (hom_as_linear D) m (xi x)) a.
Proof.
case:(eqVneq (@euclidean_linear_jacobian R m n m D) 0)=>hJ.
- rewrite /current_area_pairing_quotient_coefficient hJ mulr0
    (@current_top_image_singular_zero R h2 m n D (xi x) hJ).
  symmetry;exact:(Bilinear.lin0 ((@pairing_bilinear R Y R^o m).1 a)).
- rewrite /current_area_pairing_quotient_coefficient.
  transitivity (((@euclidean_linear_jacobian R m n m D)^-1*
    @euclidean_linear_jacobian R m n m D)*
      pairing (exterior_power_map (hom_as_linear D) m (xi x)) a).
  + ring.
  + by rewrite (mulVf hJ) mul1r.
Qed.

(** Source for [current_area_pairing_quotient_coefficient_bound]:
    the auxiliary is bounded by mass(xi) times the
    fixed covector's comass in 4.1.25, p. 383.
    This is integrable for the original compact summable
    field and needs no lower positive Jacobian bound. *)
Theorem current_area_pairing_quotient_coefficient_bound
    (h2:(1+1:R)!=0) x (D:Hom X Y) :
  has_norm_differential NX NY setT f x D ->
  `|coefficient x D| <= @current_vector_mass R h2 m m (xi x)*
    @current_form_comass R h2 n m a.
Proof.
move=>hD.
case:(eqVneq (@euclidean_linear_jacobian R m n m D) 0)=>hJ.
- rewrite /current_area_pairing_quotient_coefficient hJ invr0 mul0r normr0.
  exact:mulr_ge0
    (real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 m m).1 (xi x))
    (real_seminorm_nonnegative (@current_form_comass_real_norm R h2 n m).1 a).
- pose v:=@current_area_normalised_image_coefficient R m n xi x D.
  have hValue:partial_function_graph u x v:=
    @current_area_normalised_image_at_differential R m n f xi x D hD hJ.
  have hMass:=@current_area_normalised_image_mass R h2 m n f xi x v hValue.
  have hPair:=real_functional_norm_bound (@current_mass_pairing_norm R h2 n m v) a.
  rewrite hMass /v /current_area_normalised_image_coefficient in hPair.
  move:hPair; rewrite PairingLinear.pairing_rightE -PairingLinear.pairing_leftE
    linearZ /= =>hPair.
  exact:hPair.
Qed.
End AreaPairingQuotientLaws.
