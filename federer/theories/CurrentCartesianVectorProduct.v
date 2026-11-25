(** Federer (1969), 4.1.8, p. 361: the original
    product-density coefficient is the exterior product of
    the two original block inclusions. Use only the
    existing exterior maps and their algebraic laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear AlgebraUP GradedComponents
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps
  ExteriorGrading ExteriorMaps ExteriorHomogeneousProducts
  CurrentCoefficientNorms CurrentVectorSpaces NormFiniteBilinearBound
  NormBoundedBilinearUP RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianVectorProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation P := (@euclidean_first_injection_map R m n).
Local Notation Q := (@euclidean_last_injection_map R m n).
Local Notation A := (exterior_power X i).
Local Notation B := (exterior_power Y j).
Local Notation C := (exterior_power Z (i+j)).
Local Notation NA := (@current_vector_mass R h2 m i).
Local Notation NB := (@current_vector_mass R h2 n j).
Local Notation NC := (@current_vector_mass R h2 (m+n) (i+j)).

(** Source for [current_cartesian_vector_product]: the
    displayed coefficient wedge^i P(xi) wedge wedge^j Q(eta)
    in Federer 4.1.8, p. 361. The original exterior
    operations fix this value without a new construction. *)
Definition current_cartesian_vector_product (xi:A) (eta:B):C:=
  exterior_product (exterior_power_map (hom_as_linear P) i xi)
    (exterior_power_map (hom_as_linear Q) j eta).

(** Source for [current_cartesian_vector_product_bilinear]:
    the original product-density coefficient is bilinear,
    supporting Federer 4.1.8, p. 361, by 1.3.1, p. 14. *)
Lemma current_cartesian_vector_product_bilinear:bilinear current_cartesian_vector_product.
Proof.
split=>z c a b;rewrite /current_cartesian_vector_product.
- rewrite linearP ((@exterior_product_bilinear R Z i j).1 _);by [].
- rewrite linearP ((@exterior_product_bilinear R Z i j).2 _);by [].
Qed.

(** Source for [current_cartesian_vector_product_bounded]:
    the original finite coefficient operation is bounded,
    supporting its weak measurability and local integrability
    in Federer 4.1.8, p. 361. No sharp constant is
    asserted by this supporting bound. *)
Lemma current_cartesian_vector_product_bounded:norm_bounded_bilinear NA NB NC current_cartesian_vector_product.
Proof.
have[d [e he]]:=@current_vector_finite_basis R h2 m i.
have[f [b hb]]:=@current_vector_finite_basis R h2 n j.
exact:(@norm_finite_bilinear_bounded R A B C NA NB NC
  (@current_vector_mass_real_norm R h2 m i)
  (@current_vector_mass_real_norm R h2 n j)
  (@current_vector_mass_real_norm R h2 (m+n) (i+j))
  d f e b he hb current_cartesian_vector_product current_cartesian_vector_product_bilinear).
Qed.
End CurrentCartesianVectorProduct.
