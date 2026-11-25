(** Federer (1969), 4.1.7, pp. 355–356:
    the original contraction and vector products
    on density coefficients. Their order follows
    the characteristic pairings of 1.5.1,
    pp. 21–22, rather than a choice of sign. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import AlternatingSum ScalarCoefficients BoundedHom HomogeneousHom GradedComponents Hom TensorUP Bilinear GrassmannAbbreviations ExteriorGrading
  ExteriorHomogeneousProducts AlternatingForms AlternatingProduct AlternatingPairing
  LeftInterior DualityMaps RightInterior CurrentVectorFormInterior CurrentInteriorPairing CurrentVectorContraction
  CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentVectorSpaces NormFiniteBilinearBound
  RealNormUP NormBoundedBilinearUP VectorDaniellHypotheses FiniteNormMetricPolish.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentMeasurableProductCoefficients.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Z := (fun m=>exterior_power X m).
Local Notation Y := (fun m=>A_m X R^o m).
Variables k p:nat.

(** Source for [current_density_form_contraction]:
    the density of T contracted by phi is
    the original left interior of the density
    and phi, Federer 4.1.7, pp. 355–356,
    by 1.5.1, p. 22. The cast only
    identifies the equal output degrees. *)
Definition current_density_form_contraction (z:Z (k+p)) (phi:Y k):Z p:=
  @current_vector_contraction R h2 X k p z phi.

(** Source for [current_density_form_contraction_bilinear]:
    the original contraction is bilinear,
    supporting Federer 4.1.7, pp. 355–356,
    by the proved 1.5.1 characteristic map. *)
Lemma current_density_form_contraction_bilinear:bilinear current_density_form_contraction.
Proof. exact:current_vector_contraction_bilinear. Qed.

(** Source for [current_density_form_contraction_pairing]:
    pairing the new density with psi gives
    precisely the original phi wedge psi
    action, Federer 4.1.7, pp. 355–356. *)
Lemma current_density_form_contraction_pairing z phi (psi:Y p):
  pairing (current_density_form_contraction z phi) psi=
  pairing z (form_wedge h2 (scalar_bilinear R) phi psi).
Proof. exact:current_vector_contraction_pairing. Qed.

(** Source for [current_density_vector_product]:
    the density of T wedge xi is eta wedge
    xi when T has density eta, Federer
    4.1.7, pp. 355–356. This order is
    forced by the original right interior. *)
Definition current_density_vector_product (eta:Z p) (xi:Z k):Z (k+p):=
  exterior_reindex (addnC p k) (exterior_product eta xi).

(** Source for [current_density_vector_product_bilinear]:
    the original vector product is bilinear,
    supporting Federer 4.1.7, pp. 355–356,
    through 1.3.1 and 1.5.1. *)
Lemma current_density_vector_product_bilinear:bilinear current_density_vector_product.
Proof.
split=>z c a b;rewrite /current_density_vector_product.
- rewrite ((@exterior_product_bilinear R X p k).1 z) linearP;by [].
- rewrite ((@exterior_product_bilinear R X p k).2 z) linearP;by [].
Qed.

(** Source for [current_density_vector_product_pairing]:
    the actual product density has exactly the
    original right-interior test action, Federer
    4.1.7, pp. 355–356. No sign is
    suppressed by commuting the two factors. *)
Lemma current_density_vector_product_pairing eta xi (psi:Y (k+p)):
  pairing (current_density_vector_product eta xi) psi=
  pairing eta (current_vector_form_interior xi psi).
Proof.
change (form_include psi (component_val (current_density_vector_product eta xi))=
  form_include (current_vector_form_interior xi psi) (component_val eta)).
by rewrite /current_density_vector_product exterior_reindexE exterior_productE
  current_vector_form_interior_include.
Qed.

(** Source for [current_density_form_contraction_bounded]:
    the actual coefficient operation has a finite
    mass/comass bound, supporting the local
    summability extension in Federer 4.1.7,
    pp. 355–356. A bound of one is not
    asserted for arbitrary covectors. *)
Lemma current_density_form_contraction_bounded:
  norm_bounded_bilinear (@current_vector_mass R h2 n (k+p))
    (@current_form_comass R h2 n k) (@current_vector_mass R h2 n p)
    current_density_form_contraction.
Proof.
have [d [e he]]:=@current_vector_finite_basis R h2 n (k+p).
have [f [b hb]]:=@current_form_finite_basis R h2 n k.
exact:(@norm_finite_bilinear_bounded R (Z (k+p)) (Y k) (Z p)
  (@current_vector_mass R h2 n (k+p)) (@current_form_comass R h2 n k)
  (@current_vector_mass R h2 n p) (@current_vector_mass_real_norm R h2 n (k+p))
  (@current_form_comass_real_norm R h2 n k) (@current_vector_mass_real_norm R h2 n p)
  d f e b he hb current_density_form_contraction current_density_form_contraction_bilinear).
Qed.

(** Source for [current_density_vector_product_bounded]:
    the original density product has a finite
    mass bound, sufficient for the printed
    local summability extension, Federer 4.1.7,
    pp. 355–356. *)
Lemma current_density_vector_product_bounded:
  norm_bounded_bilinear (@current_vector_mass R h2 n p)
    (@current_vector_mass R h2 n k) (@current_vector_mass R h2 n (k+p))
    current_density_vector_product.
Proof.
have [d [e he]]:=@current_vector_finite_basis R h2 n p.
have [f [b hb]]:=@current_vector_finite_basis R h2 n k.
exact:(@norm_finite_bilinear_bounded R (Z p) (Z k) (Z (k+p))
  (@current_vector_mass R h2 n p) (@current_vector_mass R h2 n k)
  (@current_vector_mass R h2 n (k+p)) (@current_vector_mass_real_norm R h2 n p)
  (@current_vector_mass_real_norm R h2 n k) (@current_vector_mass_real_norm R h2 n (k+p))
  d f e b he hb current_density_vector_product current_density_vector_product_bilinear).
Qed.
End CurrentMeasurableProductCoefficients.

(** Source for [current_vector_coefficient_separable]:
    the original finite multivector coefficient
    space is separable in mass, supporting
    the measurable products in Federer 4.1.7,
    pp. 355–356. This reuses its actual
    finite basis and 3.1.1, p. 211. *)
Lemma current_vector_coefficient_separable (R:realType) (h2:(1+1:R)!=0) n m:
  is_separable_normed_space (@current_vector_mass_real_norm R h2 n m).
Proof.
have [d [e he]]:=@current_vector_finite_basis R h2 n m.
exact:(@finite_norm_metric_separable R (exterior_power (R_n R n) m)
  (@current_vector_mass R h2 n m) (@current_vector_mass_real_norm R h2 n m) d e he).
Qed.
