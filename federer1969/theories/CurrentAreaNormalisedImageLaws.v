(** Federer (1969), 4.1.25, p. 383: use the exact
    graph and original domain of the opaque normalized
    differential summand. No zero extension or arbitrary
    off-domain differential enters these public laws. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading EuclideanLinearJacobian PartialFunctionUP
  CurrentAreaNormalisedImageUP CurrentAreaNormalisedImageSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section NormalisedImageLaws.
Variable R : realType.
Variables m n : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Variable f : X -> Y.
Variable xi : X -> exterior_power X m.
Local Notation u := (@CurrentAreaNormalisedImage.value R m n f xi).

(** Source for [current_area_normalised_image_at_differential]:
    the literal original value at each valid differential
    in Federer 4.1.25, p. 383. *)
Lemma current_area_normalised_image_at_differential x (D : Hom X Y) :
  has_norm_differential NX NY (fun _ => True) f x D ->
  @euclidean_linear_jacobian R m n m D != 0 ->
  partial_function_graph u x (current_area_normalised_image_coefficient xi x D).
Proof.
move=> hD hNonzero.
apply: (@CurrentAreaNormalisedImage.laws R m n f xi x _).2.
exists D; by split; last split.
Qed.

(** Source for [current_area_normalised_image_domain]: the
    summand's domain is exactly the original differential
    locus with nonzero source-top Jacobian, as in the
    univalent-differential set in Federer 4.1.25, p. 383. *)
Theorem current_area_normalised_image_domain x :
  partial_function_domain u x <-> exists D : Hom X Y,
    has_norm_differential NX NY (fun _ => True) f x D /\
    @euclidean_linear_jacobian R m n m D != 0.
Proof.
split.
- move=> [v hValue].
  have [D [hD [hNonzero _]]] :=
    (@CurrentAreaNormalisedImage.laws R m n f xi x v).1 hValue.
  exists D; by split.
- move=> [D [hD hNonzero]].
  exists (current_area_normalised_image_coefficient xi x D).
  exact: current_area_normalised_image_at_differential hD hNonzero.
Qed.
End NormalisedImageLaws.
