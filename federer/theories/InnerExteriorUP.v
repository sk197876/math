(** Federer (1969), 1.7.5, pp. 31-33: the unique graded algebra extension of
    the inner-product polarity. This specification is independent of any
    basis and imposes no finite-dimensional hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity AlgebraUP
  ExteriorAlgebra ExteriorGrading ExteriorUP GradedAlgebra
  AlternatingCoordinates AlternatingUnit ScalarCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_inner_exterior_extension]: Federer 1.7.5,
    p. 31, first paragraph: gamma is the unit-preserving graded
    algebra homomorphism extending the polarity beta. Algebra
    homomorphism laws are carried by its type. *)
Record is_inner_exterior_extension (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (gamma : algebra_map (exterior_algebra V)
      (alternating_unital_algebra h2 V (scalar_algebra R))) : Prop := {
  inner_exterior_extension_generator : forall v,
    gamma (exterior_generator v) = form_include (inner_polarity hB v);
  inner_exterior_extension_graded : preserves_grading
    (exterior_grading V) (A_star_grading V R^o) gamma
}.

(** Source for [inner_exterior_extension_unique]: Federer
    1.7.5, p. 31, uniqueness of the algebra extension, by the
    universal property of the exterior algebra. *)
Theorem inner_exterior_extension_unique (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (g h : algebra_map (exterior_algebra V)
      (alternating_unital_algebra h2 V (scalar_algebra R))) :
  is_inner_exterior_extension hB g -> is_inner_exterior_extension hB h -> g =1 h.
Proof.
move=> hg hh; apply: (exterior_algebra_ext (@exterior_algebra_exists R V)).
move=> v; by rewrite (inner_exterior_extension_generator hg)
  (inner_exterior_extension_generator hh).
Qed.
