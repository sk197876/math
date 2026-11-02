(** Federer (1969), 1.7.5, pp. 31 and 33: existence of the algebra extension
    gamma, via the displayed Omega diagram. Private existence proof; later
    results use the sealed extension and its defining laws. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerExteriorUP
  AlgebraUP ExteriorAlgebra ExteriorGrading ExteriorMaps GradedAlgebra
  AlternatingCoordinates AlternatingUnit ScalarCoefficients
  OmegaConstruction OneFormIdentification OneFormLinear Hom TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [inner_exterior_extension_exists]: Federer
    1.7.5, p. 31, existence of gamma. Compose the exterior map
    of beta with Omega, as in the diagram on p. 33. No basis
    or finite-dimensional hypothesis is needed. *)
Theorem inner_exterior_extension_exists (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) :
  exists gamma : algebra_map (exterior_algebra V)
    (alternating_unital_algebra h2 V (scalar_algebra R)),
    is_inner_exterior_extension hB gamma.
Proof.
pose beta := linear_comp
  (GRing.Linear.clone _ _ _ _ (@one_hom R V R^o) _) (inner_polarity hB).
exists (algebra_comp (Omega h2 V) (exterior_algebra_map beta)); constructor.
- move=> v; change (Omega h2 V (exterior_algebra_map beta (exterior_generator v)) = form_include (inner_polarity hB v)).
  rewrite exterior_algebra_mapE Omega_generator.
  change (form_include (one_form (one_hom (inner_polarity hB v))) = form_include (inner_polarity hB v)).
  by rewrite one_homK.
- move=> m x hx; apply: Omega_graded; exact: exterior_algebra_map_graded hx.
Qed.
