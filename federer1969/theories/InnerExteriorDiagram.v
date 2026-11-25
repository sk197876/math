(** Federer (1969), 1.7.5, p. 33: the commutative diagram relating beta, its
    exterior powers, Omega and gamma. The proof uses uniqueness of the
    algebra extension, without opening its sealed construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerExteriorUP InnerExterior
  AlgebraUP ExteriorAlgebra ExteriorMaps OmegaConstruction
  AlternatingCoordinates AlternatingUnit ScalarCoefficients
  OneFormIdentification OneFormLinear Hom TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [inner_exterior_omega_diagram]: Federer
    1.7.5, p. 33, gamma equals Omega composed with the
    exterior algebra map induced by beta. The representation of
    one-forms as linear functionals is the existing canonical isomorphism. *)
Theorem inner_exterior_omega_diagram (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) x :
  inner_exterior_extension h2 hB x =
    Omega h2 V (exterior_algebra_map
      (linear_comp (GRing.Linear.clone _ _ _ _ (@one_hom R V R^o) _)
        (inner_polarity hB)) x).
Proof.
pose beta := linear_comp (GRing.Linear.clone _ _ _ _ (@one_hom R V R^o) _)
  (inner_polarity hB).
change (inner_exterior_extension h2 hB x =
  algebra_comp (Omega h2 V) (exterior_algebra_map beta) x).
apply: (exterior_algebra_ext (@exterior_algebra_exists R V)) => v.
change (inner_exterior_extension h2 hB (exterior_generator v) =
  Omega h2 V (exterior_algebra_map beta (exterior_generator v))).
rewrite inner_exterior_generator exterior_algebra_mapE Omega_generator.
change (form_include (inner_polarity hB v) =
  form_include (one_form (one_hom (inner_polarity hB v)))).
by rewrite one_homK.
Qed.
