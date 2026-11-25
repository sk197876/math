(** Federer (1969), 1.7.8, p. 34: transfer the vector identities to
    covectors through gamma, the algebra homomorphism of 1.7.5. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior AlgebraUP ExteriorAlgebra
  ExteriorGrading GradedComponents ExteriorHomogeneousProducts AlternatingCoordinates
  AlternatingAlgebra AlternatingUnit ScalarCoefficients AlternatingPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [inner_exterior_form_reindex]: Federer 1.7.8,
    p. 34, supporting compatibility of gamma with identification
    of equal natural-number degrees. *)
Lemma inner_exterior_form_reindex (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    p q (h : p=q) (x : exterior_power V p) :
  form_reindex h (inner_exterior_form h2 hB x) =
    inner_exterior_form h2 hB (exterior_reindex h x).
Proof. by case: q / h. Qed.

(** Source for [inner_exterior_form_wedge]: Federer 1.7.8,
    p. 34, supporting transfer of wedge products to covectors.
    This is the homogeneous component of gamma's algebra-map law
    in 1.7.5, p. 31, not an additional construction. *)
Theorem inner_exterior_form_wedge (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    p q (x : exterior_power V p) (y : exterior_power V q) :
  inner_exterior_form h2 hB (exterior_product x y) =
    form_wedge h2 (scalar_bilinear R) (inner_exterior_form h2 hB x)
      (inner_exterior_form h2 hB y).
Proof.
apply: (can_inj (@form_includeK R V R^o (p+q))).
rewrite form_wedge_include !inner_exterior_form_include exterior_productE.
exact (@algebra_map_mul R (exterior_algebra V)
  (alternating_unital_algebra h2 V (scalar_algebra R))
  (inner_exterior_extension h2 hB) (component_val x) (component_val y)).
Qed.

(** Source for [pairing_reindex]: Federer 1.7.8, p. 34,
    supporting compatibility of the vector/covector pairing with
    the common identification of equal degrees. *)
Lemma pairing_reindex (R : fieldType) (V : lmodType R)
    p q (h : p=q) (x : exterior_power V p) (phi : A_m V R^o p) :
  pairing (exterior_reindex h x) (form_reindex h phi) = pairing x phi.
Proof. by case: q / h. Qed.
