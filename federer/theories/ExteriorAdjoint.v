(** Federer (1969), 1.7.6, p. 33: adjoints commute with exterior powers. The
    diagram is proved using the exterior algebra universal property. Given
    an adjoint, this identity requires no finite-dimensional hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerExterior
  InnerExteriorPositivity AdjointUP AdjointLaws
  OneFormLinear Hom AlgebraUP ExteriorUP ExteriorAlgebra
  ExteriorGrading ExteriorMaps AlternatingCoordinates AlternatingDual
  OmegaNaturality AlternatingUnit ScalarCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Adjoint.
Variable R : realFieldType.
Hypothesis h2 : (1+1 : R) != 0.
Variables V U : lmodType R.
Variable B : V -> V -> R.
Variable C : U -> U -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable f : {linear V -> U}.
Variable a : {linear U -> V}.
Hypothesis ha : is_adjoint B C f a.

(** Source for [adjoint_polarity_pullback]: Federer 1.7.6,
    p. 33, the degree-one part of the commutative diagram:
    pulling back the target polarity equals the source polarity
    composed with the adjoint. *)
Lemma adjoint_polarity_pullback y :
  A_m_dual f (inner_polarity hC y) = inner_polarity hB (a y).
Proof.
apply: one_hom_injective; apply: hom_ext => x.
have ht : map_tuple f [tuple x] = [tuple f x] by apply: val_inj.
by rewrite !one_homE A_m_dualE ht !inner_polarityE ha.
Qed.

(** Source for [adjoint_inner_exterior_diagram]: Federer 1.7.6,
    p. 33, commutativity of the gamma part of the diagram,
    before restricting the graded maps to a single degree. *)
Theorem adjoint_inner_exterior_diagram x :
  A_star_dual f (inner_exterior_extension h2 hC x) =
    inner_exterior_extension h2 hB (exterior_algebra_map a x).
Proof.
apply: (exterior_algebra_ext (@exterior_algebra_exists R U)
  (algebra_comp (@alternating_dual_algebra_map R h2 V U (scalar_algebra R) f)
    (inner_exterior_extension h2 hC))
  (algebra_comp (inner_exterior_extension h2 hB) (exterior_algebra_map a))) x => v.
change (A_star_dual f (inner_exterior_extension h2 hC (exterior_generator v)) =
  inner_exterior_extension h2 hB (exterior_algebra_map a (exterior_generator v))).
by rewrite exterior_algebra_mapE !inner_exterior_generator A_star_dual_include
  adjoint_polarity_pullback.
Qed.

(** Source for [adjoint_inner_exterior_form_diagram]: Federer
    1.7.6, p. 33, the degree-m gamma diagram: gamma_m composed
    with the exterior adjoint equals pullback composed with gamma'_m. *)
Theorem adjoint_inner_exterior_form_diagram m (y : exterior_power U m) :
  A_m_dual f (inner_exterior_form h2 hC y) =
    inner_exterior_form h2 hB (exterior_power_map a m y).
Proof.
apply: (can_inj (@form_includeK R V R^o m)).
rewrite -A_star_dual_include !inner_exterior_form_include.
change (A_star_dual f (inner_exterior_extension h2 hC (GradedComponents.component_val y)) =
  inner_exterior_extension h2 hB (exterior_algebra_map a (GradedComponents.component_val y))).
exact: adjoint_inner_exterior_diagram.
Qed.

(** Source for [exterior_power_adjoint]: Federer 1.7.6, p. 33,
    first conclusion: the exterior power of an adjoint is the
    adjoint of the exterior power, expressed by its defining equation. *)
Theorem exterior_power_adjoint m :
  is_adjoint (@exterior_inner_form R h2 V B hB m)
    (@exterior_inner_form R h2 U C hC m)
    (exterior_power_map f m) (exterior_power_map a m).
Proof.
move=> x y; rewrite /exterior_inner_form -adjoint_inner_exterior_form_diagram.
by rewrite A_m_dual_pairing.
Qed.
End Adjoint.
