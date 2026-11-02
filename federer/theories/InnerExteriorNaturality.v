(** Federer (1969), 1.7.5, pp. 31-32: compatibility of the induced form with
    an isometric inclusion, supporting the finite-dimensional reduction of
    the positivity proof. This is also the orthogonal special case of 1.7.6,
    p. 34. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerExteriorUP InnerExterior
  OrthogonalMaps OneFormLinear Hom AlgebraUP ExteriorUP ExteriorAlgebra
  ExteriorGrading ExteriorMaps AlternatingCoordinates AlternatingDual
  OmegaNaturality AlternatingUnit ScalarCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Naturality.
Variable R : realFieldType.
Hypothesis h2 : (1+1 : R) != 0.
Variables V U : lmodType R.
Variable B : V -> V -> R.
Variable C : U -> U -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable f : {linear V -> U}.
Hypothesis hf : is_orthogonal_map B C f.

(** Source for [orthogonal_polarity_pullback]: Federer
    1.7.5, pp. 31-32, supporting compatibility of the polarity
    with an orthogonal inclusion, evaluated on generating vectors. *)
Lemma orthogonal_polarity_pullback y :
  A_m_dual f (inner_polarity hC (f y)) = inner_polarity hB y.
Proof.
apply: one_hom_injective; apply: hom_ext => x.
have ht : map_tuple f [tuple x] = [tuple f x] by apply: val_inj.
by rewrite !one_homE A_m_dualE ht !inner_polarityE hf.
Qed.

(** Source for [inner_exterior_extension_orthogonal_natural]:
    Federer 1.7.5, pp. 31-32, supporting naturality: pulling
    back gamma of the exterior image gives the source gamma. *)
Lemma inner_exterior_extension_orthogonal_natural x :
  A_star_dual f (inner_exterior_extension h2 hC (exterior_algebra_map f x)) =
    inner_exterior_extension h2 hB x.
Proof.
apply: (exterior_algebra_ext (@exterior_algebra_exists R V)
  (algebra_comp (@alternating_dual_algebra_map R h2 V U (scalar_algebra R) f)
    (algebra_comp (inner_exterior_extension h2 hC) (exterior_algebra_map f)))
  (inner_exterior_extension h2 hB)) x => v.
change (A_star_dual f (inner_exterior_extension h2 hC
  (exterior_algebra_map f (exterior_generator v))) =
  inner_exterior_extension h2 hB (exterior_generator v)).
by rewrite exterior_algebra_mapE !inner_exterior_generator A_star_dual_include
  orthogonal_polarity_pullback.
Qed.

(** Source for [inner_exterior_form_orthogonal_natural]:
    Federer 1.7.5, pp. 31-32, degree-m form of the preceding
    compatibility, used for finite-dimensional reduction. *)
Lemma inner_exterior_form_orthogonal_natural m (x : exterior_power V m) :
  A_m_dual f (inner_exterior_form h2 hC (exterior_power_map f m x)) =
    inner_exterior_form h2 hB x.
Proof.
apply: (can_inj (@form_includeK R V R^o m)).
rewrite -A_star_dual_include !inner_exterior_form_include.
change (A_star_dual f (inner_exterior_extension h2 hC
  (exterior_algebra_map f (GradedComponents.component_val x))) =
  inner_exterior_extension h2 hB (GradedComponents.component_val x)).
exact: inner_exterior_extension_orthogonal_natural.
Qed.

(** Source for [exterior_inner_orthogonal_natural]: Federer
    1.7.5, p. 32, the induced bilinear form agrees under an
    orthogonal inclusion. This statement precedes positivity and
    therefore does not presuppose an inner product on exterior powers. *)
Theorem exterior_inner_orthogonal_natural m (x y : exterior_power V m) :
  exterior_inner_form h2 hC (exterior_power_map f m x) (exterior_power_map f m y) =
    exterior_inner_form h2 hB x y.
Proof.
by rewrite /exterior_inner_form -A_m_dual_pairing inner_exterior_form_orthogonal_natural.
Qed.
End Naturality.
