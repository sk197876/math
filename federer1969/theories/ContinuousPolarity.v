(** Public continuous-dual polarity in Federer (1969), 3.1.1, p. 209.
    The implementation is hidden; only its pairing equation is used. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom InnerProductUP InnerNorm RealNormUP
  ContinuousDualUP DifferentialGradientUP ContinuousPolarityUP
  ContinuousPolarityLaws ContinuousPolaritySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [continuous_polarity]: the polarity from X into X*
    used in the gradient paragraph of Federer 3.1.1, p. 209. *)
Definition continuous_polarity (R : realType) (V D : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  (hN : is_real_norm (inner_norm hB))
  (evaluation : Hom D (Hom V R^o)) (DN : D -> R)
  (hD : is_continuous_dual hN evaluation DN) : Hom V D :=
  @ContinuousPolarity.map R V D B hB hN evaluation DN hD.

(** Source for [continuous_polarity_pairing]: the defining equation
    of the polarity in Federer 3.1.1, p. 209. *)
Theorem continuous_polarity_pairing (R : realType) (V D : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  (hN : is_real_norm (inner_norm hB))
  (evaluation : Hom D (Hom V R^o)) (DN : D -> R)
  (hD : is_continuous_dual hN evaluation DN) u v :
  evaluation (continuous_polarity hD u) v = B v u.
Proof. exact: ContinuousPolarity.laws. Qed.

(** Source for [continuous_polarity_isomorphism]: the isomorphism
    onto the continuous real dual in Federer 3.1.1, p. 209, for a
    finite-dimensional or complete inner-product space. Linearity is
    carried by the map type; injectivity, surjectivity and preservation
    of the norm are proved from the abstract pairing and dual laws. *)
Theorem continuous_polarity_isomorphism (R : realType) (V D : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B)
  (hN : is_real_norm (inner_norm hB))
  (evaluation : Hom D (Hom V R^o)) (DN : D -> R)
  (hD : is_continuous_dual hN evaluation DN) :
  differential_gradient_space hB ->
  injective (continuous_polarity hD) /\
  (forall d : D, exists u, continuous_polarity hD u = d) /\
  (forall u, DN (continuous_polarity hD u) = inner_norm hB u).
Proof.
move=> hspace; split.
- exact: (continuous_polarity_injective hB (ContinuousPolarity.laws hD)).
- split.
  + exact: (continuous_polarity_surjective hspace hD (ContinuousPolarity.laws hD)).
  + exact: (continuous_polarity_isometric hD (ContinuousPolarity.laws hD)).
Qed.
