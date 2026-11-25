(** Federer (1969), 1.7.5, pp. 31-32: the induced product respects the
    canonical zeroth and first exterior powers from 1.3.1. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity InnerExterior ExteriorNorm
  InnerNorm ExteriorPowers ExteriorGrading ExteriorAlgebra GradedComponents
  FiniteExteriorPowers InteriorOneDegree SimpleZeroDegree
  AlternatingCoordinates AlternatingPairing CovectorProducts OrthonormalFamilies Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section LowDegrees.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [inner_exterior_first_form]: Federer 1.7.5,
    p. 31, gamma extends the original polarity; its restriction
    to the first exterior power is beta under the canonical identification. *)
Lemma inner_exterior_first_form v :
  inner_exterior_form h2 hB (exterior_first_inclusion V v) = inner_polarity hB v.
Proof.
apply: (can_inj (@form_includeK R V R^o 1)).
by rewrite inner_exterior_form_include first_inclusion_val inner_exterior_generator.
Qed.

(** Source for [exterior_inner_first]: Federer 1.7.5, pp. 31-32, the induced
    product in degree one agrees with the original inner product on V *)
Theorem exterior_inner_first x y :
  exterior_inner_form h2 hB (exterior_first_inclusion V x) (exterior_first_inclusion V y) = B x y.
Proof.
have hx : exterior_first_inclusion V x = e_lambda (@idfun V) [tuple x].
  apply: val_inj; change (component_val (exterior_first_inclusion V x) =
    component_val (e_lambda (@idfun V) [tuple x])).
  by rewrite first_inclusion_val e_lambdaE /= exterior_word_cons exterior_word_nil wedge_unitr.
rewrite /exterior_inner_form inner_exterior_first_form hx pairing_e_lambda.
exact: inner_polarityE.
Qed.

(** Source for [exterior_inner_zeroth]: Federer 1.7.5, pp. 31-32, the
    induced product in degree zero agrees with scalar multiplication on R. *)
Theorem exterior_inner_zeroth (a b : R) :
  exterior_inner_form h2 hB (exterior_zeroth_inclusion V a) (exterior_zeroth_inclusion V b) = a*b.
Proof.
pose e := fun _ : 'I_0 => (0 : V).
have ho : orthonormal_family B e.
  move=> i; by have := ltn_ord i; rewrite ltn0.
have ht : e_lambda e (ord_tuple 0) = exterior_zeroth_inclusion V 1.
  apply: val_inj; change (component_val (e_lambda e (ord_tuple 0)) =
    component_val (exterior_zeroth_inclusion V 1)).
  by rewrite e_lambdaE zeroth_inclusion_val /exterior_scalar /= scale1r enum_ord0 /= exterior_word_nil.
have hu : exterior_inner_form h2 hB (exterior_zeroth_inclusion V 1)
    (exterior_zeroth_inclusion V 1) = 1.
  rewrite -ht -exterior_norm_square (orthonormal_product_unit_norm h2 hB ho) expr1n; by [].
have hs c : exterior_zeroth_inclusion V c = c *: exterior_zeroth_inclusion V 1.
  rewrite -linearZ; congr (exterior_zeroth_inclusion V _); change (c = c*1); exact: esym (mulr1 c).
rewrite (hs a) (hs b) (bilZl (exterior_inner_form_bilinear h2 hB 0))
  (bilZr (exterior_inner_form_bilinear h2 hB 0)) hu.
change (a*(b*1) = a*b); by rewrite mulr1.
Qed.
End LowDegrees.
