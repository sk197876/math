(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OneFormIdentification OmegaConstruction CoefficientImage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4, first parenthesis: W=K x K with its ordinary
    coordinatewise multiplication is a concrete commutative coefficient
    algebra for which the asserted epimorphism does not hold. *)
Section CoefficientPair.
Variable K : fieldType.
Local Notation W := (GRing.Lmodule.clone K (K^o * K^o)%type _).
(** Source for [coefficient_pair_mul]: Federer (1969), 1.4.4, p. 20, first
    three assertions of the coefficient-algebra parenthesis. In words: The
    printed parenthesis asserts existence for arbitrary associative unital
    coefficients, noninjectivity unless the coefficient dimension is one,
    and surjectivity for finite-dimensional V. These assertions need
    correction. Definition or construction used to formalise this passage.
    This is a local correction or counterexample, not a claim proved by
    Federer. *)
Definition coefficient_pair_mul (x y : W) : W := (x.1*y.1, x.2*y.2).
(** Source for [coefficient_pair_bilinear]: Federer (1969), 1.4.4, p. 20,
    first three assertions of the coefficient-algebra parenthesis. In words:
    The printed parenthesis asserts existence for arbitrary associative
    unital coefficients, noninjectivity unless the coefficient dimension is
    one, and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma coefficient_pair_bilinear : bilinear coefficient_pair_mul.
Proof.
split.
- move=> x c y z.
  change (((c*y.1+z.1)*x.1, (c*y.2+z.2)*x.2) =
    (c*(y.1*x.1)+z.1*x.1, c*(y.2*x.2)+z.2*x.2)).
  by rewrite !mulrDl !mulrA.
- move=> x c y z.
  change ((x.1*(c*y.1+z.1), x.2*(c*y.2+z.2)) =
    (c*(x.1*y.1)+x.1*z.1, c*(x.2*y.2)+x.2*z.2)).
  by rewrite !mulrDr [x.1*(c*y.1)]mulrCA [x.2*(c*y.2)]mulrCA.
Qed.
(** Source for [coefficient_pair_associative]: Federer (1969), 1.4.4, p. 20,
    first three assertions of the coefficient-algebra parenthesis. In words:
    The printed parenthesis asserts existence for arbitrary associative
    unital coefficients, noninjectivity unless the coefficient dimension is
    one, and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma coefficient_pair_associative : associative coefficient_pair_mul.
Proof. by move=> [x1 x2] [y1 y2] [z1 z2]; rewrite /coefficient_pair_mul /= !mulrA. Qed.
(** Source for [coefficient_pair_unit_left]: Federer (1969), 1.4.4, p. 20,
    first three assertions of the coefficient-algebra parenthesis. In words:
    The printed parenthesis asserts existence for arbitrary associative
    unital coefficients, noninjectivity unless the coefficient dimension is
    one, and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma coefficient_pair_unit_left : left_id (1,1) coefficient_pair_mul.
Proof. by move=> [x1 x2]; rewrite /coefficient_pair_mul /= !mul1r. Qed.
(** Source for [coefficient_pair_unit_right]: Federer (1969), 1.4.4, p. 20,
    first three assertions of the coefficient-algebra parenthesis. In words:
    The printed parenthesis asserts existence for arbitrary associative
    unital coefficients, noninjectivity unless the coefficient dimension is
    one, and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma coefficient_pair_unit_right : right_id (1,1) coefficient_pair_mul.
Proof. by move=> [x1 x2]; rewrite /coefficient_pair_mul /= !mulr1. Qed.
(** Source for [coefficient_pair_algebra]: Federer (1969), 1.4.4, p. 20,
    first three assertions of the coefficient-algebra parenthesis. In words:
    The printed parenthesis asserts existence for arbitrary associative
    unital coefficients, noninjectivity unless the coefficient dimension is
    one, and surjectivity for finite-dimensional V. These assertions need
    correction. Definition or construction used to formalise this passage.
    This is a local correction or counterexample, not a claim proved by
    Federer. *)
Definition coefficient_pair_algebra : algebra K := @Algebra K W coefficient_pair_mul (1,1)
  coefficient_pair_bilinear coefficient_pair_associative coefficient_pair_unit_left coefficient_pair_unit_right.
(** Source for [coefficient_pair_commutative]: Federer (1969), 1.4.4, p. 20,
    first three assertions of the coefficient-algebra parenthesis. In words:
    The printed parenthesis asserts existence for arbitrary associative
    unital coefficients, noninjectivity unless the coefficient dimension is
    one, and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma coefficient_pair_commutative : commutative (alg_mul coefficient_pair_algebra).
Proof. by move=> [x1 x2] [y1 y2]; change ((x1*y1,x2*y2)=(y1*x1,y2*x2)); rewrite [x1*y1]mulrC [x2*y2]mulrC. Qed.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
(** Source for [coefficient_pair_not_surjective]: Federer (1969), 1.4.4, p.
    20, first three assertions of the coefficient-algebra parenthesis. In
    words: The printed parenthesis asserts existence for arbitrary
    associative unital coefficients, noninjectivity unless the coefficient
    dimension is one, and surjectivity for finite-dimensional V. These
    assertions need correction. Local counterexample or necessary correction
    to the printed assertion, not a claim of the book. This is a local
    correction or counterexample, not a claim proved by Federer. *)
Theorem coefficient_pair_not_surjective :
  ~ (forall phi : A_star V coefficient_pair_algebra, exists x,
    Omega_W h2 V coefficient_pair_commutative x = phi).
Proof.
move=> hs.
have [c hc] := @Omega_W_surjective_requires_scalar_coefficients K h2 V
  coefficient_pair_algebra coefficient_pair_commutative hs (1,0).
change ((1,0) = (c*1,c*1)) in hc; rewrite !mulr1 in hc.
have h1 := congr1 (@fst K K) hc; have h0 := congr1 (@snd K K) hc.
change (1=c) in h1; change (0=c) in h0.
by move: (eq_trans h1 (esym h0)) => /eqP; rewrite oner_eq0.
Qed.
End CoefficientPair.
