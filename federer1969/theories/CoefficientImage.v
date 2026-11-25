(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OneFormIdentification OmegaConstruction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4, first parenthesis: a second obstruction, even for
    commutative coefficients. The degree-zero image consists only of
    scalar multiples of the coefficient unit, not all of W. *)
Section CoefficientImage.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable W : algebra K.
Hypothesis hcomm : commutative (alg_mul W).
Local Notation O := (Omega_W h2 V hcomm).
(** Source for [Omega_W_degree_zero]: Federer (1969), 1.4.4, p. 20, first
    three assertions of the coefficient-algebra parenthesis. In words: The
    printed parenthesis asserts existence for arbitrary associative unital
    coefficients, noninjectivity unless the coefficient dimension is one,
    and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma Omega_W_degree_zero x :
  grade (A_star_grading V W) 0 (O x) =
  (exterior_augmentation (Hom V W) x : K) *: coefficient_form V (alg_one W).
Proof.
rewrite -(@graded_map_projection K (exterior_space (Hom V W)) (A_star V W)
  (exterior_grading (Hom V W)) (A_star_grading V W) O
  (@Omega_W_graded K h2 V W hcomm) 0 x).
change (O (exterior_degree 0 x) = (exterior_augmentation (Hom V W) x : K) *: coefficient_form V (alg_one W)).
rewrite exterior_degree_zero_reconstruction /exterior_scalar (linZ (linearP O)).
by rewrite Omega_W_one.
Qed.
(** Source for [Omega_W_coefficient]: Federer (1969), 1.4.4, p. 20, first
    three assertions of the coefficient-algebra parenthesis. In words: The
    printed parenthesis asserts existence for arbitrary associative unital
    coefficients, noninjectivity unless the coefficient dimension is one,
    and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Theorem Omega_W_coefficient x :
  O x (exterior_unit V) = (exterior_augmentation (Hom V W) x : K) *: alg_one W.
Proof.
have h := congr1 (fun a : A_star V W => a (exterior_unit V)) (Omega_W_degree_zero x).
change (O x (exterior_degree 0 (exterior_unit V)) =
  (exterior_augmentation (Hom V W) x : K) *: coefficient_form V (alg_one W) (exterior_unit V)) in h.
by rewrite (exterior_unit_homogeneous V) coefficient_formE exterior_augmentation_unit scale1r in h.
Qed.
(** Source for [Omega_W_surjective_requires_scalar_coefficients]: Federer
    (1969), 1.4.4, p. 20, first three assertions of the coefficient-algebra
    parenthesis. In words: The printed parenthesis asserts existence for
    arbitrary associative unital coefficients, noninjectivity unless the
    coefficient dimension is one, and surjectivity for finite-dimensional V.
    These assertions need correction. Local counterexample or necessary
    correction to the printed assertion, not a claim of the book. This is a
    local correction or counterexample, not a claim proved by Federer. *)
Theorem Omega_W_surjective_requires_scalar_coefficients :
  (forall phi : A_star V W, exists x, O x = phi) -> forall w : W, exists c : K, w = c *: alg_one W.
Proof.
move=> hs w; have [x hx] := hs (coefficient_form V w).
exists (exterior_augmentation (Hom V W) x).
have h := Omega_W_coefficient x.
by rewrite hx coefficient_formE exterior_augmentation_unit scale1r in h; symmetry.
Qed.
End CoefficientImage.
