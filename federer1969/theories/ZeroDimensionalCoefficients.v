(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OmegaConstruction CoefficientImage CoefficientCounterexample.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4, first parenthesis: the printed non-injectivity
    assertion also needs V<>0. For V=0 and W=K x K, Omega is injective
    although W has dimension two. *)
Section ZeroDimensionalCoefficients.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Local Notation V := (coordinate_space K 0).
Local Notation W := (coefficient_pair_algebra K).
Local Notation M := (Hom V W).
Local Notation O := (Omega_W h2 V (@coefficient_pair_commutative K)).
(** Source for [zero_coordinate_vector]: Federer (1969), 1.4.4, p. 20, first
    three assertions of the coefficient-algebra parenthesis. In words: The
    printed parenthesis asserts existence for arbitrary associative unital
    coefficients, noninjectivity unless the coefficient dimension is one,
    and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma zero_coordinate_vector (v : V) : v = 0.
Proof. apply/ffunP=> i; have := ltn_ord i; by rewrite ltn0. Qed.
(** Source for [zero_coordinate_Hom]: Federer (1969), 1.4.4, p. 20, first
    three assertions of the coefficient-algebra parenthesis. In words: The
    printed parenthesis asserts existence for arbitrary associative unital
    coefficients, noninjectivity unless the coefficient dimension is one,
    and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma zero_coordinate_Hom (a : M) : a = 0.
Proof. apply: hom_ext => v; by rewrite (zero_coordinate_vector v) linear0 hom_zeroE. Qed.
(** Source for [zero_Hom_exterior]: Federer (1969), 1.4.4, p. 20, first
    three assertions of the coefficient-algebra parenthesis. In words: The
    printed parenthesis asserts existence for arbitrary associative unital
    coefficients, noninjectivity unless the coefficient dimension is one,
    and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma zero_Hom_exterior x : x = (exterior_augmentation M x : K) *: exterior_unit M.
Proof.
elim/exterior_word_induction: x => [|x y hx hy|a x hx|s].
- by rewrite linear0 scale0r.
- rewrite linearD; change (x+y = ((exterior_augmentation M x : K)+(exterior_augmentation M y : K)) *: exterior_unit M).
  by rewrite scalerDl -hx -hy.
- rewrite linearZ; change (a *: x = (a*(exterior_augmentation M x : K)) *: exterior_unit M).
  by rewrite -scalerA -hx.
case: s => [|a s].
- by rewrite exterior_word_nil exterior_augmentation_unit scale1r.
- rewrite exterior_augmentation_word /word_degree_zero scale0r exterior_word_cons (zero_coordinate_Hom a).
  by rewrite linear0 (bil0l (wedge_bilinear M)).
Qed.
(** Source for [zero_domain_Omega_pair_injective]: Federer (1969), 1.4.4, p.
    20, first three assertions of the coefficient-algebra parenthesis. In
    words: The printed parenthesis asserts existence for arbitrary
    associative unital coefficients, noninjectivity unless the coefficient
    dimension is one, and surjectivity for finite-dimensional V. These
    assertions need correction. Local counterexample or necessary correction
    to the printed assertion, not a claim of the book. This is a local
    correction or counterexample, not a claim proved by Federer. *)
Theorem zero_domain_Omega_pair_injective : injective O.
Proof.
move=> x y hxy.
have h := congr1 (fun a : A_star V W => (a (exterior_unit V)).1) hxy.
rewrite !Omega_W_coefficient in h.
change ((exterior_augmentation M x : K)*1 = (exterior_augmentation M y : K)*1) in h.
rewrite !mulr1 in h; by rewrite (zero_Hom_exterior x) (zero_Hom_exterior y) h.
Qed.

(** Source for [coefficient_pair_basis]: Federer (1969), 1.4.4, p. 20, first
    three assertions of the coefficient-algebra parenthesis. In words: The
    printed parenthesis asserts existence for arbitrary associative unital
    coefficients, noninjectivity unless the coefficient dimension is one,
    and surjectivity for finite-dimensional V. These assertions need
    correction. Definition or construction used to formalise this passage.
    This is a local correction or counterexample, not a claim proved by
    Federer. *)
Definition coefficient_pair_basis (b : bool) : W := if b then (1,0) else (0,1).
(** Source for [coefficient_pair_basisP]: Federer (1969), 1.4.4, p. 20,
    first three assertions of the coefficient-algebra parenthesis. In words:
    The printed parenthesis asserts existence for arbitrary associative
    unital coefficients, noninjectivity unless the coefficient dimension is
    one, and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma coefficient_pair_basisP : is_basis coefficient_pair_basis.
Proof.
apply: finite_basis_criterion.
- move=> c; rewrite big_bool /coefficient_pair_basis.
  move=> h b; have h1 := congr1 (@fst K K) h; have h2' := congr1 (@snd K K) h.
  change (c true*1+c false*0=0) in h1.
  change (c true*0+c false*1=0) in h2'.
  rewrite mulr1 mulr0 addr0 in h1; rewrite mulr1 mulr0 add0r in h2'.
  by case: b.
- move=> [a b]; exists (fun i => if i then a else b).
  rewrite big_bool /coefficient_pair_basis.
  change ((a,b)=(a*1+b*0,a*0+b*1)); by rewrite !mulr1 !mulr0 addr0 add0r.
Qed.
(** Source for [coefficient_pair_vector_space]: Federer (1969), 1.4.4, p.
    20, first three assertions of the coefficient-algebra parenthesis. In
    words: The printed parenthesis asserts existence for arbitrary
    associative unital coefficients, noninjectivity unless the coefficient
    dimension is one, and surjectivity for finite-dimensional V. These
    assertions need correction. Definition or construction used to formalise
    this passage. This is a local correction or counterexample, not a claim
    proved by Federer. *)
Definition coefficient_pair_vector_space : vectType K := finite_basis_vect coefficient_pair_basisP.
(** Source for [coefficient_pair_dimension]: Federer (1969), 1.4.4, p. 20,
    first three assertions of the coefficient-algebra parenthesis. In words:
    The printed parenthesis asserts existence for arbitrary associative
    unital coefficients, noninjectivity unless the coefficient dimension is
    one, and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Theorem coefficient_pair_dimension : dim coefficient_pair_vector_space = 2%N.
Proof. by rewrite /coefficient_pair_vector_space finite_basis_dimension card_bool. Qed.
End ZeroDimensionalCoefficients.
