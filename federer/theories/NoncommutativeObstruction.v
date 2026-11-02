(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OneFormIdentification OneFormCommutator.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4, first parenthesis: the assertion for every associative
    coefficient algebra is false as printed. Any asserted extension
    would force all values of each one-form to commute. *)
Section NecessaryCondition.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable W : algebra K.
Local Notation A := (alternating_unital_algebra h2 V W).
Variable g : algebra_map (exterior_algebra (Hom V W)) A.
Hypothesis hg : forall a, g (exterior_generator a) = one_generator a.
(** Source for [exterior_extension_forces_commuting_values]: Federer (1969),
    1.4.4, p. 20, first three assertions of the coefficient-algebra
    parenthesis. In words: The printed parenthesis asserts existence for
    arbitrary associative unital coefficients, noninjectivity unless the
    coefficient dimension is one, and surjectivity for finite-dimensional V.
    These assertions need correction. Local counterexample or necessary
    correction to the printed assertion, not a claim of the book. This is a
    local correction or counterexample, not a claim proved by Federer. *)
Theorem exterior_extension_forces_commuting_values (a : Hom V W) v w :
  alg_mul W (a v) (a w) = alg_mul W (a w) (a v).
Proof.
have hs := congr1 (fun x : exterior_space (Hom V W) => g x) (exterior_generator_square a).
change (g (alg_mul (exterior_algebra (Hom V W)) (exterior_generator a) (exterior_generator a)) = g 0) in hs.
rewrite algebra_map_mul !hg linear0 in hs.
have hv := congr1 (fun f : A_star V W => f (exterior_word [:: v; w])) hs.
change (alternating_wedge h2 (alg_bilinear W) (one_generator a) (one_generator a)
  (exterior_word [:: v; w]) = 0) in hv.
rewrite one_forms_wedge_two in hv.
move/eqP: hv; by rewrite subr_eq0 => /eqP.
Qed.
End NecessaryCondition.

(** A concrete counterexample: the coefficient algebra is the free
    associative algebra on two letters, and V is the two-dimensional
    free space. No matrix presentation or extra axiom is used. *)
Section Counterexample.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Local Notation C := (Choice.clone bool _).
Local Notation V := (GRing.Lmodule.clone K (free_vector K C) _).
Local Notation W := (word_algebra K C).
(** Source for [letter_form]: Federer (1969), 1.4.4, p. 20, first three
    assertions of the coefficient-algebra parenthesis. In words: The printed
    parenthesis asserts existence for arbitrary associative unital
    coefficients, noninjectivity unless the coefficient dimension is one,
    and surjectivity for finite-dimensional V. These assertions need
    correction. Definition or construction used to formalise this passage.
    This is a local correction or counterexample, not a claim proved by
    Federer. *)
Definition letter_form : Hom V W := hom_of_linear
  (GRing.Linear.clone _ _ _ _ (free_extend (fun b : bool => word_delta K [:: b])) _).
(** Source for [letter_formE]: Federer (1969), 1.4.4, p. 20, first three
    assertions of the coefficient-algebra parenthesis. In words: The printed
    parenthesis asserts existence for arbitrary associative unital
    coefficients, noninjectivity unless the coefficient dimension is one,
    and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma letter_formE b : letter_form (delta K b) = word_delta K [:: b].
Proof. exact: free_extend_delta. Qed.
(** Source for [two_letters_do_not_commute]: Federer (1969), 1.4.4, p. 20,
    first three assertions of the coefficient-algebra parenthesis. In words:
    The printed parenthesis asserts existence for arbitrary associative
    unital coefficients, noninjectivity unless the coefficient dimension is
    one, and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma two_letters_do_not_commute :
  alg_mul W (letter_form (delta K false)) (letter_form (delta K true)) !=
  alg_mul W (letter_form (delta K true)) (letter_form (delta K false)).
Proof.
rewrite !letter_formE; change (word_mul (word_delta K [:: false]) (word_delta K [:: true]) !=
  word_mul (word_delta K [:: true]) (word_delta K [:: false])).
rewrite !word_mulE; apply/eqP => he.
have hv := congr1 (free_eval [:: false; true]) he.
change (delta K [:: false; true] [:: false; true] = delta K [:: true; false] [:: false; true]) in hv.
by move/eqP: hv; rewrite !deltaE /= oner_eq0.
Qed.
(** Source for [noncommutative_exterior_extension_impossible]: Federer
    (1969), 1.4.4, p. 20, first three assertions of the coefficient-algebra
    parenthesis. In words: The printed parenthesis asserts existence for
    arbitrary associative unital coefficients, noninjectivity unless the
    coefficient dimension is one, and surjectivity for finite-dimensional V.
    These assertions need correction. Local counterexample or necessary
    correction to the printed assertion, not a claim of the book. This is a
    local correction or counterexample, not a claim proved by Federer. *)
Theorem noncommutative_exterior_extension_impossible :
  ~ exists g : algebra_map (exterior_algebra (Hom V W)) (alternating_unital_algebra h2 V W),
      forall a, g (exterior_generator a) = one_generator a.
Proof.
move=> [g hg].
have he := @exterior_extension_forces_commuting_values K h2 V W g hg
  letter_form (delta K false) (delta K true).
by move: two_letters_do_not_commute; rewrite he eqxx.
Qed.
End Counterexample.
