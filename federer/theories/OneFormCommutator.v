(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OneFormIdentification.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [linear_four_values]: Federer (1969), 1.4.4, p. 20, first
    three assertions of the coefficient-algebra parenthesis. In words: The
    printed parenthesis asserts existence for arbitrary associative unital
    coefficients, noninjectivity unless the coefficient dimension is one,
    and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma linear_four_values (K : fieldType) (X Y : lmodType K)
    (f : {linear X -> Y}) (x1 x2 x3 x4 : X) (a b : Y) :
  f x1 = 0 -> f x2 = a -> f x3 = b -> f x4 = 0 ->
  f (x1+x2+(-x3+x4)) = a-b.
Proof. by move=> h1 h2 h3 h4; rewrite !linearD linearN h1 h2 h3 h4 add0r addr0. Qed.

(** Federer 1.4.4, first parenthesis: obstruction to the printed
    assertion for noncommutative coefficients. This calculation uses
    the actual alternating product constructed in 1.4.2. *)
Section Commutator.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Variable mu : W -> W -> W.
Hypothesis hmu : bilinear mu.
Local Notation u := (exterior_unit V).
Local Notation ev := (@exterior_generator K V).
(** Source for [Psi_two]: Federer (1969), 1.4.4, p. 20, first three
    assertions of the coefficient-algebra parenthesis. In words: The printed
    parenthesis asserts existence for arbitrary associative unital
    coefficients, noninjectivity unless the coefficient dimension is one,
    and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma Psi_two v w : Psi h2 V (exterior_word [:: v; w]) =
  tensor_inj (wedge (ev v) (ev w)) u + tensor_inj (ev v) (ev w) +
  (- tensor_inj (ev w) (ev v) + tensor_inj u (wedge (ev v) (ev w))).
Proof.
rewrite Psi_word_cons.
change (Psi_left_action v (Psi h2 V (ev w)) + Psi_right_action v (Psi h2 V (ev w)) = tensor_inj (wedge (ev v) (ev w)) u + tensor_inj (ev v) (ev w) +
  (- tensor_inj (ev w) (ev v) + tensor_inj u (wedge (ev v) (ev w)))).
rewrite PsiE (linD (Psi_left_action_linear v)) (linD (Psi_right_action_linear v)).
apply (congr2 (fun x y : tensor_space (exterior_space V) (exterior_space V) => x+y)).
- apply (congr2 (fun x y : tensor_space (exterior_space V) (exterior_space V) => x+y)).
  + exact (@Psi_left_factor K V v 1 (ev w) u (exterior_generator_homogeneous w)).
  + exact (@diagonal_left_right K V v w).
- apply (congr2 (fun x y : tensor_space (exterior_space V) (exterior_space V) => x+y)).
  + exact (@diagonal_right_left K V w v).
  + have h := @Psi_right_factor K V v 0 u (ev w) (exterior_unit_homogeneous V).
    by rewrite expr0 scale1r in h.
Qed.
(** Source for [one_generator_unit]: Federer (1969), 1.4.4, p. 20, first
    three assertions of the coefficient-algebra parenthesis. In words: The
    printed parenthesis asserts existence for arbitrary associative unital
    coefficients, noninjectivity unless the coefficient dimension is one,
    and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma one_generator_unit (a : Hom V W) : one_generator a u = 0.
Proof. rewrite -exterior_word_nil one_generator_word; exact: form_words_wrong. Qed.
(** Source for [one_generator_two]: Federer (1969), 1.4.4, p. 20, first
    three assertions of the coefficient-algebra parenthesis. In words: The
    printed parenthesis asserts existence for arbitrary associative unital
    coefficients, noninjectivity unless the coefficient dimension is one,
    and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Lemma one_generator_two (a : Hom V W) v w : one_generator a (wedge (ev v) (ev w)) = 0.
Proof.
have he : wedge (ev v) (ev w) = exterior_word [:: v; w].
  by rewrite exterior_word_cons exterior_word_cons exterior_word_nil wedge_unitr.
rewrite he one_generator_word; exact: form_words_wrong.
Qed.
(** Source for [one_forms_wedge_two]: Federer (1969), 1.4.4, p. 20, first
    three assertions of the coefficient-algebra parenthesis. In words: The
    printed parenthesis asserts existence for arbitrary associative unital
    coefficients, noninjectivity unless the coefficient dimension is one,
    and surjectivity for finite-dimensional V. These assertions need
    correction. Supporting result for the corrected coefficient statement;
    not an assertion of the printed book. This is a local correction or
    counterexample, not a claim proved by Federer. *)
Theorem one_forms_wedge_two (a b : Hom V W) v w :
  alternating_wedge h2 hmu (one_generator a) (one_generator b) (exterior_word [:: v; w]) =
  mu (a v) (b w) - mu (a w) (b v).
Proof.
pose f := paired_tensor hmu (one_generator a) (one_generator b).
change (f (Psi h2 V (exterior_word [:: v; w])) = mu (a v) (b w) - mu (a w) (b v)).
apply (eq_trans (congr1 f (Psi_two v w))).
apply (@linear_four_values K _ _ f).
- by rewrite /f paired_tensorE one_generator_two (bil0l hmu).
- by rewrite /f paired_tensorE !one_generatorE.
- by rewrite /f paired_tensorE !one_generatorE.
- by rewrite /f paired_tensorE one_generator_unit (bil0l hmu).
Qed.
End Commutator.
