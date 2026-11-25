(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP Bilinear.
From Federer Require Import AlgebraPowers AlgebraBinomial DividedPowers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, binomial display: division by n! cancels the
    binomial coefficient into the two divided powers. *)
Section DividedBinomial.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
(** Source for [divided_binomial_coefficient]: Federer (1969), 1.4.5, p. 21,
    binomial expansion and the two characteristic-polynomial displays. In
    words: The determinant of tI-f is the sum of t^(n-m)(-1)^m times the
    traces of the exterior powers of f; det(I+tf) has the corresponding
    coefficients t^m. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma divided_binomial_coefficient n i : (i <= n)%N ->
  (n`!%:R : K)^-1 * 'C(n,i)%:R = ((n-i)`!%:R : K)^-1 * (i`!%:R : K)^-1.
Proof.
move=> hi.
have hn := characteristic_zero_factorial h0 n.
have hl := characteristic_zero_factorial h0 (n-i).
have hr := characteristic_zero_factorial h0 i.
have hf : ('C(n,i)%:R : K) * ((i`!%:R : K) * ((n-i)`!%:R : K)) = n`!%:R.
  by rewrite -!natrM bin_fact.
have hc : ('C(n,i)%:R : K) = n`!%:R / ((i`!%:R : K)*((n-i)`!%:R : K)).
  by rewrite -hf mulfK // mulf_neq0.
by rewrite hc mulrA mulVf // mul1r invfM mulrC.
Qed.
Variable B : algebra K.
Hypothesis hc : commutative (alg_mul B).
Hypothesis h1 : alg_one B != 0.
(** Source for [divided_power]: Federer (1969), 1.4.5, p. 21, binomial
    expansion and the two characteristic-polynomial displays. In words: The
    determinant of tI-f is the sum of t^(n-m)(-1)^m times the traces of the
    exterior powers of f; det(I+tf) has the corresponding coefficients t^m.
    Definition or construction used to formalise this passage. *)
Definition divided_power (x : B) m := (m`!%:R : K)^-1 *: @algebra_power K B x m.
(** Source for [divided_power_scale]: Federer (1969), 1.4.5, p. 21, binomial
    expansion and the two characteristic-polynomial displays. In words: The
    determinant of tI-f is the sum of t^(n-m)(-1)^m times the traces of the
    exterior powers of f; det(I+tf) has the corresponding coefficients t^m.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma divided_power_scale c x m : divided_power (c *: x) m = c ^+ m *: divided_power x m.
Proof. by rewrite /divided_power algebra_power_scale !scalerA mulrC. Qed.
(** Source for [divided_binomial]: Federer (1969), 1.4.5, p. 21, binomial
    expansion and the two characteristic-polynomial displays. In words: The
    determinant of tI-f is the sum of t^(n-m)(-1)^m times the traces of the
    exterior powers of f; det(I+tf) has the corresponding coefficients t^m.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem divided_binomial x y n : divided_power (x+y) n =
  \sum_(i < n.+1) alg_mul B (divided_power x (n-i)) (divided_power y i).
Proof.
rewrite /divided_power (@algebra_binomial K B hc h1) scaler_sumr.
apply: eq_bigr => i _.
rewrite (bilZl (alg_bilinear B)) (bilZr (alg_bilinear B)) !scalerA.
have hi : (i <= n)%N by move: (ltn_ord i); rewrite ltnS.
by rewrite (divided_binomial_coefficient hi).
Qed.
End DividedBinomial.
