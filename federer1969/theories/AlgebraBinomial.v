(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP Bilinear.
From Federer Require Import AlgebraPowers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5: apply the binomial theorem to his commutative
    algebra A. The following MathComp view retains exactly the given
    vectors, multiplication and unit, allowing use of exprDn. *)
Section AlgebraBinomial.
Variable K : fieldType.
Variable B : algebra K.
Hypothesis hc : commutative (alg_mul B).
Hypothesis h1 : alg_one B != 0.
(** Source for [algebra_ring]: Federer (1969), 1.4.5, p. 21, binomial
    expansion and the two characteristic-polynomial displays. In words: The
    determinant of tI-f is the sum of t^(n-m)(-1)^m times the traces of the
    exterior powers of f; det(I+tf) has the corresponding coefficients t^m.
    Definition or construction used to formalise this passage. *)
Definition algebra_ring : Type := B.
HB.instance Definition _ := GRing.Lmodule.copy algebra_ring B.
HB.instance Definition _ := @GRing.Zmodule_isComNzRing.Build algebra_ring
  (alg_one B) (alg_mul B) (@alg_assoc K B) hc (@alg_unitl K B)
  (bilDl (alg_bilinear B)) h1.
(** Source for [algebra_power_ring]: Federer (1969), 1.4.5, p. 21, binomial
    expansion and the two characteristic-polynomial displays. In words: The
    determinant of tI-f is the sum of t^(n-m)(-1)^m times the traces of the
    exterior powers of f; det(I+tf) has the corresponding coefficients t^m.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma algebra_power_ring (x : algebra_ring) m : @algebra_power K B x m = x ^+ m.
Proof. by elim: m => [|m ih] //=; rewrite ih exprS. Qed.
(** Source for [algebra_binomial]: Federer (1969), 1.4.5, p. 21, binomial
    expansion and the two characteristic-polynomial displays. In words: The
    determinant of tI-f is the sum of t^(n-m)(-1)^m times the traces of the
    exterior powers of f; det(I+tf) has the corresponding coefficients t^m.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem algebra_binomial (x y : B) n :
  @algebra_power K B (x+y) n = \sum_(i < n.+1) ('C(n,i)%:R : K) *:
    alg_mul B (@algebra_power K B x (n-i)) (@algebra_power K B y i).
Proof.
rewrite !(algebra_power_ring) exprDn.
apply: eq_bigr => i _.
by rewrite scaler_nat !algebra_power_ring.
Qed.
End AlgebraBinomial.
