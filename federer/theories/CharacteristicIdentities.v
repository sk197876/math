(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import TraceAlgebra TraceDefinition GammaPower TracePower
  DividedBinomial TraceContraction CharacteristicPolynomial.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5: the characteristic polynomial is an actual
    polynomial whose value at t is the displayed determinant. *)
Section CharacteristicIdentities.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation D := (A h2 V V).
Local Notation G := (@Gamma_A K h2 V V (Finite.clone 'I_n _) e he).
Local Notation I_V := (hom_of_linear (linear_id V)).
Local Notation GE := (@Gamma_exterior K h2 V n e he).
(** Source for [characteristic_polynomial]: Federer (1969), 1.4.5, p. 21,
    binomial expansion and the two characteristic-polynomial displays. In
    words: The determinant of tI-f is the sum of t^(n-m)(-1)^m times the
    traces of the exterior powers of f; det(I+tf) has the corresponding
    coefficients t^m. Definition or construction used to formalise this
    passage. *)
Definition characteristic_polynomial (f : Hom V V) : {poly K} :=
  \sum_(m < n.+1) ((-1 : K)^+m * trace h2 V (GE f m)) *: 'X^(n-m).
Hypothesis h0 : [pchar K] =i pred0.
(** Source for [characteristic_polynomial_horner]: Federer (1969), 1.4.5, p.
    21, binomial expansion and the two characteristic-polynomial displays.
    In words: The determinant of tI-f is the sum of t^(n-m)(-1)^m times the
    traces of the exterior powers of f; det(I+tf) has the corresponding
    coefficients t^m. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem characteristic_polynomial_horner (f : Hom V V) t :
  (characteristic_polynomial f).[t] = det h2 he (hom_as_linear (t *: I_V-f)).
Proof.
rewrite /characteristic_polynomial horner_sum (@characteristic_polynomialE K h2 h0 V n e he f t).
apply: eq_bigr => m _; rewrite hornerZ hornerXn.
by rewrite mulrC mulrA.
Qed.
(** Federer 1.4.5: the first equality in the binomial display comes
    from linearity of Gamma; the second is the divided binomial theorem. *)
(** Source for [Gamma_characteristic_power]: Federer (1969), 1.4.5, p. 21,
    binomial expansion and the two characteristic-polynomial displays. In
    words: The determinant of tI-f is the sum of t^(n-m)(-1)^m times the
    traces of the exterior powers of f; det(I+tf) has the corresponding
    coefficients t^m. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem Gamma_characteristic_power (f : Hom V V) t :
  @divided_power K D (G (t *: I_V-f)) n = @divided_power K D (t *: G I_V-G f) n.
Proof.
congr (@divided_power K D _ n).
by rewrite (linB (linearP G)) (linZ (linearP G)).
Qed.
(** Source for [Gamma_characteristic_binomial]: Federer (1969), 1.4.5, p.
    21, binomial expansion and the two characteristic-polynomial displays.
    In words: The determinant of tI-f is the sum of t^(n-m)(-1)^m times the
    traces of the exterior powers of f; det(I+tf) has the corresponding
    coefficients t^m. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem Gamma_characteristic_binomial (f : Hom V V) t :
  @divided_power K D (G (t *: I_V-f)) n =
  \sum_(m < n.+1) t ^+ (n-m) *:
    alg_mul D (Gamma_identity h2 he (n-m)) ((-1 : K)^+m *: GE f m).
Proof.
rewrite -scaleN1r (@Gamma_binomial K h2 h0 V n e he t (-1) f).
apply: eq_bigr => m _.
by rewrite (bilZr (alg_bilinear D)) scalerA.
Qed.
(** Federer 1.4.5: apply the abbreviation trace(Gamma(g))=trace(g)
    to g=exterior_power f, as well as to endomorphisms of V. *)
(** Source for [exterior_trace]: Federer (1969), 1.4.5, p. 21, binomial
    expansion and the two characteristic-polynomial displays. In words: The
    determinant of tI-f is the sum of t^(n-m)(-1)^m times the traces of the
    exterior powers of f; det(I+tf) has the corresponding coefficients t^m.
    Definition or construction used to formalise this passage. *)
Definition exterior_trace (f : Hom V V) m : K :=
  @trace_Hom K h2 (exterior_power V m) (Finite.clone (Lambda n m) _)
    (@finite_e_lambda K n V e m) (finite_e_lambda_basis he h2 m)
    (hom_of_linear (exterior_power_map (hom_as_linear f) m)).
(** Source for [exterior_traceE]: Federer (1969), 1.4.5, p. 21, binomial
    expansion and the two characteristic-polynomial displays. In words: The
    determinant of tI-f is the sum of t^(n-m)(-1)^m times the traces of the
    exterior powers of f; det(I+tf) has the corresponding coefficients t^m.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma exterior_traceE f m : trace h2 V (GE f m) = exterior_trace f m.
Proof. exact: trace_Gamma_power. Qed.
(** Source for [characteristic_polynomial_trace]: Federer (1969), 1.4.5, p.
    21, binomial expansion and the two characteristic-polynomial displays.
    In words: The determinant of tI-f is the sum of t^(n-m)(-1)^m times the
    traces of the exterior powers of f; det(I+tf) has the corresponding
    coefficients t^m. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem characteristic_polynomial_trace (f : Hom V V) t :
  det h2 he (hom_as_linear (t *: I_V-f)) =
  \sum_(m < n.+1) (t ^+ (n-m) * (-1 : K)^+m) * exterior_trace f m.
Proof.
rewrite (@characteristic_polynomialE K h2 h0 V n e he f t).
apply: eq_bigr => m _; by rewrite exterior_traceE.
Qed.
End CharacteristicIdentities.
