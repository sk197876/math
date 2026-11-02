(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import TraceAlgebra TraceComponents TraceDefinition GammaPower
  AlgebraPowers AlgebraBinomial DividedPowers DividedBinomial TracePower TraceContraction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5, binomial theorem and characteristic polynomial.
    The determinant remains the intrinsic top-exterior-power scalar
    of 1.3.4 throughout. *)
Section CharacteristicPolynomial.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Hypothesis h0 : [pchar K] =i pred0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation D := (A h2 V V).
Local Notation G := (@Gamma_A K h2 V V (Finite.clone 'I_n _) e he).
Local Notation I_V := (hom_of_linear (linear_id V)).
(** Source for [Gamma_exterior]: Federer (1969), 1.4.5, p. 21, binomial
    expansion and the two characteristic-polynomial displays. In words: The
    determinant of tI-f is the sum of t^(n-m)(-1)^m times the traces of the
    exterior powers of f; det(I+tf) has the corresponding coefficients t^m.
    Definition or construction used to formalise this passage. *)
Definition Gamma_exterior (f : Hom V V) m : D :=
  @Gamma_power_A K h2 V V n e he m (hom_of_linear (exterior_power_map (hom_as_linear f) m)).
(** Source for [Gamma_dividedE]: Federer (1969), 1.4.5, p. 20, divided-power
    display and following natural isomorphisms. In words: The divided m-th
    power of Gamma(f) is the sum of omega_lambda tensored with the m-th
    exterior image of e_lambda, and equals Gamma of that exterior map.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma Gamma_dividedE f m : @divided_power K D (G f) m = Gamma_exterior f m.
Proof. exact (@Gamma_divided_power K h2 V V n e he f m (characteristic_zero_factorial h0 m)). Qed.
(** Source for [Gamma_identity_power]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma Gamma_identity_power m : Gamma_exterior I_V m = Gamma_identity h2 he m.
Proof.
rewrite /Gamma_exterior /Gamma_identity; congr (@Gamma_power_A K h2 V V n e he m _).
apply: hom_ext => xi; apply: val_inj.
change (exterior_algebra_map (hom_as_linear I_V) (\val xi) = \val xi).
by rewrite (exterior_algebra_map_eq (g := linear_id V)) // exterior_algebra_map_id.
Qed.
(** Source for [Gamma_exterior_homogeneous]: Federer (1969), 1.4.5, p. 20,
    divided-power display and following natural isomorphisms. In words: The
    divided m-th power of Gamma(f) is the sum of omega_lambda tensored with
    the m-th exterior image of e_lambda, and equals Gamma of that exterior
    map. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma Gamma_exterior_homogeneous f m : homogeneous (A_grading h2 V V) m (Gamma_exterior f m).
Proof. exact: A_component_homogeneous. Qed.
(** Source for [Gamma_binomial]: Federer (1969), 1.4.5, p. 21, binomial
    expansion and the two characteristic-polynomial displays. In words: The
    determinant of tI-f is the sum of t^(n-m)(-1)^m times the traces of the
    exterior powers of f; det(I+tf) has the corresponding coefficients t^m.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem Gamma_binomial s t (f : Hom V V) :
  @divided_power K D (G (s *: I_V + t *: f)) n =
  \sum_(m < n.+1) (s ^+ (n-m) * t ^+ m) *:
    alg_mul D (Gamma_identity h2 he (n-m)) (Gamma_exterior f m).
Proof.
rewrite (linD (linearP G)) !(linZ (linearP G)) (@divided_binomial K h0 D (@A_commutative K h2 V V) (A_unit_nonzero h2 V)).
apply: eq_bigr => m _.
have hs : @divided_power K D (s *: G I_V) (n-m) =
    s ^+ (n-m) *: Gamma_identity h2 he (n-m).
  exact (eq_trans (@divided_power_scale K D s (G I_V) (n-m))
    (congr1 (fun x : D => s ^+ (n-m) *: x)
      (eq_trans (@Gamma_dividedE I_V (n-m)) (@Gamma_identity_power (n-m))))).
have ht : @divided_power K D (t *: G f) m = t ^+ m *: Gamma_exterior f m.
  exact (eq_trans (@divided_power_scale K D t (G f) m)
    (congr1 (fun x : D => t ^+ m *: x) (@Gamma_dividedE f m))).
apply (eq_trans (congr2 (alg_mul D) hs ht)).
by rewrite (bilZl (alg_bilinear D)) (bilZr (alg_bilinear D)) scalerA.
Qed.
(** Source for [trace_Gamma_complement]: Federer (1969), 1.4.5, p. 21,
    binomial expansion and the two characteristic-polynomial displays. In
    words: The determinant of tI-f is the sum of t^(n-m)(-1)^m times the
    traces of the exterior powers of f; det(I+tf) has the corresponding
    coefficients t^m. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma trace_Gamma_complement f m : (m <= n)%N ->
  trace h2 V (alg_mul D (Gamma_identity h2 he (n-m)) (Gamma_exterior f m)) =
  trace h2 V (Gamma_exterior f m).
Proof.
move=> hm; rewrite (@A_commutative K h2 V V).
by rewrite (@trace_contraction K h2 V n e he m (n-m) (Gamma_exterior f m) (Gamma_exterior_homogeneous f m)) binn scale1r.
Qed.
(** Source for [determinant_binomial]: Federer (1969), 1.4.5, p. 21,
    binomial expansion and the two characteristic-polynomial displays. In
    words: The determinant of tI-f is the sum of t^(n-m)(-1)^m times the
    traces of the exterior powers of f; det(I+tf) has the corresponding
    coefficients t^m. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem determinant_binomial s t (f : Hom V V) :
  det h2 he (hom_as_linear (s *: I_V + t *: f)) =
  \sum_(m < n.+1) (s ^+ (n-m) * t ^+ m) * trace h2 V (Gamma_exterior f m).
Proof.
rewrite -(@trace_divided_top_power K h2 V n e he (s *: I_V+t *: f) (characteristic_zero_factorial h0 n)).
change (trace h2 V (@divided_power K D (G (s *: I_V+t *: f)) n) =
  \sum_(m < n.+1) (s ^+ (n-m) * t ^+ m) * trace h2 V (Gamma_exterior f m)).
rewrite Gamma_binomial linear_sum; apply: eq_bigr => m _.
rewrite linearZ trace_Gamma_complement; first by [].
by move: (ltn_ord m); rewrite ltnS.
Qed.
(** Federer 1.4.5: the displayed value of the characteristic
    polynomial at t, followed by det(I+t f). *)
(** Source for [characteristic_polynomialE]: Federer (1969), 1.4.5, p. 21,
    binomial expansion and the two characteristic-polynomial displays. In
    words: The determinant of tI-f is the sum of t^(n-m)(-1)^m times the
    traces of the exterior powers of f; det(I+tf) has the corresponding
    coefficients t^m. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem characteristic_polynomialE (f : Hom V V) t :
  det h2 he (hom_as_linear (t *: I_V - f)) =
  \sum_(m < n.+1) (t ^+ (n-m) * (-1 : K)^+m) * trace h2 V (Gamma_exterior f m).
Proof. by rewrite -scaleN1r determinant_binomial. Qed.
(** Source for [determinant_identity_add]: Federer (1969), 1.4.5, p. 21,
    binomial expansion and the two characteristic-polynomial displays. In
    words: The determinant of tI-f is the sum of t^(n-m)(-1)^m times the
    traces of the exterior powers of f; det(I+tf) has the corresponding
    coefficients t^m. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Theorem determinant_identity_add (f : Hom V V) t :
  det h2 he (hom_as_linear (I_V + t *: f)) =
  \sum_(m < n.+1) t ^+ m * trace h2 V (Gamma_exterior f m).
Proof.
rewrite -{1}(scale1r I_V) determinant_binomial; apply: eq_bigr => m _.
by rewrite expr1n mul1r.
Qed.
End CharacteristicPolynomial.
