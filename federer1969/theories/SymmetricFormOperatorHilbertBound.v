(** Federer (1969), 1.10.6, p. 49: the first final norm comparison, ||phi||
    <= m^m |phi| / sqrt(m!). This follows exactly as the book says from the
    polynomial bound and 1.10.5. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import InnerProductUP InnerNorm LinearBasis SymmetricForms
  SymmetricFormInner SymmetricFormHilbertBounds HomogeneousPolynomialFunctions
  RealNormUP HilbertFormCompactness PolynomialNorm PolynomialPolarizationNorm
  SymmetricOperatorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Bounds.
Variable R : realType.
Variables V W : lmodType R.
Variable B : V -> V -> R.
Variable C : W -> W -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable m : nat.

(** Source for [symmetric_polynomial_norm_hilbert_bound]: Federer 1.10.6,
    p. 49, supporting unit-ball consequence of the penultimate
    display: the associated polynomial norm is at most |phi|/sqrt(m!). *)
Theorem symmetric_polynomial_norm_hilbert_bound (f : S_m V W m) :
  (polynomial_norm (proj1 (inner_norm_real_norm hB)) (inner_norm hC)
    (sform_polynomial_value f) <=
    ((Num.sqrt ((m`!)%:R : R))^-1 * symmetric_form_norm hB hC he m f)%:E)%E.
Proof.
apply: polynomial_norm_least=> x hx; rewrite lee_fin.
apply: le_trans (symmetric_form_polynomial_hilbert_bound hB hC he f x) _.
rewrite -[leRHS]mulr1 [(_ * _) * 1]mulr1.
have hpow : (inner_norm hB x)^+m <= 1.
  rewrite -[leRHS](expr1n R m).
  apply: lerXn2r.
  - exact: inner_norm_nonnegative.
  - exact: ler01.
  - exact: hx.
apply: (ler_wpM2r (inner_norm_nonnegative _ _)).
rewrite -[leRHS]mulr1; apply: ler_wpM2l; last exact: hpow.
by rewrite invr_ge0 sqrtr_ge0.
Qed.

(** Source for [symmetric_operator_norm_hilbert_bound]: Federer 1.10.6,
    p. 49, first final inequality. In words: the operator norm
    is bounded by m^m times the Hilbert length divided by sqrt(m!).
    The extended-supremum convention is retained, and this finite bound
    therefore also establishes boundedness. The convention 0^0=1
    gives the correct degree-zero statement. *)
Theorem symmetric_operator_norm_hilbert_bound (f : S_m V W m) :
  (symmetric_operator_norm (proj1 (inner_norm_real_norm hB)) (inner_norm hC) f <=
    (((m%:R : R)^+m * (Num.sqrt ((m`!)%:R : R))^-1) *
      symmetric_form_norm hB hC he m f)%:E)%E.
Proof.
have h := @polynomial_polarization_finite_norm_bound R V W (inner_norm hB)
  (inner_norm hC) (inner_norm_real_norm hB) (proj1 (inner_norm_real_norm hC))
  m f _ (symmetric_polynomial_norm_hilbert_bound f).
by rewrite mulrA in h.
Qed.
End Bounds.
