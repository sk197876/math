(** Federer (1969), 1.10.5, p. 47, induced inner products; the pure-power
    norm is also used in 1.10.6, p. 49. These are specializations of the
    permutation formula; no basis or finite dimension is needed. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import InnerProductUP InnerNorm SymmetricAlgebra SymmetricGrading
  SymmetricFormIsomorphism InnerSymmetric InnerSymmetricPermutationFormula
  SymmetricInnerNorm InnerSymmetricPositivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section PurePowers.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.

(** Source for [symmetric_inner_pure_powers]: Federer 1.10.5,
    p. 47, supporting consequence of the induced inner-product
    formula. The pairing of x to the m-th power and y to the m-th
    power is m factorial times the m-th power of their pairing. *)
Lemma symmetric_inner_pure_powers m (x y : V) :
  symmetric_inner_form hB (symmetric_tuple_component [tuple x | i < m])
    (symmetric_tuple_component [tuple y | i < m]) = (m`!)%:R * B x y ^+ m.
Proof.
rewrite symmetric_inner_tuple_permutations.
under eq_bigr do (under eq_bigr do rewrite !tnth_mktuple).
under eq_bigr do rewrite prodr_const card_ord.
by rewrite sumr_const card_Sn mulr_natl.
Qed.

(** Source for [symmetric_inner_pure_power_norm]: Federer 1.10.5,
    p. 47, induced norm; also the pure-power identity used in
    1.10.6, p. 49. The Hilbert norm of x to the m-th power
    is the square root of m factorial times the m-th power of its length.
    This differs from the mass norm in the later paragraph of 1.10.5. *)
Theorem symmetric_inner_pure_power_norm m (x : V) :
  symmetric_inner_norm hB (symmetric_tuple_component [tuple x | i < m]) =
    Num.sqrt ((m`!)%:R : R) * (inner_norm hB x) ^+ m.
Proof.
apply: inner_norm_value.
- apply: mulr_ge0; first exact: sqrtr_ge0.
  exact: exprn_ge0 (inner_norm_nonnegative hB x).
- rewrite exprMn sqr_sqrtr ?ler0n // exprAC inner_norm_sqr.
  symmetry; exact: symmetric_inner_pure_powers.
Qed.
End PurePowers.
