(** Federer (1969), 1.9.3, p. 43: cancellation in the signed polarization
    sum. These supporting coefficient identities use finite distributivity
    to pair the two signs in each coordinate. They remain valid over any
    field; factorial division is handled separately. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricMultiIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [symmetric_multi_one]: Federer 1.9.3, p. 43,
    the all-ones exponent tuple, which is the only degree-m
    tuple in m variables having no zero entry. *)
Definition symmetric_multi_one m : symmetric_multi_index m := [ffun _ => 1%N].

(** Source for [symmetric_multi_one_degree]: Federer 1.9.3,
    p. 43, the all-ones tuple in m variables has degree m. *)
Lemma symmetric_multi_one_degree m : symmetric_multi_degree (symmetric_multi_one m) = m.
Proof.
rewrite /symmetric_multi_degree /symmetric_multi_one.
under eq_bigr do rewrite ffunE.
by rewrite sum1_card card_ord.
Qed.

(** Source for [symmetric_positive_balanced_index]: Federer
    1.9.3, p. 43, supporting inference in the polarization
    argument: m positive integer entries summing to m are all one. *)
Lemma symmetric_positive_balanced_index m (a : symmetric_multi_index m) :
  symmetric_multi_degree a = m -> (forall i, 0 < a i) -> a = symmetric_multi_one m.
Proof.
move=> hm ha.
have hs : (\sum_(i < m) (a i - 1)) = 0.
  rewrite sumnB; last by move=> i _; exact: ha.
  by rewrite -/(symmetric_multi_degree a) hm sum1_card card_ord subnn.
have hz : forall i, a i - 1 == 0.
  have h := introT eqP hs; rewrite sum_nat_eq0 in h.
  by move=> i; exact: (forallP h i).
apply/ffunP=> i; rewrite /symmetric_multi_one ffunE.
apply/eqP; rewrite eqn_leq; apply/andP; split; last exact: ha.
by move: (hz i); rewrite subn_eq0.
Qed.

(** Source for [polarization_signs]: Federer 1.9.3, p. 43,
    T is the set of all functions from the m positions to two
    signs, encoded by booleans. *)
Definition polarization_signs m := {ffun 'I_m -> bool}.

Section Coefficients.
Variable K : fieldType.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polarization_sign]: Federer 1.9.3, p. 43,
    the two choices of scalar sign, minus one and one. *)
Definition polarization_sign (b : bool) : K := if b then -1 else 1.

(** Source for [polarization_coefficient]: Federer 1.9.3,
    p. 43, the bracketed coefficient after interchanging the
    multinomial sum and the sum over sign choices. *)
Definition polarization_coefficient m (a : symmetric_multi_index m) : K :=
  \sum_(t : polarization_signs m) \prod_(i < m)
    (polarization_sign (t i)) ^+ (1 + a i).

(** Source for [polarization_coefficient_factor]: Federer
    1.9.3, p. 43, supporting finite distributivity: the sum
    over independent sign choices factors into one sum per position. *)
Lemma polarization_coefficient_factor m (a : symmetric_multi_index m) :
  polarization_coefficient a = \prod_(i < m)
    (\sum_(b : bool) (polarization_sign b) ^+ (1 + a i)).
Proof. exact: esym (bigA_distr_bigA _). Qed.

(** Source for [polarization_coefficient_missing]: Federer
    1.9.3, p. 43, the bracketed coefficient vanishes if some
    exponent is zero, because the two signs at that position cancel. *)
Lemma polarization_coefficient_missing m (a : symmetric_multi_index m) j :
  a j = 0%N -> polarization_coefficient a = 0.
Proof.
move=> hj.
by rewrite polarization_coefficient_factor (bigD1 j) //= hj addn0
  big_bool /polarization_sign /= ?expr1 ?mulr1 ?addNr ?mul0r.
Qed.

(** Source for [polarization_coefficient_one]: Federer 1.9.3,
    p. 43, the coefficient of the all-ones tuple is the number
    of sign choices, namely two to the power m. *)
Lemma polarization_coefficient_one m :
  polarization_coefficient (symmetric_multi_one m) = (2%:R : K) ^+ m.
Proof.
rewrite polarization_coefficient_factor /symmetric_multi_one.
under eq_bigr do rewrite ffunE big_bool /polarization_sign !expr2 !mulrNN !mul1r.
by rewrite prodr_const card_ord.
Qed.

(** Source for [polarization_balanced_coefficient]: Federer
    1.9.3, p. 43, the complete coefficient calculation:
    amongst degree-m exponents in m variables, only the all-ones
    tuple survives, with coefficient two to the power m. *)
Theorem polarization_balanced_coefficient m (a : symmetric_multi_index m) :
  symmetric_multi_degree a = m ->
  polarization_coefficient a = if a == symmetric_multi_one m then (2%:R : K)^+m else 0.
Proof.
move=> hm; case: eqP=> [->|hne]; first exact: polarization_coefficient_one.
have /existsP [j hj] : [exists i, a i == 0%N].
  case: (boolP [exists i, a i == 0%N])=> [he|hn]; first by [].
  move: hn; rewrite negb_exists => /forallP hp.
  exfalso; apply: hne; apply: (@symmetric_positive_balanced_index m a hm)=> i.
  by move: (hp i); rewrite -lt0n.
exact: polarization_coefficient_missing (eqP hj).
Qed.
End Coefficients.
