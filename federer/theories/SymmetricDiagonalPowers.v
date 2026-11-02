(** Federer (1969), 1.9.4, p. 43: the monomial diagonal formula in one
    variable. The proof applies the binomial theorem to the two tensor
    placements of one vector. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded AlgebraPowers AlgebraBinomial DividedBinomial AlgebraPowerMaps
  SymmetricAlgebra SymmetricGrading SymmetricDirectSum SymmetricDiagonal SymmetricCounit
  SymmetricDividedMonomials.
From Federer Require Import UnitalGradedTensor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Powers.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (symmetric_unital V).
Local Notation EG := (unital_graded_view E).
Local Notation T := (unital_graded_tensor E E false).
Local Notation u := (symmetric_unit V).
Local Notation D := (symmetric_diagonal V).

(** Source for [symmetric_tensor_unit_nonzero]: Federer
    1.9.4, p. 43, supporting nondegeneracy: the unit in the
    ordinary tensor square is nonzero, as contraction maps it to
    the nonzero unit of the symmetric algebra. *)
Lemma symmetric_tensor_unit_nonzero : alg_one T != 0.
Proof.
apply/eqP=> hz.
have h := congr1 (symmetric_counit_left V) hz.
rewrite algebra_map_one linear0 in h.
exact: (negP (symmetric_unit_nonzero V)) (introT eqP h).
Qed.

(** Source for [symmetric_tensor_left_power]: Federer 1.9.4,
    p. 43, supporting identity: the power of x tensor 1 is
    x^m tensor 1 in the ordinary tensor algebra. *)
Lemma symmetric_tensor_left_power (x : E) m :
  @algebra_power K T (tensor_inj x u) m = tensor_inj (@algebra_power K E x m) u.
Proof.
elim: m=> [|m ih] //=.
rewrite ih (@ordinary_tensor_mulE K EG EG).
change (tensor_inj (alg_mul E x (@algebra_power K E x m)) (alg_mul E u u) =
  tensor_inj (alg_mul E x (@algebra_power K E x m)) u).
by rewrite alg_unitl.
Qed.

(** Source for [symmetric_tensor_right_power]: Federer 1.9.4,
    p. 43, the power of 1 tensor x is 1 tensor x^m. *)
Lemma symmetric_tensor_right_power (x : E) m :
  @algebra_power K T (tensor_inj u x) m = tensor_inj u (@algebra_power K E x m).
Proof.
elim: m=> [|m ih] //=.
rewrite ih (@ordinary_tensor_mulE K EG EG).
change (tensor_inj (alg_mul E u u) (alg_mul E x (@algebra_power K E x m)) =
  tensor_inj u (alg_mul E x (@algebra_power K E x m))).
by rewrite alg_unitl.
Qed.

(** Source for [symmetric_diagonal_power_binomial]: Federer
    1.9.4, p. 43, the ordinary monomial formula for one
    vector: the diagonal of v^m is the sum of binomial(m,i)
    times v^i tensor v^(m-i). *)
Lemma symmetric_diagonal_power_binomial v m :
  D (symmetric_vector_power v m) =
    \sum_(i < m.+1) ('C(m,i)%:R : K) *:
      tensor_inj (symmetric_vector_power v i) (symmetric_vector_power v (m-i)).
Proof.
rewrite symmetric_vector_powerE algebra_hom_power symmetric_diagonalE addrC.
rewrite (@algebra_binomial K T (@symmetric_tensor_commutative K V V)
  symmetric_tensor_unit_nonzero).
apply: eq_bigr=> i _; congr (_ *: _).
rewrite symmetric_tensor_right_power symmetric_tensor_left_power.
change (@graded_tensor_mul K EG EG false
  (tensor_inj u (@algebra_power K E (symmetric_generator v) (m-i)))
  (tensor_inj (@algebra_power K E (symmetric_generator v) i) u) =
  tensor_inj (symmetric_vector_power v i) (symmetric_vector_power v (m-i))).
rewrite (@ordinary_tensor_mulE K EG EG).
change (tensor_inj (symmetric_product u (@algebra_power K E (symmetric_generator v) i))
  (symmetric_product (@algebra_power K E (symmetric_generator v) (m-i)) u) =
  tensor_inj (symmetric_vector_power v i) (symmetric_vector_power v (m-i))).
by rewrite symmetric_product_unitl symmetric_product_unitr !symmetric_vector_powerE.
Qed.

(** Source for [symmetric_diagonal_divided_power]: Federer
    1.9.4, p. 43, the divided monomial formula for one vector:
    the binomial coefficients cancel against the factorial denominator. *)
Theorem symmetric_diagonal_divided_power (h0 : [pchar K] =i pred0) v m :
  D (symmetric_divided_vector_power v m) =
    \sum_(i < m.+1) tensor_inj (symmetric_divided_vector_power v i)
      (symmetric_divided_vector_power v (m-i)).
Proof.
rewrite /symmetric_divided_vector_power linearZ.
change ((m`!%:R : K)^-1 *: D (symmetric_vector_power v m) =
  \sum_(i < m.+1) tensor_inj ((i`!%:R : K)^-1 *: symmetric_vector_power v i)
    (((m-i)`!%:R : K)^-1 *: symmetric_vector_power v (m-i))).
rewrite symmetric_diagonal_power_binomial scaler_sumr.
apply: eq_bigr=> i _.
rewrite tensor_inj_scalel tensor_inj_scaler !scalerA.
have hi : (i <= m)%N by move: (valP i); rewrite ltnS.
by rewrite (divided_binomial_coefficient h0 hi) mulrC.
Qed.
End Powers.
