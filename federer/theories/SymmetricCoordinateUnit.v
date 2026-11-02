(** Federer (1969), 1.10.2, p. 45: the empty product in the dual monomial
    basis. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded Hom HomogeneousHom BoundedHom TensorPowers
  LinearBasis SymmetricAlgebra SymmetricGrading SymmetricMultiIndices
  SymmetricUnitMultiIndices SymmetricMonomialCoordinates SymmetricFormSum SymmetricFormUnit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Unit.
Variable K : fieldType.
Hypothesis h0 : [pchar K] =i pred0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation M0 := (symmetric_coordinate_full_form he (symmetric_multi_zero n)).

(** Source for [symmetric_coordinate_zero_unit]: Federer 1.10.2,
    p. 45, the zero-exponent coordinate takes value one on the unit. *)
Lemma symmetric_coordinate_zero_unit : M0 (symmetric_unit V) = 1.
Proof.
by rewrite -(symmetric_divided_monomial_zero e)
  (@symmetric_coordinate_divided_monomial K V n e he h0) eqxx.
Qed.

(** Source for [symmetric_coordinate_zero_coefficient]: Federer
    1.10.2, p. 45, the zero-exponent normalized coordinate is the
    coefficient one, hence the empty symmetric product of one-forms. *)
Theorem symmetric_coordinate_zero_coefficient :
  M0 = @symmetric_coefficient_form K V K^o 1.
Proof.
apply: hom_finite_ext=> x.
elim/symmetric_word_induction: x=> [|x y hx hy|c x hx|s].
- by rewrite !linear0.
- rewrite !linearD.
  change (M0 x + M0 y = @symmetric_coefficient_form K V K^o 1 x +
    @symmetric_coefficient_form K V K^o 1 y).
  by rewrite hx hy.
- rewrite !linearZ.
  change (c * M0 x = c * @symmetric_coefficient_form K V K^o 1 x).
  by rewrite hx.
- case: s=> [|v s].
  + by rewrite symmetric_word_nil symmetric_coordinate_zero_unit
      symmetric_coefficient_formE symmetric_augmentation_unit scale1r.
  + have hz : M0 (symmetric_word (v::s)) = 0.
      change (symmetric_coordinate_homogeneous he (symmetric_multi_zero n)
        (symmetric_word (v::s)) = 0).
      apply: hom_m_degree (symmetric_word_homogeneous (v::s)).
      by rewrite symmetric_multi_degree_zero.
    by rewrite hz symmetric_coefficient_formE symmetric_augmentation_word /word_degree_zero scale0r.
Qed.
End Unit.
