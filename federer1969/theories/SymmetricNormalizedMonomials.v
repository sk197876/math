(** Federer (1969), 1.10.5, p. 47, the normalized monomials
    e^alpha/sqrt(alpha!) in the first displayed orthonormal family. This
    module defines the scalar normalization and proves that it preserves a
    monomial basis. Orthogonality is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import GradedComponents LinearBasis BasisRescaling
  SymmetricAlgebra SymmetricGrading SymmetricMultiIndices SymmetricIndexBounds
  SymmetricMonomials SymmetricMonomialBasis SymmetricDividedMonomials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_factorial_scalar_positive]: Federer 1.10.5,
    p. 47, supporting positivity of the normalization alpha!. The
    factorial product is a nonzero natural scalar, also for empty indices. *)
Lemma symmetric_factorial_scalar_positive (R : realFieldType) n
    (a : symmetric_multi_index n) :
  0 < ((symmetric_multi_factorial a)%:R : R).
Proof.
have hn := @symmetric_multi_factorial_nonzero R (@pchar_num R) n a.
by rewrite lt_def hn ler0n.
Qed.

(** Source for [symmetric_factorial_root]: Federer 1.10.5,
    p. 47, the scalar sqrt(alpha!) in the displayed normalization. *)
Definition symmetric_factorial_root (R : rcfType) n (a : symmetric_multi_index n) : R :=
  Num.sqrt ((symmetric_multi_factorial a)%:R : R).

(** Source for [symmetric_factorial_root_positive]: Federer 1.10.5,
    p. 47, supporting legitimacy of division by sqrt(alpha!). *)
Lemma symmetric_factorial_root_positive (R : rcfType) n (a : symmetric_multi_index n) :
  0 < symmetric_factorial_root R a.
Proof. rewrite /symmetric_factorial_root sqrtr_gt0; exact: symmetric_factorial_scalar_positive. Qed.

(** Source for [symmetric_factorial_root_square]: Federer 1.10.5,
    p. 47, squaring the normalization recovers alpha!. *)
Lemma symmetric_factorial_root_square (R : rcfType) n (a : symmetric_multi_index n) :
  (symmetric_factorial_root R a)^+2 = (symmetric_multi_factorial a)%:R.
Proof. rewrite /symmetric_factorial_root sqr_sqrtr //; exact: ler0n. Qed.

Section Monomials.
Variable R : rcfType.
Variable V : lmodType R.
Variable n : nat.
Variable e : 'I_n -> V.

(** Source for [symmetric_normalized_monomial]: Federer 1.10.5,
    p. 47, the actual normalized vector e^alpha/sqrt(alpha!) in
    the m-th symmetric power. No orthogonality is assumed in its definition. *)
Definition symmetric_normalized_monomial m (a : symmetric_indices n m) : symmetric_power V m :=
  (symmetric_factorial_root R (symmetric_indices_unbound a))^-1 *:
    symmetric_finite_monomial e a.

(** Source for [symmetric_normalized_monomialE]: Federer 1.10.5,
    p. 47, inclusion into the full algebra gives exactly the
    displayed scalar multiple of the ordinary monomial. *)
Lemma symmetric_normalized_monomialE m (a : symmetric_indices n m) :
  component_val (symmetric_normalized_monomial a) =
    (symmetric_factorial_root R (symmetric_indices_unbound a))^-1 *:
      symmetric_monomial e (symmetric_indices_unbound a).
Proof.
rewrite /symmetric_normalized_monomial linearZ.
change ((symmetric_factorial_root R (symmetric_indices_unbound a))^-1 *:
  component_val (symmetric_finite_monomial e a) =
  (symmetric_factorial_root R (symmetric_indices_unbound a))^-1 *:
    symmetric_monomial e (symmetric_indices_unbound a)).
by rewrite /symmetric_finite_monomial symmetric_monomial_componentE.
Qed.

(** Source for [symmetric_normalized_monomial_basis]: Federer 1.10.5,
    p. 47, the normalized family is a basis whenever the original
    family is a finite basis, using 1.9.2 and nonzero rescaling. *)
Theorem symmetric_normalized_monomial_basis (he : is_basis e) m :
  is_basis (@symmetric_normalized_monomial m).
Proof.
apply: (@basis_rescaling R (Choice.clone (symmetric_indices n m) _)
  (symmetric_power V m) (@symmetric_finite_monomial R V n e m)
  (symmetric_finite_monomial_basis he m)).
move=> a; rewrite invr_eq0.
exact: lt0r_neq0 (symmetric_factorial_root_positive R (symmetric_indices_unbound a)).
Qed.
End Monomials.
