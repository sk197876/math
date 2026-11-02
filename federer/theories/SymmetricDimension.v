(** Federer (1969), 1.9.2, p. 42: the dimension of the m-th symmetric power
    in finite dimension. Positive and zero ambient dimensions are
    distinguished; arbitrary scalar fields are allowed. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import LinearBasis FiniteDimension SymmetricGrading
  SymmetricMonomialBasis SymmetricIndexCardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [finite_symmetric_power]: Federer 1.9.2,
    p. 42, the finite-dimensional structure on the abstract symmetric
    power, supplied by the proved finite monomial basis. *)
Definition finite_symmetric_power (K : fieldType) (V : lmodType K)
    n (e : 'I_n -> V) (he : is_basis e) m : vectType K :=
  finite_basis_vect (symmetric_finite_monomial_basis he m).

(** Source for [symmetric_power_dimension]: Federer 1.9.2,
    p. 42, the displayed dimension formula in positive ambient
    dimension: dim Sym_m(V)=binomial(m+n,n) for dim V=n+1. *)
Theorem symmetric_power_dimension (K : fieldType) (V : lmodType K)
    n (e : 'I_n.+1 -> V) (he : is_basis e) m :
  dim (finite_symmetric_power he m) = 'C(m+n,n).
Proof. by rewrite /finite_symmetric_power finite_basis_dimension card_symmetric_indices. Qed.

(** Source for [symmetric_power_dimension_zero]: Federer 1.9.2, p. 42, the
    zero-dimensional boundary: dimension one in degree zero, and dimension
    zero in every positive degree. *)
Theorem symmetric_power_dimension_zero (K : fieldType) (V : lmodType K)
    (e : 'I_0 -> V) (he : is_basis e) m :
  dim (finite_symmetric_power he m) = (m == 0).
Proof. by rewrite /finite_symmetric_power finite_basis_dimension card_symmetric_indices_zero. Qed.
