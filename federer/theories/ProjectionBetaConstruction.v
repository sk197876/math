(** Existence witness for beta_t(n,m), the actual normalization in Federer
    (1969), 2.10.5, p. 172. Use its universal integral formula from
    2.7.16(6), pp. 139–140, and beta at infinity equal to one. This witness
    is hidden behind the existing abstract projection-constant predicate.
    Source context and proofs of the defining formula:
    OrthogonalProjectionConstants.v and ProjectionConstantNorms.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import ExteriorDiameterUP OrthogonalProjectionConstants ProjectionConstantNorms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ereal_scope.

(** Source for [projection_beta_exists]: existence of
    the normalization in Federer 2.10.5, p. 172,
    characterized by 2.7.16(6), pp. 139–140.
    The dimension and exponent domain are explicit. *)
Theorem projection_beta_exists (R : realType) (n m : nat) (t : \bar R) :
  (m<=n)%N -> 1<=t -> exists beta,
    is_extended_projection_constant (real_exterior_two_nonzero R) t n m beta.
Proof.
move=> hmn; case: t=> [p| |] ht //.
- have hp : (0<p)%R by move: ht; rewrite lee_fin=> hp; exact: lt_le_trans ltr01 hp.
  exact: (@projection_constant_exists R (real_exterior_two_nonzero R) p n m hmn hp).
- exists 1%R; exact: projection_constant_infinity.
Qed.

(** Source for [projection_beta_witness]: private
    selection of the constant used in Federer
    2.10.5, p. 172. Exponents below one
    receive an irrelevant default, so the public
    exponent family is a function without proof arguments. *)
Definition projection_beta_witness (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (t : \bar R) :=
  if pselect (1<=t) is left ht then
    projT1 (cid (@projection_beta_exists R n m t hmn ht)) else 1%R.

(** Source for [projection_beta_witness_laws]: the
    selected constant satisfies the normalization
    formula required in Federer 2.10.5, p. 172,
    on the printed domain t>=1. *)
Lemma projection_beta_witness_laws (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (t : \bar R) : 1<=t ->
  is_extended_projection_constant (real_exterior_two_nonzero R) t n m
    (@projection_beta_witness R n m hmn t).
Proof.
move=> ht; rewrite /projection_beta_witness; case: (pselect (1<=t))=> [h|h]; last by [].
exact: projT2 (cid (@projection_beta_exists R n m t hmn h)).
Qed.
