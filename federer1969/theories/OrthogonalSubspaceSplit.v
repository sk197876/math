(** Federer (1969), 1.7.3, p. 29: orthogonal splitting used to decompose
    invariant subspaces. Only the subspace being projected onto needs a
    finite basis; the ambient space may be infinite. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient SubspaceCarrier InnerProductUP
  InnerProductRestriction OrthogonalComplement OrthonormalFamilies
  OrthonormalProjection OrthonormalisationUP GramSchmidt LinearBasis
  FiniteDualDimension Annihilator Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Splitting.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable W : subspace V.
Variable n : nat.
Variable b : 'I_n -> subspace_space W.
Hypothesis hb : is_basis b.

(** Source for [finite_subspace_orthogonal_split]: Federer
    1.7.3, p. 29, supporting orthogonal direct-sum decomposition:
    every vector is the sum of a vector in a finite-dimensional
    subspace and a vector perpendicular to that subspace. *)
Theorem finite_subspace_orthogonal_split x :
  exists w z, W w /\ orthogonal_complement hB W z /\ x = w+z.
Proof.
pose C := @restricted_inner_product R V B W.
have hC := @restricted_inner_productP R V B hB W.
have [e [he hgs]] := @orthonormal_basis_exists R (subspace_space W) C hC n b hb.
have ho := orthonormalisation_orthonormal hgs.
pose a := fun i => subspace_val (e i).
have ha : orthonormal_family B a by exact ho.
pose w := orthonormal_projection hB a x.
exists w, (x-w); split.
- change (W (\sum_i inner_coordinate hB (a i) x *: a i)).
  elim/big_rec: _ => [|i v _ hv]; first exact: subspace_zero.
  apply: subspace_add; last exact hv.
  apply: subspace_scale; exact: subspace_valP.
- split; last by rewrite addrC subrK.
  move=> y hy.
  have hyE := congr1 (@subspace_val R V W)
    (basis_vector_expansion he (subspace_lift hy)).
  rewrite subspace_liftE linear_sum in hyE.
  rewrite (inner_symmetric hB).
  rewrite hyE -(inner_coordinateE hB) linear_sum.
  apply: big1 => i _; rewrite !linearZ inner_coordinateE (inner_symmetric hB).
  rewrite (@orthonormal_residual_orthogonal R V B hB
    (Finite.clone 'I_n _) a ha x i).
  change (dual_basis he i (subspace_lift hy) * 0 = 0).
  by rewrite mulr0.
Qed.
End Splitting.
