(** Federer (1969), 1.7.3, p. 29: supporting extraction of eigenvectors from
    a diagonal bilinear form. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP OrthonormalFamilies
  InnerFiniteSynthesis LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SingleCoordinate.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.

(** Source for [orthonormal_single_coordinate]: Federer
    1.7.3, p. 29, supporting step: a vector orthogonal to all
    basis vectors other than e_i equals its i-th coordinate times e_i. *)
Lemma orthonormal_single_coordinate v (i : 'I_n) :
  (forall j, j != i -> B v (e j) = 0) -> v = B v (e i) *: e i.
Proof.
move=> hv.
have hc := @inner_finite_synthesis_coordinates R V B hB n e he ho v.
have hs : inner_finite_synthesis hB e (fun j => inner_coordinate hB (e j) v) =
    B v (e i) *: e i.
  rewrite /inner_finite_synthesis (bigD1 i) // inner_coordinateE.
  have hz : \sum_(j | j != i) inner_coordinate hB (e j) v *: e j = 0.
    apply: big1 => j hj; by rewrite inner_coordinateE hv // scale0r.
  by rewrite hz /= addr0.
exact (eq_trans (esym hc) hs).
Qed.
End SingleCoordinate.
