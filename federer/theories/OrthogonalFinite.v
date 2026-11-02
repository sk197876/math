(** Federer (1969), 1.7.2, p. 28: in finite dimension an orthogonal
    endomorphism is an automorphism. This justifies the orthogonal group. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP FiniteIndependence
  FiniteBasisComparison FiniteBasisCriterion FiniteDimension
  LinearBasis Annihilator FiniteDualDimension Hom.
From Federer Require Import OrthogonalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section FiniteOrthogonal.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Variable f : {linear V -> V}.
Hypothesis hf : is_orthogonal_map B B f.

(** Source for [orthogonal_endomorphism_surjective]: Federer 1.7.2,
    p. 28, supporting group fact: a finite-dimensional orthogonal
    endomorphism maps onto the whole space. *)
Theorem orthogonal_endomorphism_surjective : forall y, exists x, f x = y.
Proof.
have hi := orthogonal_map_injective hB hB hf.
have hfe := finite_independent_map hi (finite_basis_independent he).
pose U := finite_basis_vect he.
have hb : is_basis (fun i => f (e i)).
  apply: (@finite_independent_basis R U n (fun i => f (e i))) => //.
  by rewrite /U finite_basis_dimension card_ord.
move=> y; exists (\sum_i dual_basis hb i y *: e i).
rewrite linear_sum; under eq_bigr do rewrite linearZ.
exact: esym (basis_vector_expansion hb y).
Qed.

(** Source for [orthogonal_endomorphism_inverse_exists]: Federer
    1.7.2, p. 28, supporting group inverse: every finite-dimensional
    orthogonal endomorphism has a two-sided linear orthogonal inverse. *)
Theorem orthogonal_endomorphism_inverse_exists :
  exists g : {linear V -> V}, cancel f g /\ cancel g f /\ is_orthogonal_map B B g.
Proof.
have hi := orthogonal_map_injective hB hB hf.
pose g := linear_inverse hi orthogonal_endomorphism_surjective.
exists (GRing.Linear.clone _ _ _ _ g _); split; first exact: linear_inverseKV.
split; first exact: linear_inverseK.
apply: orthogonal_inverse hf _; exact: linear_inverseK.
Qed.
End FiniteOrthogonal.
