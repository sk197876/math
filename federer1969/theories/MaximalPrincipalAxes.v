(** Federer (1969), 1.7.3, p. 29: successive maximisers give decreasing
    diagonal values and zero off-diagonal values. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization
  OrthonormalFamilies PrincipalAxesUP MaximalOrthonormalUP
  PrincipalAxisConstraint RayleighStationary TensorUP LinearBasis
  FiniteDimension FiniteBasisCriterion ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Principal.
Variable R : rcfType.
Variable V : lmodType R.
Variable B S : V -> V -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hS : @bilinear R V V R^o S.
Hypothesis hs : forall x y, S x y = S y x.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_maximal_orthonormal_family S hB e.
Let ho := maximal_family_orthonormal he.

(** Source for [maximal_family_ordered]: Federer 1.7.3,
    p. 29, S(e_i,e_i)>=S(e_j,e_j) for i<j, because each later
    unit vector satisfies the constraints used to choose e_i. *)
Lemma maximal_family_ordered (i j : 'I_n) : (i < j)%N ->
  S (e j) (e j) <= S (e i) (e i).
Proof.
move=> hij; apply: (maximal_family_value he).
- exact (@orthonormal_norm1 R V B hB (Finite.clone 'I_n _) e ho j).
- exact (@orthonormal_axis_in_constraint R V B hB n e i ho j (ltnW hij)).
Qed.

(** Source for [maximal_family_off_diagonal]: Federer 1.7.3,
    p. 29, vanishing of the off-diagonal values. The stationary
    identity applies in the subspace orthogonal to preceding axes. *)
Lemma maximal_family_off_diagonal (i j : 'I_n) : (i < j)%N -> S (e i) (e j) = 0.
Proof.
move=> hij.
have hxi := @orthonormal_axis_in_constraint R V B hB n e i ho i (leqnn i).
have hxj := @orthonormal_axis_in_constraint R V B hB n e i ho j (ltnW hij).
have hn := @orthonormal_norm1 R V B hB (Finite.clone 'I_n _) e ho i.
have hm x : principal_axis_constraint hB e i x -> inner_norm hB x = 1 ->
    S x x <= S (e i) (e i).
  move=> hx hnx; exact (@maximal_family_value R V B S hB n e he i x hnx hx).
have h := @rayleigh_stationary_in_subspace R V B S hB hS hs
  (principal_axis_constraint hB e i) (e i) hxi hn hm (e j) hxj.
have hne : i != j by apply/eqP=> h'; move: hij; rewrite h' ltnn.
by rewrite h ho (negbTE hne) mulr0.
Qed.

(** Source for [maximal_family_principal_axes]: Federer 1.7.3,
    p. 29, completion of the principal-axis argument from n
    successive orthonormal maximisers in an n-dimensional space. *)
Theorem maximal_family_principal_axes (b : 'I_n -> V) :
  is_basis b -> is_principal_axes B S e.
Proof.
move=> hb; constructor=> //.
- pose U := finite_basis_vect hb.
  apply: (@finite_independent_basis R U n e).
  + by rewrite /U finite_basis_dimension card_ord.
  + exact (@orthonormal_independent R V B hB (Finite.clone 'I_n _) e ho).
- exact: maximal_family_ordered.
- exact: maximal_family_off_diagonal.
Qed.
End Principal.
