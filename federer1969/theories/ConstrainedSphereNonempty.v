(** Federer (1969), 1.7.3, p. 29: the constrained unit sphere is nonempty
    before the chosen orthonormal family reaches the dimension. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization
  InnerMetric OrthonormalFamilies OrthonormalProjection FiniteSpans
  FiniteBasisCriterion FiniteBasisComparison LinearBasis ConstrainedUnitSphere.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Nonempty.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable k : nat.
Variable e : 'I_k -> V.
Hypothesis he : orthonormal_family B e.

(** Source for [orthonormal_family_missing_vector]: Federer
    1.7.3, p. 29, supporting dimension fact: fewer than dim V
    orthonormal vectors cannot span V. *)
Lemma orthonormal_family_missing_vector : (k < n)%N ->
  exists x, ~ in_finite_span e x.
Proof.
move=> hkn; apply: contrapT => hnone.
have hs x : in_finite_span e x.
  apply: contrapT => hx; apply: hnone; by exists x.
have hi := @orthonormal_independent R V B hB (Finite.clone 'I_k _) e he.
have hk : k = n := finite_basis_size (finite_basis_criterion hi hs) hb.
by move: hkn; rewrite hk ltnn.
Qed.

(** Source for [constrained_unit_sphere_nonempty]: Federer
    1.7.3, p. 29, existence of candidates in C_j at every step:
    normalise a nonzero residual orthogonal to the preceding family. *)
Theorem constrained_unit_sphere_nonempty : (k < n)%N ->
  @constrained_unit_sphere R V B hB k e !=set0.
Proof.
move=> hk; have [x hx] := orthonormal_family_missing_vector hk.
have hn := @orthonormal_residual_nonzero R V B hB k e x hx.
exists (inner_normalize hB (x - orthonormal_projection hB e x)); split.
- exact: inner_normalize_norm.
- move=> i; apply: inner_normalize_orthogonal.
  exact (@orthonormal_residual_orthogonal R V B hB (Finite.clone 'I_k _) e he x i).
Qed.
End Nonempty.
