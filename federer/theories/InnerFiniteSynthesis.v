(** Federer (1969), 1.7.1, p. 28: the finite-dimensional compactness
    argument after choosing an orthonormal basis. This module proves
    continuity of finite synthesis and recovers every vector from its
    inner-product coordinates. General topological continuity rules are
    background; the basis and coordinate statements are proved in this
    project. Source context are recorded in InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities
  InnerMetric InnerNormedTopology OrthonormalFamilies OrthonormalProjection
  InnerNormalization LinearBasis FiniteSpans Annihilator FiniteDualDimension Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Import ArrowAsProduct.
Local Open Scope ring_scope.
Section Synthesis.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation M := (inner_metric_space hB).
Variable n : nat.
Variable e : 'I_n -> V.

(** Source for [inner_finite_synthesis]: Federer 1.7.1,
    p. 28, the coordinate map from a finite real product into V. *)
Definition inner_finite_synthesis (c : 'I_n -> R^o) : M := \sum_i c i *: e i.

(** Source for [inner_finite_synthesis_continuous]: Federer
    1.7.1, p. 28, supporting continuity of the finite-coordinate
    map in the compactness argument. No basis hypothesis is needed. *)
Theorem inner_finite_synthesis_continuous : continuous inner_finite_synthesis.
Proof.
apply: continuous_big; first exact: add_continuous.
move=> i _ c; apply: continuousZ.
- exact: proj_continuous.
- exact: cst_continuous.
Qed.

Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.

(** Source for [inner_finite_synthesis_coordinates]: Federer
    1.7.1, p. 28, an orthonormal basis recovers every vector from
    the coordinates x.e_i. This identifies the finite-coordinate image. *)
Theorem inner_finite_synthesis_coordinates (x : M) :
  inner_finite_synthesis (fun i => inner_coordinate hB (e i) x) = x.
Proof.
apply: (@orthonormal_projection_fixed R V B hB n e ho x).
exists (fun i => dual_basis he i x); exact: basis_vector_expansion.
Qed.

(** Source for [inner_orthonormal_coordinate_bound]: Federer
    1.7.1, p. 28, supporting bound in the finite-dimensional
    compactness argument: each orthonormal coordinate has absolute
    value at most the vector's norm, by Cauchy's inequality. *)
Lemma inner_orthonormal_coordinate_bound (x : M) i :
  `|inner_coordinate hB (e i) x| <= inner_norm hB x.
Proof.
rewrite inner_coordinateE.
have h := @inner_cauchy R V B hB x (e i).
by rewrite (@orthonormal_norm1 R V B hB (Finite.clone 'I_n _) e ho i) mulr1 in h.
Qed.
End Synthesis.
