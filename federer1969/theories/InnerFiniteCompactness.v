(** Federer (1969), 1.7.1, p. 28: finite dimension implies bounded
    compactness. We prove this using orthonormal coordinates and compact
    real intervals. Only general topology and completeness of the real
    scalar field are imported. Source context: InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets set_interval reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerMetric
  InnerNormedTopology InnerFiniteSynthesis InnerBoundedness
  OrthonormalFamilies OrthonormalisationUP GramSchmidt LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteCompactness.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation M := (inner_metric_space hB).
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.

(** Source for [inner_coordinate_cube]: Federer 1.7.1, p. 28,
    supporting finite-coordinate box for the compactness assertion. *)
Definition inner_coordinate_cube (r : R) : set ('I_n -> R^o) :=
  [set c | forall i, `[-r, r] (c i)].

(** Source for [inner_coordinate_cube_compact]: Federer 1.7.1,
    p. 28, supporting compactness of the coordinate box, from compactness
    of real closed intervals and the general product theorem. *)
Lemma inner_coordinate_cube_compact r : compact (inner_coordinate_cube r).
Proof.
exact (@tychonoff _ (fun _ : 'I_n => (Topological.clone R^o _))
  (fun _ => `[(-r), r]) (fun _ => @segment_compact R (-r) r)).
Qed.

(** Source for [inner_orthonormal_boundedly_compact]: Federer 1.7.1,
    p. 28, forward implication: a finite orthonormal basis makes each
    closed bounded set compact, including the zero-dimensional case. *)
Theorem inner_orthonormal_boundedly_compact : inner_boundedly_compact hB.
Proof.
move=> A hA [r hr].
have hc : compact ((@inner_finite_synthesis R V B hB n e) @`
    inner_coordinate_cube r).
  apply: continuous_compact; last exact: inner_coordinate_cube_compact.
  apply: continuous_subspaceT; exact: inner_finite_synthesis_continuous.
apply: (subclosed_compact hA hc) => x hx.
exists (fun i => inner_coordinate hB (e i) x).
- move=> i; rewrite set_itvcc /= -ler_norml.
  exact: (le_trans (@inner_orthonormal_coordinate_bound R V B hB n e ho x i)
    (hr x hx)).
- exact (@inner_finite_synthesis_coordinates R V B hB n e he ho x).
Qed.
End FiniteCompactness.

(** Source for [inner_finite_basis_boundedly_compact]: Federer
    1.7.1, p. 28, forward implication for an arbitrary finite basis,
    first replaced by an orthonormal basis as in the preceding paragraph. *)
Theorem inner_finite_basis_boundedly_compact (R : realType)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (u : 'I_n -> V) : is_basis u -> inner_boundedly_compact hB.
Proof.
move=> hu; have [e [he ho]] := orthonormal_basis_exists hB hu.
exact: inner_orthonormal_boundedly_compact he (orthonormalisation_orthonormal ho).
Qed.
