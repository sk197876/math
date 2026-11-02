(** Federer (1969), 1.7.3, p. 29: continuity of the quadratic function
    maximised in the principal-axis argument. We use finite coordinates, not
    differentiation or an imported finite-dimensional bilinear theorem. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology
  OrthonormalFamilies InnerFiniteSynthesis LinearBasis TensorUP.
From Federer Require Import InnerCoordinateContinuity BilinearFiniteCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Section Quadratic.
Variable R : rcfType.
Variable V : lmodType R.
Variable B S : V -> V -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hS : @bilinear R V V R^o S.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.
Local Notation M := (inner_metric_space hB).

(** Source for [quadratic_orthonormal_expansion]: Federer 1.7.3,
    p. 29, supporting expression of S(x,x) as a finite quadratic
    polynomial in the continuous orthonormal coordinates. *)
Lemma quadratic_orthonormal_expansion (x : M) : S x x =
  \sum_i \sum_j (inner_coordinate hB (e i) x * inner_coordinate hB (e j) x) * S (e i) (e j).
Proof.
have hx := @inner_finite_synthesis_coordinates R V B hB n e he ho x.
have hh := @bilinear_finite_expansion R V S hS
  (Finite.clone 'I_n _) (Finite.clone 'I_n _) e e
  (fun i => inner_coordinate hB (e i) x) (fun i => inner_coordinate hB (e i) x).
change (S (inner_finite_synthesis hB e (fun i => inner_coordinate hB (e i) x))
  (inner_finite_synthesis hB e (fun i => inner_coordinate hB (e i) x)) =
  \sum_i \sum_j (inner_coordinate hB (e i) x * inner_coordinate hB (e j) x) * S (e i) (e j)) in hh.
by rewrite hx in hh.
Qed.

(** Source for [quadratic_continuous]: Federer 1.7.3,
    p. 29, continuity used to maximise S(x,x) on the compact set C_j.
    Symmetry is unnecessary for this supporting continuity assertion. *)
Theorem quadratic_continuous : continuous (fun x : M => (S x x : R^o)).
Proof.
have hfun : (fun x : M => (S x x : R^o)) =
  (fun x : M => \sum_i \sum_j
    (inner_coordinate hB (e i) x * inner_coordinate hB (e j) x) * S (e i) (e j)).
  apply: funext => x; exact: quadratic_orthonormal_expansion.
rewrite hfun.
apply: continuous_big; first exact: add_continuous.
move=> i _; apply: continuous_big; first exact: add_continuous.
move=> j _ x.
apply: (@continuousM R (Topological.clone M _)
  (fun x => inner_coordinate hB (e i) x * inner_coordinate hB (e j) x)
  (fun _ => S (e i) (e j)) x); last exact: cst_continuous.
apply: (@continuousM R (Topological.clone M _)
  (fun x => inner_coordinate hB (e i) x) (fun x => inner_coordinate hB (e j) x) x);
  exact: inner_coordinate_continuous.
Qed.
End Quadratic.
