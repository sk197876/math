(** Federer (1969), 1.7.6, pp. 33-34: existence of the linear operator norm
    in finite dimension. This private witness uses the bounded compactness
    established in 1.7.1 and the project's quadratic continuity lemma, not
    an imported operator norm. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerMetric
  InnerNormedTopology InnerBoundedness InnerFiniteCompactness
  TensorUP LinearBasis GramSchmidt OrthonormalisationUP BilinearPrecompose
  QuadraticContinuity CompactMaximum OperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [operator_norm_exists]: Federer 1.7.6, p. 33,
    the finite-dimensional closed unit ball supplies an attained
    supremum. The target may have arbitrary dimension: only the
    real quadratic function x -> f(x).f(x) is maximised. *)
Theorem operator_norm_exists (R : realType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b) (f : {linear V -> U}) :
  exists L, is_operator_norm hB hC f L.
Proof.
have [e [he ho]] := orthonormal_basis_exists hB hb.
have horth := orthonormalisation_orthonormal ho.
pose S := fun x y => C (f x) (f y).
have hS : @bilinear R V V R^o S :=
  @bilinear_linear_precompose R V V U U R^o C (inner_bilinear hC) f f.
have hc := @quadratic_continuous R V B S hB hS n e he horth.
have hcompact := @inner_unit_ball_compact R V B hB
  (@inner_finite_basis_boundedly_compact R V B hB n b hb).
have hne : (@inner_unit_ball R V B hB) !=set0.
  exists 0; change (inner_norm hB (0 : V) <= 1).
  by rewrite inner_norm0.
have [x [hx hm]] := @continuous_compact_maximum R
  (Topological.clone (inner_metric_space hB) _) ((@inner_unit_ball R V B hB))
  (fun x => (S x x : R^o)) hne hcompact hc.
exists (inner_norm hC (f x)); constructor.
- move=> y hy.
  rewrite -(ler_sqr (inner_norm_nonnegative hC _) (inner_norm_nonnegative hC _))
    !inner_norm_sqr.
  exact: hm y hy.
- by exists x.
Qed.
