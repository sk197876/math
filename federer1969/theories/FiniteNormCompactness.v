(** Federer (1969), 1.10.5, p. 48: supporting compactness for the attained
    finite-dimensional mass decomposition. Neither passage is asserted to
    state the compactness lemma below: it supplies general topology for
    Federer. The proof uses the project's norm comparison and closed-bounded
    compactness of an auxiliary Euclidean metric. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import LinearBasis RealNormUP InnerProductUP InnerNorm
  InnerMetric InnerNormedTopology InnerBoundedness InnerFiniteCompactness
  FiniteNormContinuity FiniteNormLowerBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_norm_ball_compact]: Federer 1.10.5,
    p. 48, supporting compact parameter domain for finite products.
    Every closed ball of an arbitrary finite-dimensional norm is
    compact in an auxiliary Euclidean metric. Nonpositive radii and
    the zero-dimensional case require no additional hypotheses. *)
Theorem finite_norm_ball_compact (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (N : V -> R) (hN : is_real_norm N) n (e : 'I_n -> V) (he : is_basis e) r :
  compact [set x : inner_metric_space hB | N x <= r].
Proof.
apply: (@inner_finite_basis_boundedly_compact R V B hB n e he).
- change (closed ((fun x : inner_metric_space hB => (N x:R^o)) @^-1` [set y | y<=r])).
  apply: preimage_closed; last exact: closed_le.
  move=> x _; exact (@finite_seminorm_inner_continuous R V B hB N (proj1 hN) n e he x).
- have [C [hC hc]] := @finite_norm_inner_lower_bound R V B hB N hN n e he.
  exists (C*r)=> x hx; apply: le_trans (hc x) _.
  exact (ler_wpM2l (ltW hC) hx).
Qed.
