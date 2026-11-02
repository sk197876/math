(** Federer (1969), 2.5.19, p. 113, the norm of K(X), as used for 2.6.6, p.
    120. This public adapter supplies the norm laws and strict uniform
    approximation estimate from the sealed least-bound interface. Source
    context: UniformFunctionNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From mathcomp.analysis.normedtype_theory Require Import pseudometric_normed_Zmodule.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP CompactSupportFunctionLattice
  DaniellSpaceCompactness CompactMaximum UniformFunctionNormUP UniformFunctionNorm UniformFunctionNormLaws
  VectorFunctionLattice FunctionLatticeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_support_vector_lattice]: supporting real
    vector-lattice structure on K(X), Federer 2.5.19, p. 113,
    used in 2.6.6, p. 120. No compactness assumption on X is needed. *)
Lemma compact_support_vector_lattice (R : realType) (X : topologicalType) :
  is_vector_function_lattice (@compactly_supported_continuous_functions R X).
Proof.
split; first exact: compactly_supported_continuous_functions_lattice.
split; first exact: compactly_supported_zero_function.
exact: (@compactly_supported_scale R X).
Qed.

(** Source for [compact_support_uniform_norm_laws]: the seminorm
    laws of nu, Federer 2.5.19, p. 113, supporting 2.6.6, p. 120.
    Point separation is given by uniform_function_norm_separates. *)
Theorem compact_support_uniform_norm_laws (R : realType) (X : topologicalType) :
  is_finite_function_seminorm (@compactly_supported_continuous_functions R X)
    (@compact_support_uniform_norm R X).
Proof.
apply: uniform_function_norm_seminorm; first exact: compact_support_vector_lattice.
exact: (@compact_support_uniform_norm_specification R X).
Qed.

(** Source for [compact_support_uniform_norm_strict_bound]: supporting
    passage from a pointwise strict error to a strict norm error in
    Federer 2.6.6, p. 120. Compact support gives attainment unless
    f is zero; the error is required to be positive. *)
Lemma compact_support_uniform_norm_strict_bound (R : realType) (X : topologicalType)
    (f : X -> R) (e : R) :
  compactly_supported_continuous_functions f -> 0<e ->
  (forall x, `|f x|<e) -> compact_support_uniform_norm f<e.
Proof.
move=> hf he hb; case: (pselect (real_function_support f !=set0))=> hne.
- have hn : continuous (fun x : X => (`|f x| : R^o)).
    move=> x; exact: continuous_comp (hf.1 x) (@norm_continuous R R^o _).
  have [x [hx hmax]] := @continuous_compact_maximum R X (real_function_support f) _ hne hf.2 hn.
  apply: le_lt_trans _ (hb x).
  apply: (@uniform_function_norm_least R X f _ (compact_support_uniform_norm_specification hf) (`|f x|) (normr_ge0 (f x)))=> y.
  case: (pselect (real_function_support f y))=> hy; first exact: hmax y hy.
  rewrite (real_function_zero_off_support hy) normr0; exact: normr_ge0.
- have hf0 : f=(fun _=>0).
    apply: funext=> x; apply: real_function_zero_off_support=> hx; apply: hne; by exists x.
  have hn := compact_support_uniform_norm_specification hf.
  rewrite hf0 in hn.
  rewrite hf0 (uniform_function_norm_unique hn (@uniform_function_norm_zero R X)); exact: he.
Qed.
