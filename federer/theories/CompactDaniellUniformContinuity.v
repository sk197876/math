(** Federer (1969), 2.6.6, p. 120, together with 2.5.19, p. 113: on a
    compact space X every Daniell integral on K(X), monotone or not, is
    bounded with respect to the norm nu(f) = sup im |f|, hence continuous
    for the distance nu(f - g). This supports the assertion of 2.6.6 that
    the product integral is "uniquely characterized by the condition
    p_a#(mu) = mu_a whenever a in A", among all Daniell integrals on K(X).
    The bound is 2.5.19, p. 113 (formalised as [daniell_sup_norm_bounded]);
    only the difference form is new here. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP DaniellIntegralUP DaniellSpaceCompactSpace
  DaniellSpaceCompactness FunctionLatticeSeminormUP VectorFunctionLattice CompactUniformNorm
  UniformFunctionNormUP UniformFunctionNorm FunctionSeminormDistance DenseScalarContinuousUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactDaniellContinuity.
Variables (R : realType) (X : topologicalType).
Local Notation K := (@compactly_supported_continuous_functions R X).
Local Notation nu := (@compact_support_uniform_norm R X).
Local Notation d := (function_seminorm_distance nu).

(** Source for [compact_daniell_uniform_difference_bound]: supporting
    estimate for the uniqueness assertion of Federer 2.6.6,
    p. 120. By 2.5.19, p. 113, a Daniell integral D on K(X), X
    compact, satisfies |D(h)| <= C nu(h); applied to h = f - g this
    gives |D(f) - D(g)| <= C nu(f - g). Monotonicity of D is not
    assumed. *)
Theorem compact_daniell_uniform_difference_bound (D : (X -> R) -> R) :
  compact (@setT X) -> is_daniell_integral K D ->
  exists C, 0<=C /\ forall f g, K f -> K g -> `|D f-D g|<=C*d f g.
Proof.
move=> hc hD.
have [C [hC hb]] := daniell_sup_norm_bounded hc hD.
exists C; split=> // f g hf hg.
have hK := @compact_support_vector_lattice R X.
have hlin := @daniell_compact_support_linear R X D hD.
have hfg := @vector_function_lattice_difference R X K hK f g hf hg.
have hn := compact_support_uniform_norm_specification hfg.
rewrite -(@vector_lattice_additive_difference R X K D hK hlin.1 f g hf hg).
exact: hb _ hfg _ (uniform_function_norm_nonnegative hn) (uniform_function_norm_bound hn).
Qed.

(** Source for [compact_daniell_uniform_continuous]: every Daniell
    integral on K(X), X compact, is continuous for the norm nu of
    Federer 2.5.19, p. 113, the continuity used for uniqueness in
    2.6.6, p. 120. *)
Theorem compact_daniell_uniform_continuous (D : (X -> R) -> R) :
  compact (@setT X) -> is_daniell_integral K D -> is_scalar_continuous_on_set K d D.
Proof.
move=> hc hD.
have [C [hC hb]] := compact_daniell_uniform_difference_bound hc hD.
move=> f hf e he.
have hC1 : 0<C+1 by rewrite ltr_wpDl.
exists (e/(C+1)); split; first by rewrite divr_gt0.
move=> g hg hfg; apply: le_lt_trans (hb f g hf hg) _.
apply: le_lt_trans (_ : C*(e/(C+1))<e).
  by rewrite ler_wpM2l // ltW.
by rewrite mulrA ltr_pdivrMr // mulrC ltr_pM2l // ltrDl.
Qed.
End CompactDaniellContinuity.
