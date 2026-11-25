(** Federer (1969), 2.5.20, p. 114: the linear isomorphism S sends a
    norm-continuous family to its jointly continuous evaluation. Conversely,
    joint continuity over a compact factor gives continuity in the uniform
    norm. These supporting topology facts use only the abstract K(Y)
    interface. Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric RealMetricBackground CompactSupportFunctionUP
  CompactFunctionSpaceUP CompactFunctionSpaceLaws CompactSectionUniform TopologicalProductMaps
  UniformFunctionNorm UniformFunctionNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Joint.
Variable R : realType.
Variable Y : topologicalType.
Variable E : lmodType R.
Variable ev : E -> Y -> R.
Hypothesis hE : is_compact_function_space ev.
(** Source for [N]: uniform norm of E=K(Y), Federer 2.5.20, p. 114. *)
Let N := compact_function_norm ev.
(** Source for [hN]: proved norm laws supporting Federer 2.5.20, p. 114. *)
Let hN : is_real_norm N := compact_function_norm_laws hE.
Local Notation V := (real_norm_metric_space hN).

(** Source for [compact_function_joint_evaluation_continuous]:
    supporting continuity of S(w)(x,y)=w(x)(y) in Federer
    2.5.20, p. 114. The norm bound controls changes
    in the function, and its own continuity controls changes
    in the argument. *)
Theorem compact_function_joint_evaluation_continuous :
  continuous (fun p : V*Y => (ev p.1 p.2 : real_line_metric R)).
Proof.
move=> [a b] U hU.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP (ev a b : real_line_metric R) U) hU.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have hb0 : nbhs (ev a b : real_line_metric R) [set t | `|ev a b-t|<e/2].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (ev a b : real_line_metric R) _)).
  exists (e/2)=> // t ht; exact ht.
have hb : nbhs b [set y | `|ev a b-ev a y|<e/2].
  exact: ((compact_function_evaluation_member hE a).1 b _ hb0).
exists ([set v : V | mdist a v<e/2], [set y | `|ev a b-ev a y|<e/2]).
- split=> //; apply: (proj2 (metricType_numDomainType.nbhs_mdistP a _)).
  exists (e/2)=> // v hv; exact hv.
- move=> [v y] [hv hy]; apply: hball.
  change (`|ev a b-ev v y|<e).
  have hbound : `|ev a y-ev v y|<=N (a-v).
    have h := compact_function_evaluation_bound hE (a-v) y.
    by rewrite (compact_function_evaluation_subtract hE) in h.
  have hnear : `|ev a y-ev v y|<e/2 := le_lt_trans hbound hv.
  have heq : ev a b-ev v y=(ev a b-ev a y)+(ev a y-ev v y).
    by rewrite addrA subrK.
  rewrite heq; apply: le_lt_trans (ler_normD _ _) _.
  have h := ltrD hy hnear; by rewrite -splitr in h.
Qed.

(** Source for [compact_function_uncurry_continuous]: the
    well-definedness of S in Federer 2.5.20, p. 114,
    on norm-continuous families of functions. *)
Lemma compact_function_uncurry_continuous (X : topologicalType) (w : X -> V) :
  continuous w -> continuous (fun p : X*Y => (ev (w p.1) p.2 : real_line_metric R)).
Proof.
move=> hw.
have hp : continuous (fun p : X*Y => ((w p.1,p.2) : V*Y)).
  apply: topological_pair_continuous.
  - move=> p; exact: continuous_comp (@first_projection_continuous X Y p) (hw p.1).
  - exact: second_projection_continuous.
move=> p; exact (continuous_comp (hp p) (@compact_function_joint_evaluation_continuous (w p.1,p.2))).
Qed.

(** Source for [compact_function_curry_continuous]: the inverse
    map to S in Federer 2.5.20, p. 114, is norm
    continuous because the Y factor is compact. No choice of
    a concrete realization of K(Y) enters the estimate. *)
Theorem compact_function_curry_continuous (X : topologicalType) (w : X -> E) :
  compact (@setT Y) ->
  continuous (fun p : X*Y => (ev (w p.1) p.2 : real_line_metric R)) ->
  continuous (w : X -> V).
Proof.
move=> hY hh a U hU.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP (w a : V) U) hU.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have ht : continuous (fun p : Y*X => (ev (w p.2) p.1 : real_line_metric R)).
  have hp : continuous (fun p : Y*X => (p.2,p.1)).
    apply: topological_pair_continuous; [exact: second_projection_continuous|exact: first_projection_continuous].
  move=> p; exact: continuous_comp (hp p) (hh (p.2,p.1)).
have [W [hW [ha hnear]]] := @compact_sections_locally_uniform R Y X
  (fun p : Y*X => ev (w p.2) p.1) setT a (e/2) ht hY he2.
have hn : nbhs a W by rewrite openE in hW; exact: hW a ha.
apply: (@filterS _ _ (@nbhs_filter X a) W _ _ hn)=> x hx.
apply: hball.
change (N (w a-w x)<e).
have hehalf : e/2<e by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
apply: le_lt_trans _ hehalf.
apply: (@uniform_function_norm_least R Y (ev (w a-w x)) _
  (compact_support_uniform_norm_specification (compact_function_evaluation_member hE (w a-w x)))
  (e/2) (ltW he2))=> y.
rewrite (compact_function_evaluation_subtract hE) -opprB normrN.
exact: ltW (hnear x y hx I).
Qed.
End Joint.
