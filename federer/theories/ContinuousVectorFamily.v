(** Federer (1969), 2.5.20, p. 114: continuous vector-valued functions form
    the space Q used in the application of 2.5.12. For compact X its scalar
    pairings and norm belong to K(X), and the radial split supplies the last
    clause of 2.5.12(4), p. 103. Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormMetricContinuity
  NormMetricScaleContinuity TopologicalProductMaps CompactSupportFunctionUP
  VectorDaniellHypotheses ContinuousRadialSplitLaws ContinuousRadialSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_normed_functions]: the continuous
    vector families Q in Federer 2.5.20, p. 114,
    stated for an arbitrary normed coefficient space before
    taking E=K(Y). *)
Definition continuous_normed_functions (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N) : set (X -> E) :=
  [set w | continuous (w : X -> real_norm_metric_space hN)].

(** Source for [continuous_normed_functions_vector_space]:
    Q is a vector space in Federer 2.5.20, p. 114,
    as required by 2.5.12(4), p. 103. *)
Theorem continuous_normed_functions_vector_space (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N) :
  is_vector_function_space (@continuous_normed_functions R X E N hN).
Proof.
constructor.
- exact: cst_continuous.
- move=> w v hw hv x; exact: continuous_comp (cvg_pair (hw x) (hv x))
    (@real_norm_metric_add_continuous R E N hN (w x,v x)).
- move=> c w hw x; exact: continuous_comp (hw x)
    (@real_norm_metric_scale_continuous R E N hN c (w x)).
Qed.

(** Source for [continuous_on_compact_is_compactly_supported]:
    K(X) comprises all continuous scalar functions when X is
    compact, supporting Federer 2.5.20, p. 114. *)
Lemma continuous_on_compact_is_compactly_supported (R : realType) (X : topologicalType)
    (f : X -> R) : compact (@setT X) -> continuous (f : X -> real_line_metric R) ->
  compactly_supported_continuous_functions f.
Proof.
move=> hX hf; split=> //.
exact: subclosed_compact (@real_function_support_closed R X f) hX (@subsetT _ _).
Qed.

(** Source for [continuous_normed_functions_compact_module]:
    all clauses of 2.5.12(4), p. 103, for the
    continuous-family space of Federer 2.5.20, p. 114.
    The radial split remains continuous at zero. *)
Theorem continuous_normed_functions_compact_module (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N) :
  compact (@setT X) -> is_vector_lattice_module hN
    (@compactly_supported_continuous_functions R X) (@continuous_normed_functions R X E N hN).
Proof.
move=> hX; constructor.
- move=> f y hf x; exact: continuous_comp (hf.1 x)
    (@real_norm_metric_scalar_orbit_continuous R E N hN y (f x)).
- move=> w alpha hw ha; apply: (@continuous_on_compact_is_compactly_supported R X (fun x => alpha (w x)) hX).
  move=> x; exact: continuous_comp (hw x) (ha.2 (w x)).
- move=> w hw; apply: (@continuous_on_compact_is_compactly_supported R X (fun x => N (w x)) hX).
  move=> x; exact: continuous_comp (hw x) (@real_norm_metric_norm_continuous R E N hN (w x)).
- move=> w f hw hf hb; exists (fun x => norm_radial_split N (w x) (f x)); split.
  + exact: (@norm_radial_split_continuous R X E N hN w f hw hf.1.1 hf.2 hb).
  + split.
    * move=> x; exact: (@norm_radial_split_norm R E N hN (w x) (f x) (hf.2 x) (hb x)).
    * move=> x; exact: (@norm_radial_split_product R E N hN (w x) (f x)).
Qed.
