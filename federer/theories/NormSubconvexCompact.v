(** Federer (1969), 2.10.21, p. 184: compactness of finite-dimensional
    compact convex hulls. This supporting finite-combination argument works
    directly in the topology of the supplied abstract norm. Reuse the proved
    coefficient dimension reduction from Chapter 1, rather than an external
    convex-body theorem. Neither source is claimed to state the auxiliary
    subconvex formulation used here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormMetricContinuity
  NormMetricJointScale TopologicalProductMaps CoefficientSimplex SubconvexCombinations
  SubconvexReduction LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Combinations.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Local Notation M := (real_norm_metric_space hN).
Variable S : set M.
Hypothesis hS : compact S.

(** Source for [norm_weighted_tuple_map]: supporting coefficient/point
    parameter map for compact hulls, 2.10.21, p. 184 *)
Definition norm_weighted_tuple_map n (z : ('I_n -> R^o)*('I_n -> M)) : M :=
  \sum_i z.1 i *: z.2 i.

(** Source for [norm_weighted_tuple_map_continuous]: supporting
    continuity of the finite weighted-sum map in
    2.10.21, p. 184, with the supplied norm
    topology and its proved operation laws. *)
Lemma norm_weighted_tuple_map_continuous n : continuous (@norm_weighted_tuple_map n).
Proof.
apply: continuous_big; first exact: real_norm_metric_add_continuous.
move=> i _.
have hf : continuous (fun z : ('I_n -> R^o)*('I_n -> M) => (z.1 i : real_line_metric R)).
  move=> z; exact: continuous_comp (@first_projection_continuous [the topologicalType of ('I_n -> R^o)] [the topologicalType of ('I_n -> M)] z) (@proj_continuous 'I_n (fun _=>R^o) i z.1).
have hg : continuous (fun z : ('I_n -> R^o)*('I_n -> M) => z.2 i).
  move=> z; exact: continuous_comp (@second_projection_continuous [the topologicalType of ('I_n -> R^o)] [the topologicalType of ('I_n -> M)] z) (@proj_continuous 'I_n (fun _=>M) i z.2).
have hp := topological_pair_continuous hf hg.
move=> z; exact: continuous_comp (hp z) (@real_norm_metric_joint_scale_continuous R V N hN (z.1 i,z.2 i)).
Qed.

(** Source for [norm_subconvex_level]: supporting image
    of a compact coefficient simplex and a compact
    power of S, for 2.10.21, p. 184. *)
Definition norm_subconvex_level n : set M := @norm_weighted_tuple_map n @`
  (@coefficient_simplex R n `*` [set u : 'I_n -> M | forall i, S (u i)]).

(** Source for [norm_subconvex_level_compact]: supporting
    fixed-length compact parameter image for
    2.10.21, p. 184; zero slots are included. *)
Lemma norm_subconvex_level_compact n : compact (norm_subconvex_level n).
Proof.
apply: continuous_compact; first apply: continuous_subspaceT; first exact: norm_weighted_tuple_map_continuous.
apply: compact_setX; first exact: coefficient_simplex_compact.
exact: (@tychonoff 'I_n (fun _=>M) (fun _=>S) (fun _=>hS)).
Qed.

(** Source for [norm_subconvex_combinations_compact]: supporting
    compactness of subconvex combinations in finite
    dimension for 2.10.21, p. 184. The
    proved dimension reduction gives a finite union
    of compact fixed-length parameter images. *)
Theorem norm_subconvex_combinations_compact d (e : 'I_d -> V) :
  is_basis e -> compact (@subconvex_combinations R V S : set M).
Proof.
move=> he.
have heq : @subconvex_combinations R V S=
    \bigcup_(k in [set` (predT : pred 'I_d.+1)]) norm_subconvex_level (val k).
  apply/seteqP; split=> x.
  - move=> [n [u [a [hu [ha [hs hx]]]]]].
    have [k [v [c [hk [hv [hc [hcs hcv]]]]]]] :=
      @subconvex_dimension_reduction R V d e he S n u a hu ha hs.
    have hkd : (k<d.+1)%N by rewrite ltnS.
    exists (Ordinal hkd)=> //.
    exists (c,v); first by split; [split|].
    change (\sum_i c i*:v i=x); exact: esym (eq_trans hx hcv).
  - move=> [k _ [[a u] [[ha hs] hu] hx]].
    exists (val k),u,a; repeat split=> //; exact: esym hx.
rewrite heq bigcup_pred; apply: bigsetU_compact=> k _; exact: norm_subconvex_level_compact.
Qed.
End Combinations.
