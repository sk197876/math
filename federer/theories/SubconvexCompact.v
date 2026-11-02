(** Federer (1969), 1.8.1, p. 38: compactness underlying the convex-hull and
    mass-decomposition argument. Here the dimension reduction and compact
    coefficient domains are proved locally. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology
  CoefficientSimplex SubconvexCombinations SubconvexReduction LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Compactness.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation M := (inner_metric_space hB).
Variable S : set M.
Hypothesis hS : compact S.

(** Source for [weighted_tuple_map]: Federer 1.8.1, p. 38,
    supporting parameter map from a coefficient tuple and a point tuple
    to their weighted sum. *)
Definition weighted_tuple_map n (z : ('I_n -> R^o) * ('I_n -> M)) : M :=
  \sum_i z.1 i *: z.2 i.

(** Source for [weighted_tuple_map_continuous]: Federer 1.8.1,
    p. 38, supporting continuity of finite weighted sums, using only
    the vector-space operations and general topological continuity. *)
Lemma weighted_tuple_map_continuous n : continuous (@weighted_tuple_map n).
Proof.
apply: continuous_big; first exact: add_continuous.
move=> i _ z; apply: continuousZ.
- have hf : {for z, continuous (fun w : ('I_n -> R^o) * ('I_n -> M) => w.1)}.
    exact: cvg_fst.
  have hg : {for z.1, continuous (fun a : 'I_n -> R^o => a i)}.
    exact: proj_continuous.
  exact: (continuous_comp hf hg).
- have hf : {for z, continuous (fun w : ('I_n -> R^o) * ('I_n -> M) => w.2)}.
    exact: cvg_snd.
  have hg : {for z.2, continuous (fun u : 'I_n -> M => u i)}.
    exact: proj_continuous.
  exact: (continuous_comp hf hg).
Qed.

(** Source for [subconvex_level]: Federer 1.8.1, p. 38,
    supporting set of combinations with a fixed number of slots. *)
Definition subconvex_level n : set M := @weighted_tuple_map n @`
  (@coefficient_simplex R n `*` [set u : 'I_n -> M | forall i, S (u i)]).

(** Source for [subconvex_level_compact]: Federer 1.8.1,
    p. 38, supporting compactness of fixed-length combinations of
    points of a compact set. The zero-slot domain is included. *)
Lemma subconvex_level_compact n : compact (subconvex_level n).
Proof.
apply: continuous_compact; first apply: continuous_subspaceT; first exact: weighted_tuple_map_continuous.
apply: compact_setX; first exact: coefficient_simplex_compact.
exact (@tychonoff _ (fun _ : 'I_n => (Topological.clone M _)) (fun _ => S) (fun _ => hS)).
Qed.

(** Source for [subconvex_combinations_compact]: Federer 1.8.1,
    p. 38, supporting compactness of the convex-combination set in
    finite dimension. Local coefficient elimination reduces to a finite
    union of the compact fixed-length domains, without importing a
    Caratheodory or convex-body theorem. *)
Theorem subconvex_combinations_compact d (e : 'I_d -> V) (he : is_basis e) :
  compact (@subconvex_combinations R V S : set M).
Proof.
have heq : @subconvex_combinations R V S =
    \bigcup_(k in [set` (predT : pred 'I_d.+1)]) subconvex_level (val k).
  apply/seteqP; split=> x.
  - move=> [n [u [a [hu [ha [hs hx]]]]]].
    have [k [v [c [hk [hv [hc [hcs hcv]]]]]]] :=
      @subconvex_dimension_reduction R V d e he S n u a hu ha hs.
    have hkd : (k < d.+1)%N by rewrite ltnS.
    exists (Ordinal hkd) => //.
    exists (c,v); first by split; [split | ].
    change (\sum_i c i *: v i = x); exact: esym (eq_trans hx hcv).
  - move=> [k _ [[a u] [[ha hs] hu] hx]].
    exists (val k), u, a; repeat split=> //; exact: esym hx.
rewrite heq bigcup_pred; apply: bigsetU_compact => k _.
exact: subconvex_level_compact.
Qed.
End Compactness.
