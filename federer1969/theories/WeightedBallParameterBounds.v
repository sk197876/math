(** Federer (1969), 2.10.40, printed p. 200: compactness bounds the
    prescribed positive radii and the ratios of centre norms to radii, so
    sufficiently large dilations have a feasible centre. A norm bound and a
    positive radius lower bound give the sufficient ratio bound below. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm
  InnerMetric InnerNormedTopology CompactMaximum CompactPositiveScalarBounds
  TopologicalProductMaps WeightedBallMinimumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Parameters.
Variable R : realType.
Variable n : nat.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Variable P : set (E*R^o).

(** Source for [compact_positive_ball_radius_bounds]: supporting
    positive radius lower bound and finite upper bound
    in 2.10.40, p. 200. Both bounds come
    from attained scalar extrema on the compact family. *)
Lemma compact_positive_ball_radius_bounds :
  compact P -> P !=set0 -> positive_ball_parameter_family P ->
  exists lo hi : R, 0<lo /\ 0<hi /\ forall p, P p -> lo<=p.2<=hi.
Proof.
move=> hc hne hpos.
have hf : continuous (@snd E R^o) := @second_projection_continuous E R^o.
have [a [b [ha [hb [hapos hbound]]]]] := @compact_positive_scalar_bounds R
  [the topologicalType of (E*R^o)%type] P snd hne hc hf hpos.
exists a.2,b.2; split=> //; split.
- have /andP [hh _] := hbound b hb; exact: lt_le_trans hapos hh.
- exact hbound.
Qed.

(** Source for [compact_ball_centre_norm_bound]: supporting
    bounded prescribed centres in the first compactness
    step of 2.10.40, p. 200. The bound
    is a nonnegative attained norm value. *)
Lemma compact_ball_centre_norm_bound : compact P -> P !=set0 ->
  exists M : R, 0<=M /\ forall p, P p -> N p.1<=M.
Proof.
move=> hc hne.
have hN : continuous (fun x : E=>(N x : R^o)).
  exact: norm_continuous.
have hf : continuous (fun p : E*R^o=>(N p.1 : R^o)).
  move=> p.
  exact: continuous_comp (@first_projection_continuous E R^o p) (hN p.1).
have [a [ha hmax]] := @continuous_compact_maximum R
  [the topologicalType of (E*R^o)%type] P (fun p=>(N p.1 : R^o)) hne hc hf.
exists (N a.1); split; first exact: inner_norm_nonnegative.
exact hmax.
Qed.

(** Source for [compact_weighted_ball_feasible_scale]: direct
    nonempty feasible dilations in 2.10.40, p. 200.
    A uniform centre-norm bound divided by a positive
    radius lower bound places the origin in Y_t.
    No minimum or contact conclusion is used. *)
Theorem compact_weighted_ball_feasible_scale :
  compact P -> P !=set0 -> positive_ball_parameter_family P ->
  exists t : R, 0<=t /\ weighted_ball_centres P t (0 : E).
Proof.
move=> hc hne hpos.
have [lo [hi [hlo [_ hr]]]] := compact_positive_ball_radius_bounds hc hne hpos.
have [M [hM hbound]] := compact_ball_centre_norm_bound hc hne.
pose t := M/lo.
have ht : 0<=t by rewrite /t divr_ge0 //; exact: ltW hlo.
have hlo0 : lo!=0 by rewrite (gt_eqF hlo).
have he : lo*t=M by rewrite /t mulrCA mulfV // mulr1.
exists t; split=> // p hp.
rewrite sub0r inner_normN.
apply: le_trans (hbound p hp) _; rewrite -he.
have /andP [hlop _] := hr p hp.
exact (ler_wpM2r ht hlop).
Qed.
End Parameters.
