(** Federer (1969), 3.3.18, p. 301: compact unit
    directions around the actual approximate normal avoid the tangent. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct InnerNorm InnerNormInequalities InnerMetric InnerNormedTopology
  HilbertFormCompactness InnerProductUP Bilinear BilinearNegation UnitSphereSpace
  MetricSetDistanceUP MetricSetDistanceBasic MetricSetDistanceContinuity RealMetricBackground
  MeasureApproximateTangentUP MeasureApproximateNormalUP RectifiableTangentPlaneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [approximate_normal_unit_directions_compact]: the
    compact set of unit vectors with distance from the ORIGINAL
    approximate normal at most s in Federer 3.3.18, p. 301.
    Original distance is continuous by its abstract infimum laws;
    take a closed sublevel inside the actual compact unit sphere. *)
Lemma approximate_normal_unit_directions_compact (R:realType) n k
    (N:G (R_n R n) k) (d:inner_metric_space (@euclidean_inner_productP R n)->R) (s:R):
  is_metric_set_distance [set u:inner_metric_space (@euclidean_inner_productP R n)|grassmann_val N u] d ->
  compact [set v:inner_metric_space (@euclidean_inner_productP R n)|
    inner_norm (@euclidean_inner_productP R n) v= 1 /\d v<=s].
Proof.
move=>hd.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have hClosed:@closed [the topologicalType of X] [set v:X|d v<=s].
  apply:(@preimage_closed [the topologicalType of X] (real_line_metric R) d [set y|y<=s]).
  - move=>x _; exact:metric_set_distance_continuous hd x.
  - exact:closed_le.
change (compact (@euclidean_unit_sphere_set R n `&` [set v:X|d v<=s])).
exact:compact_closedI (@euclidean_unit_sphere_compact R n) hClosed.
Qed.

(** Source for [approximate_normal_unit_directions_nontangent]:
    the compact-direction exclusion at the end of Federer 3.3.18,
    p. 301. A unit tangent vector has distance at least one from
    its actual polar normal, by Cauchy–Schwarz and the two polar
    signs on the tangent subspace. Thus no such unit vector can
    have distance at most s<1. *)
Theorem approximate_normal_unit_directions_nontangent (R:realType) n m k
    (mu:set (R_n R n)->\bar R) (a:R_n R n)
    (T:G (R_n R n) m) (N:G (R_n R n) k)
    (d:inner_metric_space (@euclidean_inner_productP R n)->R) (s:R):
  measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n)) mu m a=
    [set v|grassmann_val T v] ->
  (forall u,grassmann_val N u <->measure_approximate_normal_cone (@euclidean_inner_productP R n) mu m a u) ->
  is_metric_set_distance [set u:inner_metric_space (@euclidean_inner_productP R n)|grassmann_val N u] d ->
  s<1 ->forall v,inner_norm (@euclidean_inner_productP R n) v= 1 ->d v<=s ->
    ~measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n)) mu m a v.
Proof.
move=>hT hN hd hs v hUnit hDistance hTan.
have hVT:grassmann_val T v.
  have hMember:([set w|grassmann_val T w]) v by rewrite -hT.
  exact:hMember.
have hOpp:measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n)) mu m a (-v).
  rewrite hT -scaleN1r; exact:subspace_scale _ hVT.
have hOne:(1<=d v)%R.
  apply:(metric_set_distance_greatest hd)=>u hu.
  have hNormal:=(hN u).1 hu.
  have hNonpositive:=hNormal v hTan.
  have hNonnegative:=hNormal (-v) hOpp.
  rewrite (bilNr (@euclidean_inner_bilinear R n)) oppr_le0 in hNonnegative.
  have hOrthogonal:@euclidean_inner_product R n u v= 0.
    apply/eqP; by rewrite eq_le hNonpositive hNonnegative.
  have hCauchy:=@inner_cauchy_upper R (R_n R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) (v-u) v.
  rewrite (bilBl (@euclidean_inner_bilinear R n)) hOrthogonal subr0
    -(inner_norm_sqr (@euclidean_inner_productP R n)) hUnit expr1n mulr1 in hCauchy.
  exact:hCauchy.
by have:=le_lt_trans hOne (le_lt_trans hDistance hs); rewrite ltxx.
Qed.
