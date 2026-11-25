(** Federer (1969), 4.1.8, p. 362: the original
    affine segment is continuous into the actual domain
    that contains it. Use the existing scalar-orbit and
    norm-addition topology laws, without assuming that
    the whole affine line lies in that domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology normedtype.
From Federer Require Import RealNormUP NormMetric NormMetricContinuity NormMetricScaleContinuity
  RealMetricBackground InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentSegmentParameter CurrentSegmentMapUP CurrentSegmentMapSealed ConvexMetricSegment
  IsotropyGroupTopology TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Section CurrentSegmentMapContinuity.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Q := (current_segment_parameter R).
Variable A:set X.
Variables u v:X.

(** Source for [current_segment_map_continuous]: the original
    specified segment map is continuous on its actual compact
    parameter carrier, supporting Federer 4.1.8, p. 362,
    by the original vector topology laws of 4.1.1. *)
Theorem current_segment_map_continuous (f:Q->current_domain R n A):
  @is_current_segment_map R n A u v f->continuous f.
Proof.
move=>hF.
apply:(@set_type_continuous_into XT A Q f).
have hSame:(fun t:Q=>set_val (f t))=(fun t:Q=>u+(set_val t)*:(v-u)).
  apply:funext=>t;exact:hF t.
change (continuous (fun t:Q=>(set_val (f t):XT))).
rewrite hSame.
have hScalar:continuous (fun t:Q=>(set_val t:real_line_metric R)).
  exact:(@set_type_val_continuous (real_line_metric R) (`[0,1]:set (real_line_metric R))).
have hOrbit:continuous (fun t:Q=>((set_val t)*:(v-u):XT)).
  move=>t;exact:(continuous_comp (hScalar t)
    (@real_norm_metric_scalar_orbit_continuous R X NX hNX (v-u) (set_val t))).
have hConst:continuous (fun _:Q=>(u:XT)).
  move=>t;exact:(@cvg_cst [the topologicalType of XT] u Q _ (@nbhs_filter Q t)).
have hPair:continuous (fun t:Q=>((u:XT),((set_val t)*:(v-u):XT))).
  exact:(@topological_pair_continuous Q XT XT (fun _=>u)
    (fun t=>(set_val t)*:(v-u)) hConst hOrbit).
move=>t;exact:(continuous_comp (hPair t)
  (@real_norm_metric_add_continuous R X NX hNX (u,(set_val t)*:(v-u)))).
Qed.

(** Source for [current_segment_opaque_map_continuous]: the
    original opaque map has the proved continuity law,
    supporting Federer 4.1.8, p. 362. *)
Theorem current_segment_opaque_map_continuous
    (hSegment:@is_current_segment_domain R n A u v):
  continuous (@SegmentCurrentPath.value R n A u v hSegment).
Proof. exact:(current_segment_map_continuous (@SegmentCurrentPath.laws R n A u v hSegment)). Qed.
End CurrentSegmentMapContinuity.
