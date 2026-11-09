(** Federer (1969), 3.3.20, p. 307: a nonempty open actual projection overlap family. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanRealPlane
  MetricCartesianProductUP EuclideanOneCoordinate EuclideanProjectionSpace EuclideanProjectionMetric
  PlanarProjectionCoefficientLaws PlanarUnitProjectionExistence BinaryProjectionOverlapScalar
  OrthogonalProjectionProbability ProjectionProbabilitySupport RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_projection_strict_overlap_locus]: the interior
    ordered positive-coordinate part of the actual original overlap
    family U in 3.3.20, p. 307. This auxiliary locus is specified by
    strict printed coordinate inequalities; no image or mass is assumed. *)
Definition binary_projection_strict_overlap_locus (R:realType) (s:R):set (euclidean_projection_space R 2 1):=
  [set p|0<planar_projection_second_coefficient p /\
    planar_projection_second_coefficient p<planar_projection_first_coefficient p /\
    (1-2 * s) * planar_projection_first_coefficient p<planar_projection_second_coefficient p /\
    (1-2 * s) * planar_projection_second_coefficient p<s * planar_projection_first_coefficient p].

(** Source for [binary_projection_strict_overlap_open]: continuity of
    actual original projection coordinates proves the strict overlap
    family open, supporting the nondegenerate-direction assertion in
    3.3.20, p. 307. No openness is assumed of projected masses. *)
Theorem binary_projection_strict_overlap_open (R:realType) (s:R):
  open (binary_projection_strict_overlap_locus s).
Proof.
pose P:=euclidean_projection_space R 2 1.
pose U (p:P):R^o:=planar_projection_first_coefficient p.
pose V (p:P):R^o:=planar_projection_second_coefficient p.
have hU:continuous U:=@planar_projection_fixed_scalar_value_continuous R (@euclidean_real_plane_pair R 1 0).
have hV:continuous V:=@planar_projection_fixed_scalar_value_continuous R (@euclidean_real_plane_pair R 0 1).
pose B (p:P):R^o:=U p-V p.
pose C (p:P):R^o:=V p-(1-2 * s) * U p.
pose D (p:P):R^o:=s * U p-(1-2 * s) * V p.
have hB:continuous B by move=>p;exact:cvgB (hU p) (hV p).
have hC:continuous C.
  move=>p;apply:cvgB.
  - exact:(@nbhs_filter P p).
  - exact:hV p.
  - apply:cvgM.
    + exact:(@nbhs_filter P p).
    + apply:cvg_cst;exact:(@nbhs_filter P p).
    + exact:hU p.
have hD:continuous D.
  move=>p;apply:cvgB.
  - exact:(@nbhs_filter P p).
  - apply:cvgM.
    + exact:(@nbhs_filter P p).
    + apply:cvg_cst;exact:(@nbhs_filter P p).
    + exact:hU p.
  - apply:cvgM.
    + exact:(@nbhs_filter P p).
    + apply:cvg_cst;exact:(@nbhs_filter P p).
    + exact:hV p.
have hEqual:binary_projection_strict_overlap_locus s=
    (V @^-1` [set t:R^o|0<t]) `&`
    ((B @^-1` [set t:R^o|0<t]) `&`
    ((C @^-1` [set t:R^o|0<t]) `&` (D @^-1` [set t:R^o|0<t]))).
  apply/seteqP;split=>p;by rewrite /binary_projection_strict_overlap_locus /U /V /B /C /D /preimage /= !subr_gt0.
rewrite hEqual;apply:openI.
- exact:((continuousP V).1 hV _ (@open_gt R 0)).
- apply:openI;first exact:((continuousP B).1 hB _ (@open_gt R 0)).
  apply:openI;[exact:((continuousP C).1 hC _ (@open_gt R 0))|exact:((continuousP D).1 hD _ (@open_gt R 0))].
Qed.

(** Source for [supercritical_original_projection_overlap_nonempty]:
    for m>1/2 the actual original overlap locus has an interior unit
    direction, 3.3.20, p. 307. The existing orthogonal-frame and
    adjoint interfaces realize the strict scalar witness in O*(2,1). *)
Theorem supercritical_original_projection_overlap_nonempty (R:realType) (m:R):
  1/2<m ->m<1 ->exists p,binary_projection_strict_overlap_locus (real_power 2 (-m^-1)) p.
Proof.
move=>hSuper hm1.
have [hUnit [hv [hVU [hMiddle hSide]]]]:=@supercritical_binary_projection_strict_overlap R m hSuper hm1.
have [p hP]:=planar_unit_coordinate_projection_exists hUnit.
have hFirst:planar_projection_first_coefficient p=(2:R)/Num.sqrt 5.
  rewrite /planar_projection_first_coefficient hP
    (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
    (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)) mulr1 mulr0 addr0.
  by [].
have hSecond:planar_projection_second_coefficient p=(1:R)/Num.sqrt 5.
  rewrite /planar_projection_second_coefficient hP
    (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
    (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)) mulr0 mulr1 add0r.
  by [].
exists p.
change (0<planar_projection_second_coefficient p /\
  planar_projection_second_coefficient p<planar_projection_first_coefficient p /\
  (1-2 * real_power 2 (-m^-1)) * planar_projection_first_coefficient p<planar_projection_second_coefficient p /\
  (1-2 * real_power 2 (-m^-1)) * planar_projection_second_coefficient p<real_power 2 (-m^-1) * planar_projection_first_coefficient p).
rewrite hFirst hSecond.
exact:(conj hv (conj hVU (conj hMiddle hSide))).
Qed.

(** Source for [supercritical_original_overlap_positive_probability]:
    the actual normalized projection probability assigns positive mass
    to the original strict overlap family for m>1/2, 3.3.20, p. 307.
    The previously proved full support applies to the proved nonempty
    open locus; no positive-probability direction premise is supplied. *)
Theorem supercritical_original_overlap_positive_probability (R:realType) (m:R):
  (1/2<m)%R ->(m<1)%R ->
  (0<@orthogonal_projection_probability R 2 1 (leqnSn 1)
    (binary_projection_strict_overlap_locus (real_power 2 (-m^-1))))%E.
Proof.
move=>hSuper hm1.
apply:(@theta_star_nonempty_open_positive R 2 1 (leqnSn 1)).
- exact:((@orthogonal_projection_metric_openE R 2 1
    (binary_projection_strict_overlap_locus (real_power 2 (-m^-1)))).2
    (@binary_projection_strict_overlap_open R (real_power 2 (-m^-1)))).
- exact:supercritical_original_projection_overlap_nonempty hSuper hm1.
Qed.
