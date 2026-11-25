(** Federer (1969), 4.1.18, pp. 375–377: the L1
    pair cost uses the original Lebesgue measure over the
    actual open U. This is the existing open-subspace measure
    of 2.1.2, p. 54, not a new normalization. Its Radon
    laws follow by tracing the already proved full-domain measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentDomain CurrentDomainGeometry
  EuclideanFullDomainMeasure EuclideanLebesgueDimensions OpenSubspaceMeasure
  OpenSubtypeTraceMeasure MeasureImagePullback MeasurePushforward MeasureRestriction
  MeasureUP RadonMeasureUP IsotropyGroupTopology SubtypeCompactHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_open_domain_measure]: the original
    Lebesgue measure over U in the Omega_m and J definitions,
    Federer 4.1.18, p. 375. The source point type is exactly
    the old current domain, including empty U and R^0. *)
Definition euclidean_open_domain_measure (R:realType) n
    (U:set (R_n R n)):set (current_domain R n U)->\bar R:=
  @open_subspace_measure R (R_n R n) U (@euclidean_lebesgue_measure R n).

(** Source for [euclidean_open_domain_measure_full_trace]:
    this same original measure is the trace of its full-domain
    copy, by 2.1.2, p. 54, supporting the original-U integrals
    of Federer 4.1.18, pp. 375–377. No point outside U is chosen. *)
Lemma euclidean_open_domain_measure_full_trace (R:realType) n
    (U:set (R_n R n)):
  @euclidean_open_domain_measure R n U=
    @open_subtype_trace_measure R
      (real_norm_metric_space (inner_norm_real_norm
        (@euclidean_inner_productP R n))) U setT
      (fun _ _=>Logic.I) (@euclidean_full_domain_measure R n).
Proof.
apply:funext=>A.
rewrite /euclidean_open_domain_measure /open_subtype_trace_measure
  /measure_image_pullback /euclidean_full_domain_measure /open_subspace_measure.
congr (@euclidean_lebesgue_measure R n);apply/seteqP;split.
- move=>x [y hy hxy].
  exists (@open_subtype_inclusion
    (real_norm_metric_space (inner_norm_real_norm
      (@euclidean_inner_productP R n))) U setT (fun _ _=>Logic.I) y).
  + by exists y.
  + exact:hxy.
- move=>x [z [y hy hyz] hzx].
  exists y;first exact:hy.
  by rewrite -hyz in hzx.
Qed.

(** Source for [euclidean_open_domain_measure_laws]: Lebesgue
    measure over the original open U has the measure and Radon
    laws required for the L1 pair representation, Federer 4.1.18,
    pp. 375–377, through the earlier local representation of
    4.1.7, pp. 355–358. Empty U remains allowed. *)
Theorem euclidean_open_domain_measure_laws (R:realType) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x):
  is_measure (@euclidean_open_domain_measure R n U) /\
  is_radon_measure (@euclidean_open_domain_measure R n U).
Proof.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose XT:=real_norm_metric_space hNX.
pose mu:=@euclidean_full_domain_measure R n.
pose inc:=fun (x:X) (_:U x)=>Logic.I.
have hFull:=@euclidean_full_domain_measure_laws R n.
have hOpen:@open XT U.
  rewrite openE=>x hx.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).1 (@hU x hx).
have hHaus:hausdorff_space (current_domain R n U).
  exact:(@set_type_hausdorff XT U (@metric_hausdorff R XT)).
rewrite euclidean_open_domain_measure_full_trace;split.
- exact:(@open_subtype_trace_is_measure R XT U setT inc mu hFull.1).
- exact:(@open_subtype_trace_radon R XT U setT inc mu hFull.1 hFull.2
    hOpen hHaus (@current_domain_locally_compact R n U hU)).
Qed.

(** Source for [euclidean_open_domain_measure_ambient]: the
    inclusion image is precisely the original restriction to U,
    by 2.1.2, p. 54. This gives the same literal U integrals
    in Federer 4.1.18, pp. 375–377, with no conull domain replaced. *)
Theorem euclidean_open_domain_measure_ambient (R:realType) n
    (U:set (R_n R n)):
  measure_pushforward (set_val:current_domain R n U->R_n R n)
    (@euclidean_open_domain_measure R n U)=
    measure_restrict (@euclidean_lebesgue_measure R n) U.
Proof.
exact:(@open_subspace_measure_pushforward R
  (real_norm_metric_space (inner_norm_real_norm
    (@euclidean_inner_productP R n))) U (@euclidean_lebesgue_measure R n)).
Qed.
