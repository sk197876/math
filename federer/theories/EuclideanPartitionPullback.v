(** Federer (1969), 4.1.1, p. 345: transport the already
    proved partition of 3.1.13 to a finite source with its
    original norm. Only linear chart laws and public partition
    properties are used. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness ContinuousMultilinearSealed NormRegularity
  NormRegularityLinearMaps CompactSupportFunctionUP NormPartitionUnityUP NormLocallyFiniteFamilyUP
  FiniteFamilySumUP EuclideanPartitionBallCoverUP EuclideanPartitionFamilyUP EuclideanPartitionFamilyLaws
  FiniteNormEuclideanChart SmoothCompactPartitionUP SmoothPartitionPullbackSupport
  NormLocallyFiniteLinearPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PartitionPullback.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable n:nat.
Variable e:Hom (R_n R n) X.
Variable p:Hom X (R_n R n).
Hypothesis hChart:is_finite_norm_euclidean_chart NX e p.
Local Notation Z := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNR := (@scalar_absolute_value_norm R).
Local Notation V := (fun k=>@ContinuousMultilinear.space R k (R_n R n) R^o NZ (fun t=>`|t|) hNZ hNR).
Local Notation evV := (fun k=>@ContinuousMultilinear.evaluation R k (R_n R n) R^o NZ (fun t=>`|t|) hNZ hNR).
Local Notation VN := (fun k=>@ContinuousMultilinear.norm R k (R_n R n) R^o NZ (fun t=>`|t|) hNZ hNR).
Local Notation hV := (fun k=>@ContinuousMultilinear.laws R k (R_n R n) R^o NZ (fun t=>`|t|) hNZ hNR).
Variables (Phi:set (set Z)) (S:set Z) (sigma:Z->R) (v:Z->Z->R).
Hypothesis ho:forall A,Phi A -> open A.
Hypothesis hS:is_federer_partition_ball_cover Phi S.
Hypothesis hv:is_euclidean_partition_family evV VN Phi S sigma v.
Local Notation U := (\bigcup_(A in Phi) A).
Local Notation UX := (fun x:X=>U (p x)).
Local Notation VX := (fun s:Z=>fun x:X=>v s (p x)).

(** Source for [euclidean_partition_pullback_refines]: compact
    supports of the transported partition refine the transported
    cover, supporting the arbitrary finite source of Federer
    4.1.1, p. 345, by 3.1.13, pp. 224–225. *)
Theorem euclidean_partition_pullback_refines:
  forall s,S s ->exists A,Phi A /\
    @real_function_support R (real_norm_metric_space hNX) (VX s) `<=` (fun x=>A (p x)).
Proof.
move=>s hs.
have [hRef hLocal]:=euclidean_partition_supports_refine ho hS hv.
have [A [hA hSupp]]:=hRef s hs.
exists A; split=>// x hx.
have [z hz hzx]:=@smooth_partition_pullback_support_bound R X NX hNX n e p hChart (v s)
  (partition_family_compact_support hv hs) x hx.
rewrite -hzx (finite_norm_chart_left_inverse hChart).
exact:hSupp z hz.
Qed.

(** Source for [euclidean_partition_pullback]: the transported
    family has the independent smooth compact-partition laws
    in the original source norm, supporting Federer 4.1.1,
    p. 345. No Euclidean norm replaces the given norm NX. *)
Theorem euclidean_partition_pullback:
  is_smooth_compact_partition hNX UX S VX.
Proof.
constructor.
- move=>s hs x; exact:(@euclidean_partition_global_range R n V evV VN Phi S sigma v hv s (p x) hs).
- move=>s hs k.
  exact:(@norm_class_precompose_linear R X (R_n R n) R^o NX NZ (fun t=>`|t|)
    hNX hNZ hNR (fun _=>True) (v s) p k (finite_norm_chart_inverse_bounded hChart)
    (partition_family_global_smooth hv hs k)).
- move=>s hs; exact:(@smooth_partition_pullback_support_compact R X NX hNX n e p hChart (v s)
    (partition_family_compact_support hv hs)).
- move=>s hs x hx; have [A [hA hSub]]:=euclidean_partition_pullback_refines hs.
  exists A=>//; exact:hSub x hx.
- exact:(norm_locally_finite_linear_pullback hNX
    (finite_norm_chart_inverse_bounded hChart)
    (norm_partition_locally_finite (partition_family_partition hv))).
- move=>x hx F hFI hF.
  exact:(norm_partition_sum_one (partition_family_partition hv) hx hFI hF).
Qed.
End PartitionPullback.
