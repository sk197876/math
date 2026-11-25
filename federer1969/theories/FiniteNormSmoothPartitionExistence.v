(** Federer (1969), 4.1.1, p. 345: the associated smooth
    partition of unity for an arbitrary finite normed source,
    obtained from the already proved Euclidean 3.1.13,
    pp. 224–225. No new partition construction is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric InnerNorm HilbertFormCompactness ContinuousMultilinearSealed CompactSupportFunctionUP
  EuclideanPartitionBallCoverUP EuclideanPartitionFamilyUP EuclideanSmoothPartition
  FiniteNormEuclideanChart SmoothCompactPartitionUP EuclideanPartitionPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_norm_smooth_partition_exists]: every
    open cover of a finite normed source union has a countable
    locally finite smooth partition with compact subordinate
    supports, as used in Federer 4.1.1, p. 345, by 3.1.13,
    pp. 224–225. The given norm, empty domain and dimension
    zero are retained. *)
Theorem finite_norm_smooth_partition_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X)
    (hb:is_basis b) (Phi:set (set (real_norm_metric_space hNX))):
  (forall A,Phi A -> open A) ->
  exists (J:choiceType) (I:set J) (v:J->X->R),
    countable I /\ is_smooth_compact_partition hNX (\bigcup_(A in Phi) A) I v /\
    forall s,I s ->exists A,Phi A /\
      @real_function_support R (real_norm_metric_space hNX) (v s) `<=` A.
Proof.
move=>hPhi.
have [e [p hChart]]:=finite_norm_euclidean_chart_exists hNX hb.
pose Z:=inner_metric_space (@euclidean_inner_productP R n).
pose NZ:=inner_norm (@euclidean_inner_productP R n).
pose hNZ:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNR:=@scalar_absolute_value_norm R.
pose W:=fun k=>@ContinuousMultilinear.space R k (R_n R n) R^o NZ (fun t=>`|t|) hNZ hNR.
pose ew:=fun k=>@ContinuousMultilinear.evaluation R k (R_n R n) R^o NZ (fun t=>`|t|) hNZ hNR.
pose WN:=fun k=>@ContinuousMultilinear.norm R k (R_n R n) R^o NZ (fun t=>`|t|) hNZ hNR.
pose hW:=fun k=>@ContinuousMultilinear.laws R k (R_n R n) R^o NZ (fun t=>`|t|) hNZ hNR.
pose PhiZ:set (set Z):=[set V|exists A,Phi A /\ V=[set z:Z|A (e z)]].
have hForward:continuous (fun z:Z=>(e z:real_norm_metric_space hNX)):=
  @finite_norm_chart_forward_continuous R X NX hNX n e p hChart.
have hOpen:forall V,PhiZ V -> @open [the topologicalType of Z] V.
  move=>V [A [hA ->]]; exact:(continuousP _).1 hForward A (hPhi A hA).
have [Dmu [G [Vcoeff [hMu [hG [hV hExists]]]]]]:=
  @federer_smooth_partition_exists R n W ew WN hW.
have [S [sigma [v [hS [hv [hSigma hDer]]]]]]:=hExists PhiZ hOpen.
have hPull:=@euclidean_partition_pullback R X NX hNX n e p hChart PhiZ S sigma v hOpen hS hv.
have hRef:=@euclidean_partition_pullback_refines R X NX hNX n e p hChart PhiZ S sigma v hOpen hS hv.
have hDomain:(fun x:X=>(\bigcup_(V in PhiZ) V) (p x))=(fun x:X=>(\bigcup_(A in Phi) A) x).
  apply:funext=>x; apply:propext; split.
  - move=>[V [A [hA hEq]] hxV].
    exists A=>//; move:hxV; by rewrite hEq /= (finite_norm_chart_right_inverse hChart).
  - move=>[A hA hxA].
    exists [set z:Z|A (e z)]; first by exists A.
    by rewrite /= (finite_norm_chart_right_inverse hChart).
rewrite hDomain in hPull.
exists [the choiceType of Z],S,(fun s x=>v s (p x)); split.
- exact:partition_ball_centers_countable hS.
- split; first exact hPull.
  move=>s hs; have [V [[A [hA hEq]] hSupp]]:=hRef s hs.
  exists A; split=>// x hx.
  have h:=hSupp x hx.
  by rewrite hEq /= (finite_norm_chart_right_inverse hChart) in h.
Qed.
