(** Federer (1969), 3.4.8(11), pp. 334–335:
    the actual prefix norms form the numerical
    family used by the nested neighbourhood proof.
    Continuity, their zero-centre values and equality
    of the full prefix norm with the original
    source norm follow from the existing sealed maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct RealMetricBackground
  NormMetricContinuity NormBoundedLinearTopology NormFiniteLinearBound AnalyticPrefixCoordinatesSealed
  AnalyticPrefixSphereCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_prefix_norm_family_exists]:
    the exact original |p_j(x)| values in
    3.4.8(11), pp. 334–335. Values beyond
    the ambient index have no role and
    are included only to use a natural-index
    finite recursion. The family is a local witness. *)
Theorem analytic_prefix_norm_family_exists (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
    (hDual:forall i k,omega i (e k) = if i==k then 1 else 0):
  exists q:nat->X->R,
    (forall j (hJN:(j<=n)%N) x,q j x = inner_norm (@euclidean_inner_productP R j)
      (@AnalyticPrefixCoordinates.projection R X n omega j hJN x)) /\
    (forall j,continuous (fun x:real_norm_metric_space (inner_norm_real_norm hB)=>
      (q j x:real_line_metric R))) /\
    (forall j,q j 0 = 0) /\forall x,q n x = inner_norm hB x.
Proof.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose q:=fun j (x:X)=>if pselect (j<=n)%N is left hJN then
  inner_norm (@euclidean_inner_productP R j)
    (@AnalyticPrefixCoordinates.projection R X n omega j hJN x) else NX x.
have hEquation j (hJN:(j<=n)%N) x:q j x = inner_norm (@euclidean_inner_productP R j)
    (@AnalyticPrefixCoordinates.projection R X n omega j hJN x).
  rewrite /q;case:(pselect (j<=n)%N)=>h.
  - have hProof:h = hJN:=@bool_irrelevance (j<=n)%N h hJN.
    by rewrite hProof.
  - exfalso;exact:h hJN.
exists q;split;first exact:hEquation.
split.
- move=>j;rewrite /q;case:(pselect (j<=n)%N)=>hJN.
  + pose Y:=R_n R j.
    pose NY:=inner_norm (@euclidean_inner_productP R j).
    pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R j).
    pose P:=@AnalyticPrefixCoordinates.projection R X n omega j hJN.
    have hBound:=@norm_finite_linear_bounded R X Y NX NY hNX hNY n e he P.
    have hContinuous:=@norm_bounded_linear_continuous R X Y NX NY hNX hNY P hBound.
    move=>x;exact:(@continuous_comp (real_norm_metric_space hNX) (real_norm_metric_space hNY)
      (real_line_metric R) (fun y=>P y) (fun y=>NY y) x (hContinuous x)
      (@real_norm_metric_norm_continuous R Y NY hNY (P x))).
  + exact:real_norm_metric_norm_continuous.
- split.
  + move=>j;rewrite /q;case:(pselect (j<=n)%N)=>hJN.
    * by rewrite linear0 inner_norm0.
    * exact:inner_norm0.
  + move=>x;rewrite hEquation.
    pose P:=@AnalyticPrefixCoordinates.projection R X n omega n (leqnn n).
    pose S:=@AnalyticPrefixCoordinates.inclusion R X n e n (leqnn n).
    have hP:=@AnalyticPrefixCoordinates.projection_laws R X n omega n (leqnn n).
    have hS:=@AnalyticPrefixCoordinates.inclusion_laws R X n e n (leqnn n).
    have hSP:S (P x) = x.
      apply:(@analytic_prefix_section_projection_fixed R X B hB n e he hON omega hDual
        n (leqnn n) P S hP hS x)=>i hi.
      have hFalse:=leq_ltn_trans hi (ltn_ord i);by rewrite ltnn in hFalse.
    have hNorm:=@analytic_prefix_section_norm R X B hB n e hON n (leqnn n) S hS (P x).
    rewrite hSP in hNorm;exact:esym hNorm.
Qed.
