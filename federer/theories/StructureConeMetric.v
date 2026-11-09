(** Federer (1969), 3.3.6, pp. 293–294: use the original
    projection-cone inequality in Euclidean distance coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNorm
  EuclideanProjectionSpace StructureCone StructureProjectionKernel StructureProjectionCone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_projection_cone_metricE]: supporting
    distance form of the original cone in Federer 3.3.6, pp. 293–294,
    using the exact projection identity of 3.3.1, p. 287. Both strict
    inequalities remain, and the original radius may be infinite. *)
Theorem structure_projection_cone_metricE (R:realType) n m (hmn:(m<=n)%N)
    (p:euclidean_projection_space R n m)
    (a b:inner_metric_space (@euclidean_inner_productP R n)) (r: \bar R) (s:R):
  0<s ->
  (structure_cone (structure_projection_kernel hmn p) a r s b <->
    ((mdist a b)%:E<r)%E /\
    mdist (euclidean_projection_linear p a:inner_metric_space (@euclidean_inner_productP R m))
      (euclidean_projection_linear p b)<s*mdist a b).
Proof.
move=>hs; rewrite structure_projection_coneE.
have hA:mdist a b=inner_norm (@euclidean_inner_productP R n) (b-a).
  by rewrite inner_metric_distanceE -[a-b]opprB inner_normN.
have hP:mdist (euclidean_projection_linear p a:inner_metric_space (@euclidean_inner_productP R m))
    (euclidean_projection_linear p b)=
    inner_norm (@euclidean_inner_productP R m) (euclidean_projection_linear p (b-a)).
  by rewrite inner_metric_distanceE -linearB -[a-b]opprB linearN inner_normN.
rewrite hA hP.
have hScale:s*s^-1= 1 by rewrite mulfV // gt_eqF.
split.
- move=>[hSmall hNear]; split; first exact:hNear.
  have hMul:s*(s^-1*inner_norm (@euclidean_inner_productP R m)
      (euclidean_projection_linear p (b-a)))<s*inner_norm (@euclidean_inner_productP R n) (b-a).
    by rewrite ltr_pM2l.
  by rewrite mulrA hScale mul1r in hMul.
- move=>[hNear hSmall]; split; last exact:hNear.
  have hInv:0<s^-1 by rewrite invr_gt0.
  have hMul:s^-1*inner_norm (@euclidean_inner_productP R m)
      (euclidean_projection_linear p (b-a))<s^-1*(s*inner_norm (@euclidean_inner_productP R n) (b-a)).
    by rewrite ltr_pM2l.
  by rewrite mulrA mulVf ?gt_eqF ?mul1r in hMul.
Qed.
