(** Federer (1969), 3.3.17, p. 300: actual nearby
    projections and smaller apertures give contained original cones. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerNorm InnerNormInequalities
  Hom HomInner HomNormBound MetricSubsetBackground EuclideanProjectionSpace EuclideanProjectionMetric
  StructureCone StructureProjectionKernel StructureProjectionCone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projection_metric_difference_bound]:
    supporting the norm inequality in Federer 3.3.17, p. 300.
    The compatible inherited Hilbert metric on original projections
    bounds their actual evaluation difference by the original
    vector norm, by proved 1.7.9. No operator estimate is assumed. *)
Lemma structure_projection_metric_difference_bound (R:realType) n m
    (p q:orthogonal_projection_metric_space R n m) (x:R_n R n):
  inner_norm (@euclidean_inner_productP R m)
    (euclidean_projection_linear p x-euclidean_projection_linear q x)<=
  mdist p q*inner_norm (@euclidean_inner_productP R n) x.
Proof.
have h:=@hom_norm_vector_bound R (R_n R n) (R_n R m)
  (@euclidean_inner_product R n) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n) (val p-val q) x.
rewrite metric_subset_distanceE inner_metric_distanceE.
exact:h.
Qed.

(** Source for [structure_nearby_projection_cone_subset]: the
    ORIGINAL X(a,infinity,ker q,t) subset X(a,infinity,ker p,s)
    inclusion in Federer 3.3.17, p. 300. Prove it for EVERY
    original radius, so the same actual test cutoff remains.
    The metric is compatible with the original Hom topology and
    the actual norm estimate is derived above. *)
Theorem structure_nearby_projection_cone_subset (R:realType) n m (hmn:(m<=n)%N)
    (p q:orthogonal_projection_metric_space R n m)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (r: \bar R) (s t:R):
  0<t ->t<s ->mdist p q<s-t ->
  structure_cone (structure_projection_kernel hmn q) a r t `<=`
    structure_cone (structure_projection_kernel hmn p) a r s.
Proof.
move=>ht hTS hDistance x hx.
have hs:0<s:=lt_trans ht hTS.
have [hAngle hRadius]:=(@structure_projection_coneE R n m hmn q a r t x).1 hx.
pose v:=(x-a)%R.
pose norm:=inner_norm (@euclidean_inner_productP R n) v.
pose normQ:=inner_norm (@euclidean_inner_productP R m) (euclidean_projection_linear q v).
pose normP:=inner_norm (@euclidean_inner_productP R m) (euclidean_projection_linear p v).
have hQ:normQ<t*norm.
  have hMul:t*(t^-1*normQ)<t*norm by rewrite ltr_pM2l.
  by rewrite mulrA mulfV ?gt_eqF // mul1r in hMul.
have hNorm:0<norm.
  have hNQ:0<=normQ:=inner_norm_nonnegative _ _.
  nra.
have hDifference:=@structure_projection_metric_difference_bound R n m p q v.
have hTriangle: normP<=inner_norm (@euclidean_inner_productP R m)
    (euclidean_projection_linear p v-euclidean_projection_linear q v)+normQ.
  have h:=@inner_norm_triangle R (R_n R m) (@euclidean_inner_product R m)
    (@euclidean_inner_productP R m)
    (euclidean_projection_linear p v-euclidean_projection_linear q v) (euclidean_projection_linear q v).
  by rewrite subrK in h.
have hProduct:mdist p q*norm<(s-t)*norm by rewrite ltr_pM2r.
have hP:normP<s*norm.
  have hSmall:=le_lt_trans hDifference hProduct.
  have hSum:=ltrD hSmall hQ.
  rewrite -mulrDl subrK in hSum.
  exact:le_lt_trans hTriangle hSum.
apply:(@structure_projection_coneE R n m hmn p a r s x).2.
split; last exact:hRadius.
have hInverse:0<s^-1 by rewrite invr_gt0.
have hMul:s^-1*normP<s^-1*(s*norm) by rewrite ltr_pM2l.
by rewrite mulrA mulVf ?gt_eqF // mul1r in hMul.
Qed.
