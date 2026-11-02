(** Federer (1969), 3.2.13, p. 251: transitivity of
    O(m) on unit vectors. Existing opaque orthogonal normal charts
    provide the existence proof; their implementations remain hidden. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm OrthogonalMaps EuclideanNormalChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [unit_vector_orthogonal_map_exists]: any two
    unit vectors are related by an orthogonal map, the
    homogeneous-sphere assertion in Federer 3.2.13, p. 251.
    Only the proved abstract inverse, axis and inner-product laws
    of normal charts are used in this existence argument. *)
Lemma unit_vector_orthogonal_map_exists (R:realType) m (u v:R_n R m):
  (0<m)%N ->inner_norm (@euclidean_inner_productP R m) u= 1 ->
  inner_norm (@euclidean_inner_productP R m) v= 1 ->
  exists f:{linear R_n R m->R_n R m},is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R m) f /\f u=v.
Proof.
move=>hm hu hv.
have hU:euclidean_inner_product u u= 1 by rewrite -(inner_norm_sqr (@euclidean_inner_productP R m)) hu expr1n.
have hV:euclidean_inner_product v v= 1 by rewrite -(inner_norm_sqr (@euclidean_inner_productP R m)) hv expr1n.
pose a:=Ordinal hm.
pose F:=euclidean_normal_chart_forward a hV.
pose B:=euclidean_normal_chart_backward a hU.
have hFO:=euclidean_normal_chart_orthogonal a hV.
have hBO:is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R m) B.
  move=>x y.
  have h:=euclidean_normal_chart_orthogonal a hU (B x) (B y).
  rewrite !euclidean_normal_chart_backwardK in h; exact:esym h.
pose f:=linear_comp F B.
exists f; split.
- move=>x y; change (euclidean_inner_product (F (B x)) (F (B y))=euclidean_inner_product x y).
  by rewrite hFO hBO.
- have hB:B u=@coordinate_basis R m a.
    exact:(eq_trans (esym (congr1 B (euclidean_normal_chart_axis a hU)))
      (euclidean_normal_chart_forwardK a hU (@coordinate_basis R m a))).
  change (F (B u)=v); by rewrite hB /F euclidean_normal_chart_axis.
Qed.
