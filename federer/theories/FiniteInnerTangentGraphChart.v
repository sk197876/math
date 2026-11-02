(** Federer (1969), 3.2.28, pp. 265–267:
    Euclidean coordinates of the actual tangent partial
    differential retain exactly its original tangent domain.
    Tangent transport uses the invertible linear chart law
    of 3.1.21, p. 234. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm HilbertFormCompactness NormDifferentialUP NormLinearIsometryInverse
  NormLinearIsomorphismTangent TangentConeUP FiniteInnerChartUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_tangent_partial_graph_chart]:
    the exact tangent-domain coordinate graph used for
    the Jacobians in Federer 3.2.28, pp. 265–267.
    Source and target maps are the actual chart and
    derivative compositions, without an extension on a
    missing tangent direction. *)
Theorem finite_inner_tangent_partial_graph_chart (R:realType) (X Y:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n k
    (e:Hom (R_n R n) X) (p:Hom X (R_n R n)) (t:Hom Y (R_n R k))
    (S:set X) a (T:subspace X) (L:Hom X Y):
  is_finite_inner_chart B e p ->norm_tangent_cone (inner_norm hB) S a=(T:set X) ->
  forall v w,partial_function_graph
    (partial_function_source_restrict
      (norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) (p @` S) (p a))
      (partial_function_total (hom_comp t (hom_comp L e)))) v w <->
    exists u:subspace_space T,p (subspace_val u)=v /\t (L (subspace_val u))=w.
Proof.
move=>hChart hTan.
have hP:norm_bounded_linear (inner_norm hB) (inner_norm (@euclidean_inner_productP R n)) p.
  apply:norm_linear_isometry_bounded=>x; exact:(@finite_inner_chart_inverse_norm R X B hB n e p hChart x).
have hE:norm_bounded_linear (inner_norm (@euclidean_inner_productP R n)) (inner_norm hB) e.
  apply:norm_linear_isometry_bounded=>x; exact:(@finite_inner_chart_norm R X B hB n e p hChart x).
have hImage:=@norm_linear_isomorphism_tangent_image R X (R_n R n)
  (inner_norm hB) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm hB) (inner_norm_real_norm (@euclidean_inner_productP R n))
  p e S a hP hE (finite_inner_chart_right_inverse hChart) (finite_inner_chart_left_inverse hChart).
rewrite hTan in hImage.
move=>v w; split.
- move=>[hv hw].
  have hPv:(p @` (T:set X)) v by rewrite hImage.
  have [x hx hpx]:=hPv.
  exists (@subspace_lift R X T x hx); split; first exact hpx.
  change (t (L x)=w).
  change (t (L (e v))=w) in hw.
  by rewrite -hpx (finite_inner_chart_right_inverse hChart) in hw.
- move=>[u [hu hw]]; split.
  + rewrite -hImage; exists (subspace_val u); last exact hu.
    exact:subspace_valP u.
  + change (t (L (e v))=w).
    by rewrite -hu (finite_inner_chart_right_inverse hChart).
Qed.
