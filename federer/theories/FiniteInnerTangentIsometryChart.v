(** Federer (1969), 3.2.28(4), pp. 266–267:
    actual tangent isometries in orthonormal ambient
    coordinates, as used by the area formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm HilbertFormCompactness
  OrthogonalMaps NormDifferentialUP NormLinearIsometryInverse NormLinearIsomorphismTangent TangentConeUP
  FiniteInnerChartUP FiniteInnerDifferentialChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_tangent_isometry_chart]:
    coordinate invariance of the tangent isometry DT,
    Federer 3.2.28(4), p. 266, by the
    linear tangent-transport law of 3.1.21, p. 234.
    The actual full differential and actual tangent
    inner products are retained in both presentations. *)
Theorem finite_inner_tangent_isometry_chart (R:realType) (V U:lmodType R)
    (B:V->V->R) (C:U->U->R) (hB:is_inner_product B) (hC:is_inner_product C) n p
    (e:Hom (R_n R n) V) (q:Hom V (R_n R n)) (t:Hom U (R_n R p))
    (S:set V) (F:V->U) a (D:Hom V U):
  is_finite_inner_chart B e q ->
  is_orthogonal_map C (@euclidean_inner_product R p) (hom_as_linear t) ->
  has_norm_differential (inner_norm hB) (inner_norm hC) (fun _=>True) F a D ->
  (forall x y,norm_tangent_cone (inner_norm hB) S a x ->
    norm_tangent_cone (inner_norm hB) S a y ->C (D x) (D y)=B x y) ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R p)) (fun _=>True)
    (fun z=>t (F (e z))) (q a) (hom_comp t (hom_comp D e)) /\
  forall x y,norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) (q @` S) (q a) x ->
    norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) (q @` S) (q a) y ->
    euclidean_inner_product (hom_comp t (hom_comp D e) x) (hom_comp t (hom_comp D e) y)=
      euclidean_inner_product x y.
Proof.
move=>hChart hT hD hPair; split.
- exact:(@finite_inner_differential_chart R V U B C hB hC n p e q t F a D hChart hT hD).
- have hQ:norm_bounded_linear (inner_norm hB) (inner_norm (@euclidean_inner_productP R n)) q.
    apply:norm_linear_isometry_bounded=>x; exact:(@finite_inner_chart_inverse_norm R V B hB n e q hChart x).
  have hE:norm_bounded_linear (inner_norm (@euclidean_inner_productP R n)) (inner_norm hB) e.
    apply:norm_linear_isometry_bounded=>x; exact:(@finite_inner_chart_norm R V B hB n e q hChart x).
  have hTan:=@norm_linear_isomorphism_tangent_image R V (R_n R n)
    (inner_norm hB) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm hB) (inner_norm_real_norm (@euclidean_inner_productP R n))
    q e S a hQ hE (finite_inner_chart_right_inverse hChart) (finite_inner_chart_left_inverse hChart).
  move=>x y hx hy.
  have [u hu hux]:(q @` (norm_tangent_cone (inner_norm hB) S a)) x by rewrite hTan.
  have [v hv hvy]:(q @` (norm_tangent_cone (inner_norm hB) S a)) y by rewrite hTan.
  rewrite -hux -hvy.
  change (euclidean_inner_product (t (D (e (q u)))) (t (D (e (q v))))=
    euclidean_inner_product (q u) (q v)).
  rewrite !(finite_inner_chart_right_inverse hChart) hT (hPair u v hu hv).
  symmetry; exact:(@finite_inner_chart_inverse_product R V B n e q hChart u v).
Qed.
