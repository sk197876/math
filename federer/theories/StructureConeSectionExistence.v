(** Federer (1969), 3.3.5, p. 292: prove existence of the
    original global Lipschitz projection section from cone avoidance. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanProjectionSpace EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanRightBlockProjection OrthogonalMaps OrthogonalProjectionChartUP
  OrthogonalProjectionChart OrthogonalProjectionChartLaws
  StructureGraphSectionUP StructureConeAvoidance StructureNormalGraphBounds StructureSharpGraphBound
  MetricBiLipschitzInverse MetricDiameter LipschitzUP
  KirszbraunExtensionUP KirszbraunExtension SignedSquareRootSealed SignedSquareRootLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_cone_avoiding_section_exists_blocks]: the
    first conclusion of Federer 3.3.5, p. 292, with ambient dimension
    k+m. The actual inverse restriction and normal-coordinate bound are
    derived from original cone avoidance. Extend only its transverse
    coordinates by 2.10.43, then restore the base coordinates unchanged.
    Independent projection-chart and section laws control the result;
    every auxiliary chart and inverse stays local to the existence proof. *)
Theorem structure_cone_avoiding_section_exists_blocks (R:realType) k m (hmn:(m<=k+m)%N)
    (E S:set (inner_metric_space (@euclidean_inner_productP R (k+m))))
    (p:euclidean_projection_space R (k+m) m) (r: \bar R) (s:R):
  0<s<1 ->is_structure_cone_avoiding hmn E p r s ->S `<=` E ->
  (extended_metric_diameter S<r)%E ->
  exists f,is_structure_projection_section S p s f.
Proof.
move=>hs hAvoid hSE hDiameter.
pose X:=inner_metric_space (@euclidean_inner_productP R (k+m)).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose Z:=inner_metric_space (@euclidean_inner_productP R k).
pose F:=(@orthogonal_projection_chart R k m (euclidean_projection_linear p)
  (euclidean_projection_linear_member p)).1.
pose G:=(@orthogonal_projection_chart R k m (euclidean_projection_linear p)
  (euclidean_projection_linear_member p)).2.
have hChart:=@orthogonal_projection_chart_specification R k m
  (euclidean_projection_linear p) (euclidean_projection_linear_member p).
have hBi:=@structure_cone_avoidance_bilipschitz R (k+m) m hmn E S p r s hs hAvoid hSE hDiameter.
have [invP [hInvP hInvBound]]:=@metric_bilipschitz_inverse_exists R X Y S
  (euclidean_projection_linear p) s^-1 (0:X) hBi.
pose c:=s^-1^+2-1.
have hInvPositive:0<s^-1 by rewrite invr_gt0; exact:(andP hs).1.
have hIdentity:s*s^-1= 1 by rewrite mulfV // gt_eqF //; exact:(andP hs).1.
have hsPositive:0<s:=(andP hs).1.
have hsSmall:s<1:=(andP hs).2.
have hInvOne:1<s^-1 by nra.
have hc:0<=c by rewrite /c; nra.
pose C:=@SignedSquareRoot.value R c.
have hC:0<=C:=(signed_root_sign_bounds c).1 hc.
have hSquare:C^+2=c by rewrite /C signed_root_square (ger0_norm hc).
pose g0:=fun y:Y=>(@euclidean_first_block R k m (F (invP y)):Z).
have hG0:@is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R k))
    (euclidean_projection_linear p @` S) g0 C.
  split=>// y z [x hx <-] [t ht <-].
  rewrite /g0 (hInvP x hx) (hInvP t ht).
  exact:(@structure_transverse_inverse_distance R k m hmn E S p F G r s C
    hChart hs hC hSquare hAvoid hSE hDiameter x t hx ht).
pose g:=@euclidean_lipschitz_extension R m k (euclidean_projection_linear p @` S) g0 C hG0.
have hG:=@euclidean_lipschitz_extension_specification R m k
  (euclidean_projection_linear p @` S) g0 C hG0.
pose f:=fun y:Y=>(G (@euclidean_block_join R k m (g y,y)):X).
exists f; split.
- have hL:0<=s^-1:=ltW hInvPositive.
  have hGraph:=@structure_orthogonal_graph_sharp_lipschitz R m k g C s^-1
    (kirszbraun_extension_bound_law hG) hL (ltac:(by rewrite hSquare /c subrK)).
  split=>// x y _ _; rewrite /f inner_metric_distanceE -linearB.
  rewrite (orthogonal_map_norm (@euclidean_inner_productP R (k+m))
    (@euclidean_inner_productP R (k+m)) (projection_chart_backward_orthogonal hChart)).
  have h:=hGraph.2 x y I I; by rewrite inner_metric_distanceE in h.
- split.
  + move=>y; exact:projection_chart_fibre_coordinate hChart (g y) y.
  + move=>x hx; exists (euclidean_projection_linear p x)=>//.
    rewrite /f (@kirszbraun_extension_agreement_law R m k
      (euclidean_projection_linear p @` S) g0 g C hG _ (ex_intro2 _ _ x hx erefl)).
    rewrite /g0 (hInvP x hx) -(projection_chart_coordinate_law hChart).
    change (G (@euclidean_block_join R k m (@euclidean_block_split R k m (F x)))=x).
    by rewrite euclidean_block_splitK (projection_chart_forward_inverse_law hChart).
Qed.
