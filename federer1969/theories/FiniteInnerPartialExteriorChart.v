(** Federer (1969), 3.2.28, pp. 265–267:
    transfer the actual tangent exterior norm to the
    partial Euclidean graph used by the intrinsic
    approximate Jacobian, with no off-tangent values. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerProductUP OrthogonalMaps LinearBasis FiniteInnerChartUP FiniteInnerChart
  ExteriorMaps InnerExteriorPositivity OperatorNormUP PartialFunctionUP PartialExteriorNormUP
  PartialExteriorIsometricChart FiniteInnerExteriorJacobianChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [finite_inner_partial_exterior_chart]: the
    actual intrinsic partial-graph norm in the area/coarea
    use of Federer 3.2.28, pp. 265–267.
    Both ambient identifications are actual isometries.
    A local source chart proves the equality; the
    specification keeps exactly the original tangent graph. *)
Theorem finite_inner_partial_exterior_chart (R:realType) (U V:lmodType R)
    (B:U->U->R) (C:V->V->R) (hB:is_inner_product B) (hC:is_inner_product C)
    d (b:'I_d->U) (hb:is_basis b) n k q
    (A:Hom U (R_n R n)) (t:Hom V (R_n R k)) (f:Hom U V)
    (g:partial_function (R_n R n) (R_n R k)) j:
  is_orthogonal_map B (@euclidean_inner_product R n) (hom_as_linear A) ->
  is_orthogonal_map C (@euclidean_inner_product R k) (hom_as_linear t) ->
  (forall v w,partial_function_graph g v w <->exists u,A u=v /\t (f u)=w) ->
  is_operator_norm (exterior_inner_productP (euclidean_two_nonzero R) hB q)
    (exterior_inner_productP (euclidean_two_nonzero R) hC q)
    (exterior_power_map (hom_as_linear f) q) j ->
  is_partial_exterior_norm q g j.
Proof.
move=>hA hT hGraph hNorm.
have [e [p hChart]]:=finite_inner_chart_exists hB hb.
pose D:=hom_comp A e.
pose H:=hom_comp t (hom_comp f e).
have hD:is_orthogonal_map (@euclidean_inner_product R d) (@euclidean_inner_product R n)
    (hom_as_linear D).
  move=>x y; change (euclidean_inner_product (A (e x)) (A (e y))=euclidean_inner_product x y).
  rewrite hA; exact:finite_inner_chart_product hChart x y.
have hCoords v w:partial_function_graph g v w <->exists z,D z=v /\H z=w.
  split.
  - move=>h; have [u [hu hw]]:=(hGraph v w).1 h.
    exists (p u); split.
    + change (A (e (p u))=v); by rewrite (finite_inner_chart_right_inverse hChart).
    + change (t (f (e (p u)))=w); by rewrite (finite_inner_chart_right_inverse hChart).
  - move=>[z [hz hw]]; apply:(hGraph v w).2.
    exists (e z); by split.
have hPartial:=@partial_exterior_isometric_chart_norm R d n k q D H g hD hCoords.
have hValue:=@finite_inner_chart_exterior_jacobian R U V B C hB hC d k e p t f q j
  hChart hT hNorm.
by rewrite hValue in hPartial.
Qed.
