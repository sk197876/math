(** Federer (1969), 3.2.28, pp. 265–267:
    the computed intrinsic tangent exterior norm is
    unchanged in the actual isometric Euclidean charts
    used by the area and coarea theorems. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  InnerProductUP InnerNorm OrthogonalMaps FiniteInnerChartUP EuclideanLinearJacobian
  ExteriorGrading ExteriorMaps ExteriorMapScaling FiniteExteriorPowers ExteriorNorm ExteriorNormNaturality
  InnerExteriorPositivity ExteriorOperatorNorm OperatorNormUP OperatorNormTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_inner_chart_exterior_jacobian]:
    the Euclidean-coordinate interpretation of the tangent
    Jacobians calculated in Federer 3.2.28(2)–(4),
    pp. 265–267. The operator-norm value is
    transported through actual exterior isometries and
    the proved source inverse; no new norm is selected. *)
Theorem finite_inner_chart_exterior_jacobian (R:realType) (U V:lmodType R)
    (B:U->U->R) (C:V->V->R) (hB:is_inner_product B) (hC:is_inner_product C)
    d p (e:Hom (R_n R d) U) (r:Hom U (R_n R d))
    (t:Hom V (R_n R p)) (f:Hom U V) q j:
  is_finite_inner_chart B e r ->
  is_orthogonal_map C (@euclidean_inner_product R p) (hom_as_linear t) ->
  is_operator_norm (exterior_inner_productP (euclidean_two_nonzero R) hB q)
    (exterior_inner_productP (euclidean_two_nonzero R) hC q)
    (exterior_power_map (hom_as_linear f) q) j ->
  euclidean_linear_jacobian q (hom_comp t (hom_comp f e))=j.
Proof.
move=>hChart hT hF.
pose h2:=euclidean_two_nonzero R.
pose H:=hom_comp t (hom_comp f e).
have hE:is_orthogonal_map (@euclidean_inner_product R d) B (hom_as_linear e).
  exact:finite_inner_chart_product hChart.
have hLift x:exterior_norm h2 hB (exterior_power_map (hom_as_linear e) q x)=
    exterior_norm h2 (@euclidean_inner_productP R d) x.
  exact:(@exterior_norm_orthogonal_natural R h2 (R_n R d) U
    (@euclidean_inner_product R d) B (@euclidean_inner_productP R d) hB
    (hom_as_linear e) hE q x).
have hOnto z:exists x,exterior_power_map (hom_as_linear e) q x=z.
  exists (exterior_power_map (hom_as_linear r) q z).
  exact:(@exterior_power_mapK R U (R_n R d) (hom_as_linear r) (hom_as_linear e)
    (finite_inner_chart_right_inverse hChart) q z).
have hLinear:hom_as_linear H =1 linear_comp (hom_as_linear t)
    (linear_comp (hom_as_linear f) (hom_as_linear e)) by move=>x.
have hMap x:exterior_power_map (hom_as_linear H) q x=
    exterior_power_map (hom_as_linear t) q
      (exterior_power_map (hom_as_linear f) q (exterior_power_map (hom_as_linear e) q x)).
  rewrite (exterior_power_map_ext hLinear) -!exterior_power_map_composition; reflexivity.
have hValues x:exterior_norm h2 hC
    (exterior_power_map (hom_as_linear f) q (exterior_power_map (hom_as_linear e) q x))=
    exterior_norm h2 (@euclidean_inner_productP R p) (exterior_power_map (hom_as_linear H) q x).
  by rewrite hMap (@exterior_norm_orthogonal_natural R h2 V (R_n R p) C
    (@euclidean_inner_product R p) hC (@euclidean_inner_productP R p)
    (hom_as_linear t) hT).
exact:(@operator_norm_isometric_transport R
  (exterior_power (R_n R d) q) (exterior_power (R_n R p) q) (exterior_power U q) (exterior_power V q)
  _ _ _ _ (exterior_inner_productP h2 (@euclidean_inner_productP R d) q)
  (exterior_inner_productP h2 (@euclidean_inner_productP R p) q)
  (exterior_inner_productP h2 hB q) (exterior_inner_productP h2 hC q)
  (exterior_power_map (hom_as_linear H) q) (exterior_power_map (hom_as_linear f) q)
  (exterior_power_map (hom_as_linear e) q) hLift hOnto hValues
  (euclidean_linear_jacobian q H) j
  (@exterior_operator_normP R h2 (R_n R d) (R_n R p) _ _
    (@euclidean_inner_productP R d) (@euclidean_inner_productP R p) d
    (@coordinate_basis R d) (@coordinate_basisP R d) (hom_as_linear H) q) hF).
Qed.
