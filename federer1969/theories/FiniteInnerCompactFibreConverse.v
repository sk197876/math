(** Federer (1969), 3.2.47(3), p. 283: supporting
    compact-domain application of 3.2.22(2). Pass to actual
    orthonormal coordinates, take a true rectifiable Borel hull
    inside the original compact slicing domain, and extend the
    actual slicing map with its proved bound. Only containment
    in the hull is used; no null excess is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric FiniteInnerChartUP FiniteInnerChartCompact
  FiniteInnerRectifiableCoordinates FiniteInnerCartesianGeometry
  LipschitzUP LipschitzBasic MetricLipschitzComposition
  KirszbraunExtensionUP KirszbraunExtension RectifiableSetUP
  RectifiableBorelMeasureHull MeasureRectifiableSubset RectifiableFibreImageConverse
  HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureHull
  BorelRegularMeasureUP TopologicalBorel BorelFamilyBasic MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_inner_compact_fibre_converse]: the actual
    good-fibre method of the first conclusion of 3.2.47(3),
    p. 283, with all finite-dimensional coordinate, hull and
    extension obligations proved. S, Z, H and P are actual
    geometric data whose hypotheses are discharged in the sphere
    application, rather than assumed bundle or measure identities. *)
Theorem finite_inner_compact_fibre_converse (R:realType) (V U:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R U C) N K t r mu
    (e:Hom (R_n R N) V) (p:Hom V (R_n R N))
    (a:Hom (R_n R K) U) (q:Hom U (R_n R K))
    (S X0:set V) (Z:set U) (E:set (R_n R t))
    (H0:V->U) (P:V->R_n R t):
  is_finite_inner_chart B e p ->is_finite_inner_chart C a q ->
  @compact (inner_metric_space hB) S ->X0 `<=` S ->
  @compact (inner_metric_space hC) Z ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hB) (r+mu)) (r+mu)%N X0 ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hC) mu) mu Z ->
  0<@hausdorff_measure R (inner_metric_space hC) mu Z ->
  @is_metric_lipschitz R (inner_metric_space hB) (inner_metric_space hC) S H0 ->
  (forall x,S x ->Z (H0 x)) ->
  @is_metric_lipschitz R (inner_metric_space hB)
    (inner_metric_space (@euclidean_inner_productP R t)) setT P ->
  (forall z,Z z ->forall y,E y ->exists x,X0 x /\H0 x=z /\P x=y) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R t)) r) r E.
Proof.
move=>hSource hTarget hS hXS hZ hXRect hZRect hPositive hH hRange hP hCover.
pose VX:=inner_metric_space hB.
pose UY:=inner_metric_space hC.
pose A:=inner_metric_space (@euclidean_inner_productP R N).
pose D:=inner_metric_space (@euclidean_inner_productP R K).
pose T:=inner_metric_space (@euclidean_inner_productP R t).
pose SC:=p @` S.
pose XC:=p @` X0.
pose ZC:=q @` Z.
pose rho:=@hausdorff_measure R A (r+mu)%N.
pose beta:=@hausdorff_measure R D mu.
have hRho:=@hausdorff_measure_is_measure R A (r+mu)%N.
have hBeta:=@hausdorff_measure_is_measure R D mu.
have hSCompact:=@finite_inner_chart_compact R V B hB N e p S hSource hS.
have hZCompact:=@finite_inner_chart_compact R U C hC K a q Z hTarget hZ.
have hSCBorel:@borel_set A SC:=closed_borel_set (compact_closed (@metric_hausdorff R A) hSCompact).
have hZCBorel:@borel_set D ZC:=closed_borel_set (compact_closed (@metric_hausdorff R D) hZCompact).
have hXCoordinates:=@finite_inner_chart_measure_rectifiable_coordinates R V B hB N e p
  (r+mu)%N X0 hSource hXRect.
have [M [hMBorel [hHull hMRect]]]:=@rectifiable_borel_measure_hull R (r+mu)%N N XC hXCoordinates.
pose W:=M `&` SC.
have hWBorel:@borel_set A W:=borel_family_binary_intersection (borel_sets_family A) hMBorel hSCBorel.
have hWMeas:measure_measurable rho W.
  exact:(borel_regular_borel_measurable hRho (@hausdorff_measure_borel_regular R A (r+mu)%N) hWBorel).
have hWRect:is_measure_m_rectifiable rho (r+mu)%N W.
  exact (@measure_rectifiable_subset R A rho (r+mu)%N M W (fun x hx=>hx.1) hMRect).
have hXW:XC `<=` W.
  move=>x hx; split; first exact (@measure_hull_subset R A rho XC M hHull x hx).
  have [y hy <-]:=hx; exists y; first exact:hXS y hy.
  reflexivity.
have hZCoordinates:=@finite_inner_chart_measure_rectifiable_coordinates R U C hC K a q
  mu Z hTarget hZRect.
have hZMeas:measure_measurable beta ZC.
  exact:(borel_regular_borel_measurable hBeta (@hausdorff_measure_borel_regular R D mu) hZCBorel).
have hZPositive:0<beta ZC.
  rewrite /beta /ZC (@finite_inner_chart_inverse_hausdorff R U C hC K a q hTarget mu Z).
  exact hPositive.
pose F0:=fun x:A=>(q (H0 (e x)):D).
have [L [_ hHBound]]:=hH.
have hF0:@is_metric_lipschitz_bound R A D SC F0 L.
  split; first exact hHBound.1.
  move=>x y hx hy.
  have hxS:S (e x).
    have [z hz <-]:=hx; by rewrite (finite_inner_chart_right_inverse hSource).
  have hyS:S (e y).
    have [z hz <-]:=hy; by rewrite (finite_inner_chart_right_inverse hSource).
  have hEstimate:=hHBound.2 (e x) (e y) hxS hyS.
  have hSourceDistance:mdist (e x:VX) (e y)=mdist x y.
    rewrite !inner_metric_distanceE.
    change (inner_norm hB (e x-e y)=inner_norm (@euclidean_inner_productP R N) (x-y)).
    by rewrite -linearB (finite_inner_chart_norm hB hSource).
  have hTargetDistance:mdist (F0 x) (F0 y)=mdist (H0 (e x):UY) (H0 (e y)).
    rewrite !inner_metric_distanceE /F0.
    change (inner_norm (@euclidean_inner_productP R K) (q (H0 (e x))-q (H0 (e y)))=
      inner_norm hC (H0 (e x)-H0 (e y))).
    by rewrite -linearB (finite_inner_chart_inverse_norm hC hTarget).
  by rewrite hTargetDistance -hSourceDistance.
pose F:=@euclidean_lipschitz_extension R N K SC F0 L hF0.
have hExtension:=@euclidean_lipschitz_extension_specification R N K SC F0 L hF0.
have hF:is_metric_lipschitz setT F:=metric_lipschitz_of_bound (kirszbraun_extension_bound_law hExtension).
have hFRange x (hx:W x):ZC (F x).
  have hAgreement:F x=F0 x.
    exact (@kirszbraun_extension_agreement_law R N K SC F0 F L hExtension x hx.2).
  rewrite hAgreement.
  have hxS:S (e x).
    have [z hz hzx]:=hx.2; by rewrite -hzx (finite_inner_chart_right_inverse hSource).
  exists (H0 (e x)); first exact:hRange _ hxS.
  reflexivity.
pose P0:=fun x:A=>(P (e x):T).
have hP0:is_metric_lipschitz setT P0.
  exact:(metric_lipschitz_whole_composite
    (@finite_inner_chart_direct_lipschitz R V B hB N e p setT hSource) hP).
apply:(@rectifiable_fibre_image_converse R r mu N K t W ZC E F P0
  hWRect hWMeas hZCoordinates hZMeas hZPositive hF hFRange hP0).
move=>z [u hu hqu] y hy.
have [x [hx [hHx hPx]]]:=hCover u hu y hy.
exists (p x).
- split.
  + apply:hXW; by exists x.
  + have hxSC:SC (p x).
      exists x; first exact:hXS x hx.
      reflexivity.
    have hAgreement:F (p x)=F0 (p x).
      exact (@kirszbraun_extension_agreement_law R N K SC F0 F L hExtension (p x) hxSC).
    change (F (p x)=z); rewrite hAgreement.
    change (q (H0 (e (p x)))=z).
    by rewrite (finite_inner_chart_right_inverse hSource) hHx hqu.
- change (P (e (p x))=y).
  by rewrite (finite_inner_chart_right_inverse hSource) hPx.
Qed.
