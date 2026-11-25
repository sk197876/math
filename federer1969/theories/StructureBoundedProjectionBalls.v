(** Federer (1969), 3.3.7, p. 294: local ball bounds
    for the actual original restricted projection measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureCone StructureProjectionKernel StructureApertureMassUP StructurePureConeMass
  RectifiableSetUP MeasureRestriction MeasurePushforward MetricClosedBalls
  EuclideanBallVolume EuclideanClosedBallVolume EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_bounded_projection_ball_mass]: first
    displayed projection bound in the proof of Federer 3.3.7, p. 294.
    Use a positive finite upper bound M for the original diameter,
    choose the actual aperture 4 rho/M, and apply 3.3.6. This also
    covers empty and zero-diameter sources without dividing by zero.
    Every ball remains centred at an actual original projected point. *)
Theorem structure_bounded_projection_ball_mass (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))-> \bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (sigma lam M:R):
  is_purely_measure_m_unrectifiable phi m A ->0<sigma<1 ->0<lam ->0<M ->
  (forall x y,A x ->A y ->mdist x y<=M) ->
  is_structure_aperture_mass_bound hmn phi A p sigma lam ->
  forall a,A a ->forall rho:R,0<rho ->rho<sigma*M/4 ->
    (measure_pushforward (euclidean_projection_linear p) (measure_restrict phi A)
      (metric_closed_ball (euclidean_projection_linear p a:inner_metric_space (@euclidean_inner_productP R m)) rho)<=
      (2*84^+m*lam)%:E*euclidean_lebesgue_measure m
        (metric_closed_ball (euclidean_projection_linear p a:inner_metric_space (@euclidean_inner_productP R m)) rho))%E.
Proof.
move=>hPure hSigma hLam hM hDiameter hAperture a ha rho hRho hSmall.
have [hSigma0 hSigma1]:=andP hSigma.
pose e:=rho/M.
have he0:0<e by rewrite /e divr_gt0.
have hWide:4*e<sigma.
  rewrite /e mulrA ltr_pdivrMr //; nra.
have he:0<e<1 by apply/andP; split; first exact:he0; nra.
have hWidePositive:0<4*e by nra.
have hFinite x:A x ->forall r:R,0<r ->(r%:E<= +oo)%E ->
    (phi (A `&` structure_cone (structure_projection_kernel hmn p) x r%:E (4*e))<=
      (lam*euclidean_unit_ball_volume R m*r^+m*(4*e)^+m)%:E)%E.
  move=>hx r hr _; exact:hAperture x hx r hr (4*e) hWidePositive (ltW hWide).
have hEstimate:=@structure_pure_cone_local_mass R n m hmn phi A p e lam rho +oo a
  hPure he (ltW hLam) hRho (leey _) hFinite.
have hRadius:rho/e=M.
  by rewrite /e invfM invrK mulrA mulfV ?gt_eqF // mul1r.
have hRegion:(A `&` metric_closed_ball a (rho/e) `&`
    ((euclidean_projection_linear p) @^-1`
      metric_closed_ball (euclidean_projection_linear p a:inner_metric_space (@euclidean_inner_productP R m)) rho))=
    (A `&` ((euclidean_projection_linear p) @^-1`
      metric_closed_ball (euclidean_projection_linear p a:inner_metric_space (@euclidean_inner_productP R m)) rho)).
  apply/seteqP; split; first by move=>x [[hx _] hProjected]; split.
  move=>x [hx hProjected]; split; last exact:hProjected.
  split; first exact:hx.
  rewrite hRadius; exact:hDiameter a x ha hx.
rewrite hRegion in hEstimate.
rewrite /measure_pushforward /measure_restrict
  (@euclidean_closed_ball_normalized_volume R m (euclidean_projection_linear p a) rho (ltW hRho))
  -EFinM !mulrA.
exact:hEstimate.
Qed.
