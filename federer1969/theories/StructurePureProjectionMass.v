(** Federer (1969), 3.3.7, p. 294: exact
    original projection mass comparison, including unbounded sources. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureConeUP StructureCone StructureProjectionKernel StructureApertureMassUP
  StructureProjectionRegularisation StructureEuclideanMassComparison
  RectifiableSetUP PureUnrectifiableLaws MetricClosedBalls NullFibresProperSource
  EuclideanLebesgueDimensions MeasureUP MeasureBasic MeasureRestriction MeasureContinuityBelow
  ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_bounded_pure_projection_mass]: the bounded
    source case in Federer 3.3.7, p. 294. The actual Borel
    regularisation, its class-M premises, original-image mass identity
    and exact local Lebesgue comparison are all proved, rather than
    given as additional hypotheses. Empty and zero-diameter sources
    and all natural admissible dimensions remain. *)
Theorem structure_bounded_pure_projection_mass (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))-> \bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (sigma lam L:R):
  is_structure_measure phi ->is_purely_measure_m_unrectifiable phi m A ->
  0<sigma<1 ->0<lam ->0<=L ->
  A `<=` metric_closed_ball (0:inner_metric_space (@euclidean_inner_productP R n)) L ->
  is_structure_aperture_mass_bound hmn phi A p sigma lam ->
  (phi A<=(2*84^+m*lam)%:E*euclidean_lebesgue_measure m (euclidean_projection_linear p @` A))%E.
Proof.
move=>hStructure hPure hSigma hLam hL hSource hAperture.
have [psi [hRegularisation [hClass [hRadon [hImageMass [delta [hDelta hLocal]]]]]]]:=
  @structure_bounded_projection_regularisation R n m hmn phi A p sigma lam L
    hStructure hPure hSigma hLam hL hSource hAperture.
have hTwo:(0:R)<2 by rewrite ltr0n.
have hPower:0<(84:R)^+m by apply:exprn_gt0; rewrite ltr0n.
have hCoefficient:0<2*84^+m*lam:=mulr_gt0 (mulr_gt0 hTwo hPower) hLam.
rewrite hImageMass.
apply:(@structure_euclidean_local_mass_comparison R m psi
  (euclidean_projection_linear p @` A) (2*84^+m*lam) hClass hCoefficient)=>z hz.
exists delta; split; first exact:hDelta.
exact:hLocal z hz.
Qed.

(** Source for [federer_3_3_7]: COMPLETE Federer 3.3.7,
    p. 294. The outer mass of ORIGINAL arbitrary purely
    unrectifiable A is at most 2 times 84 to power m times lambda
    times the actual Lebesgue outer measure of ORIGINAL p(A).
    The source may be unbounded or nonmeasurable; all natural
    0<=m<=n and infinite masses remain. Closed-ball exhaustion is
    applied to the ORIGINAL restriction phi to A, whose needed
    measurable sets follow from the standing closed-set condition.
    No overlapping projected image costs are summed. *)
Theorem federer_3_3_7 (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))-> \bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (sigma lam:R):
  is_structure_measure phi ->is_purely_measure_m_unrectifiable phi m A ->
  0<sigma<1 ->0<lam ->is_structure_aperture_mass_bound hmn phi A p sigma lam ->
  (phi A<=(2*84^+m*lam)%:E*euclidean_lebesgue_measure m (euclidean_projection_linear p @` A))%E.
Proof.
move=>hStructure hPure hSigma hLam hAperture.
pose F j:=metric_closed_ball (0:inner_metric_space (@euclidean_inner_productP R n)) (j%:R:R).
pose E j:=A `&` F j.
pose mu:=measure_restrict phi A.
have hMu:is_measure mu:=measure_restrict_is_measure hStructure.1 A.
have hMeas j:measure_measurable mu (F j).
  apply:(measure_restrict_measurable A).
  apply:hStructure.2; exact:metric_closed_ball_closed.
have hIncreasing i j:(i<=j)%N ->F i `<=` F j.
  move=>hij x hx; apply:le_trans hx _; by rewrite ler_nat.
have hUnion:(\bigcup_j F j)=setT.
  apply/seteqP; split; first by move=>x _.
  exact:(@metric_natural_closed_balls_cover R
    (inner_metric_space (@euclidean_inner_productP R n)) 0).
have hLimit:=@measure_continuity_below R _ mu hMu F hMeas hIncreasing.
rewrite hUnion /mu /measure_restrict setIT in hLimit.
apply:(extended_order_limit_upper_bound hLimit.2)=>j.
have hEA:E j `<=` A by move=>x [hx _].
have hPureE:=pure_unrectifiable_subset hEA hPure.
have hSource:E j `<=` F j by move=>x [_ hx].
have hApertureE:is_structure_aperture_mass_bound hmn phi (E j) p sigma lam.
  move=>x hx r hr s hs hsSigma.
  have hSub:(E j `&` structure_cone (structure_projection_kernel hmn p) x r%:E s) `<=`
      (A `&` structure_cone (structure_projection_kernel hmn p) x r%:E s).
    move=>y [hy hCone]; split; [exact:hEA y hy|exact:hCone].
  exact:le_trans (@measure_mono R _ phi hStructure.1 _ _ hSub)
    (hAperture x (hEA x hx) r hr s hs hsSigma).
have hJ:(0:R)<=j%:R by rewrite ler0n.
have hBound:=@structure_bounded_pure_projection_mass R n m hmn phi (E j) p sigma lam j%:R
  hStructure hPureE hSigma hLam hJ hSource hApertureE.
have hImage:(euclidean_projection_linear p @` E j) `<=` (euclidean_projection_linear p @` A).
  move=>z [x hx <-]; exists x; first exact:hEA x hx; reflexivity.
have hImageBound:=@measure_mono R _ (@euclidean_lebesgue_measure R m)
  (euclidean_lebesgue_is_measure R m) _ _ hImage.
have hTwo:(0:R)<=2 by rewrite ler0n.
have hPower:0<=(84:R)^+m by apply:exprn_ge0; rewrite ler0n.
have hCoefficient:0<=2*84^+m*lam:=mulr_ge0 (mulr_ge0 hTwo hPower) (ltW hLam).
have hProduct:=@lee_wpmul2l R (2*84^+m*lam)%:E (lee_tofin hCoefficient) _ _ hImageBound.
exact:le_trans hBound hProduct.
Qed.
