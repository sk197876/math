(** Federer (1969), 3.3.6, pp. 293–294: exact local
    mass estimate for the original purely unrectifiable source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureCone StructureProjectionKernel StructureConeHeight StructureTwoConeCover
  StructureConeFreeRemainder StructureProjectedConePacking StructureConeMassArithmetic
  RectifiableSetUP PureUnrectifiableLaws MeasureUP MeasureBasic MeasureSplit MeasureIndexedCover
  MetricClosedBalls EuclideanBallVolume NonnegativeSum NonnegativeSumScale NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_pure_cone_local_mass]: the first conclusion
    of Federer 3.3.6, pp. 293–294, in its local proof coordinates
    e=s/4. The original source is arbitrary; the exact constant
    2 times 84 to power m and the actual projected cylinder remain.
    Only finite positive radii used in the proof are required in the
    supporting hypothesis; the full printed theorem supplies them. *)
Theorem structure_pure_cone_local_mass (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))-> \bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (e lam rho:R) (xi: \bar R)
    (a:inner_metric_space (@euclidean_inner_productP R n)):
  is_purely_measure_m_unrectifiable phi m A ->0<e<1 ->0<=lam ->0<rho ->
  ((6*rho/e)%:E<=xi)%E ->
  (forall x,A x ->forall r:R,0<r ->(r%:E<=xi)%E ->
    (phi (A `&` structure_cone (structure_projection_kernel hmn p) x r%:E (4*e))<=
      (lam*euclidean_unit_ball_volume R m*r^+m*(4*e)^+m)%:E)%E) ->
  (phi (A `&` metric_closed_ball a (rho/e) `&`
      ((euclidean_projection_linear p) @^-1`
        metric_closed_ball (euclidean_projection_linear p a:inner_metric_space (@euclidean_inner_productP R m)) rho))<=
    (2*84^+m*lam*euclidean_unit_ball_volume R m*rho^+m)%:E)%E.
Proof.
move=>hPure he hLam hRho hScale hMass.
have [he0 he1]:=andP he.
have [hm _]:=(@pure_unrectifiable_iff_rectifiable_subsets_null R _ phi m A).1 hPure.
pose B:=A `&` metric_closed_ball a (rho/e) `&`
  ((euclidean_projection_linear p) @^-1`
    metric_closed_ball (euclidean_projection_linear p a:inner_metric_space (@euclidean_inner_productP R m)) rho).
pose C:=structure_active_cone_points hmn B p e.
have hBA:B `<=` A by move=>x [[hx _] _].
have hDiameter x y:B x ->B y ->mdist x y<= 2*rho/e.
  move=>[[hx hNearX] _] [[hy hNearY] _].
  have hBound:=metric_closed_ball_diameter_bound hNearX hNearY.
  change (is_true (mdist x y<= 2*rho/e)); lra.
have hProjection x:B x ->mdist
    (euclidean_projection_linear p a:inner_metric_space (@euclidean_inner_productP R m))
    (euclidean_projection_linear p x)<=rho by move=>[_ hx]; exact:hx.
have [h [D [hHeight [hDC [hCount [hCover hPacking]]]]]]:=
  @structure_projected_cone_packing R n m hmn B p e rho a he0 hRho hDiameter hProjection.
have hSlices i:D i ->
    (phi (C `&` [set z |(mdist
      (euclidean_projection_linear p i:inner_metric_space (@euclidean_inner_productP R m))
      (euclidean_projection_linear p z)<=e*h i)%R])<=
      ((2*12^+m*lam)*(euclidean_unit_ball_volume R m*(e*h i)^+m))%:E)%E.
  move=>hi; have hCi:=hDC i hi.
  have hHi: is_structure_cone_height hmn B p e i (h i):=(hHeight i hCi).1.
  have hPositive:=structure_cone_height_positive hHi.
  have [y [hy hFar]]:=structure_cone_height_near_maximizer hHi.
  have hR:0<3*h i by nra.
  have hCutoff:((3*h i)%:E<=xi)%E.
    apply:le_trans _ hScale; rewrite lee_fin.
    have hH:h i<= 2*rho/e:=(hHeight i hCi).2.
    lra.
  have hFirst:=hMass i (hBA i hCi.1) (3*h i) hR hCutoff.
  have hSecond:=hMass y (hBA y hy.1) (3*h i) hR hCutoff.
  have hGeometry:=structure_height_two_cone_cover he0 hHi hy hFar.
  have hSourceCover:(C `&` [set z |(mdist
      (euclidean_projection_linear p i:inner_metric_space (@euclidean_inner_productP R m))
      (euclidean_projection_linear p z)<=e*h i)%R]) `<=`
      (A `&` structure_cone (structure_projection_kernel hmn p) i (3*h i)%:E (4*e)) `|`
      (A `&` structure_cone (structure_projection_kernel hmn p) y (3*h i)%:E (4*e)).
    move=>z [hCz hProjected].
    have hBz:B z:=hCz.1.
    have hCases:=hGeometry z (conj hBz hProjected).
    case:hCases=>hCone; [left|right]; split; try exact:hCone; exact:hBA z hBz.
  have hBound:=measure_binary_cover hm hSourceCover.
  apply:le_trans hBound _.
  have hPair:=leeD hFirst hSecond.
  by rewrite -EFinD structure_two_cone_coefficient in hPair.
have hIndexedCover:C `<=` \bigcup_(i in D) (C `&` [set z |(mdist
    (euclidean_projection_linear p i:inner_metric_space (@euclidean_inner_productP R m))
    (euclidean_projection_linear p z)<=e*h i)%R]).
  move=>z hz; have [i [hi hNear]]:=hCover z hz.
  exists i; first exact:hi.
  by split.
have hCovered:=@measure_indexed_cover R _ _ phi hm C D _ hCount hIndexedCover.
have hPointwise:(nonnegative_sum D (fun i=>phi (C `&` [set z |(mdist
    (euclidean_projection_linear p i:inner_metric_space (@euclidean_inner_productP R m))
    (euclidean_projection_linear p z)<=e*h i)%R]))<=
    nonnegative_sum D (fun i=>((2*12^+m*lam)*(euclidean_unit_ball_volume R m*(e*h i)^+m))%:E))%E.
  apply:nonnegative_sum_mono; exact:hSlices.
have hTwelve:0<=(12:R)^+m by apply:exprn_ge0; rewrite ler0n.
have hTwo:(0:R)<= 2 by rewrite ler0n.
have hCoefficient:0<= 2*12^+m*lam:=mulr_ge0 (mulr_ge0 hTwo hTwelve) hLam.
have hTerms i:D i ->(0<=(euclidean_unit_ball_volume R m*(e*h i)^+m)%:E)%E.
  move=>hi; rewrite lee_fin; apply:mulr_ge0; first exact:ltW (euclidean_unit_ball_volumeE R m).2.
  apply:exprn_ge0; exact:mulr_ge0 (ltW he0) (ltW (structure_cone_height_positive (hHeight i (hDC i hi)).1)).
have hFactored:nonnegative_sum D (fun i=>((2*12^+m*lam)*(euclidean_unit_ball_volume R m*(e*h i)^+m))%:E)=
    ((2*12^+m*lam)%:E*nonnegative_sum D (fun i=>(euclidean_unit_ball_volume R m*(e*h i)^+m)%:E))%E.
  rewrite -(@nonnegative_sum_scale R _ D _ (2*12^+m*lam) hCoefficient hTerms).
  apply:nonnegative_sum_ext=>i hi; exact:EFinM.
rewrite hFactored in hPointwise.
have hProduct:=@lee_wpmul2l R (2*12^+m*lam)%:E (lee_tofin hCoefficient) _ _ hPacking.
rewrite -EFinM structure_packing_coefficient in hProduct.
have hTotal:=le_trans hCovered (le_trans hPointwise hProduct).
have hEqual:=@structure_active_cone_mass R n m hmn phi A B p e hPure hBA he.
change (is_true (phi B<=(2*84^+m*lam*euclidean_unit_ball_volume R m*rho^+m)%:E)%E).
by rewrite hEqual; exact:hTotal.
Qed.
