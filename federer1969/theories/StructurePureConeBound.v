(** Federer (1969), 3.3.6, pp. 293–294: complete
    original cylinder mass and upper-density conclusions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureConeUP StructureCone StructureProjectionKernel StructureConeMassUP
  StructurePositiveConeCutoff StructurePureConeMass StructurePureConeDensity
  RectifiableSetUP MeasureRestriction MetricClosedBalls EuclideanBallVolume MetricDensities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_uniform_cone_finite_radius]: the actual
    finite-radius instances of the original hypothesis in Federer
    3.3.6, p. 293. Infinite cutoff remains; only the displayed finite
    scalar factors are regrouped. *)
Lemma structure_uniform_cone_finite_radius (R:realType) n m (hmn:(m<=n)%N)
    phi A (p:euclidean_projection_space R n m) s lam xi:
  is_structure_uniform_cone_mass_bound hmn phi A p s lam xi ->
  forall x,A x ->forall r:R,0<r ->(r%:E<=xi)%E ->
    (phi (A `&` structure_cone (structure_projection_kernel hmn p) x r%:E s)<=
      (lam*euclidean_unit_ball_volume R m*r^+m*s^+m)%:E)%E.
Proof.
move=>hBound x hx r hr hCutoff.
have hR:(0<r%:E)%E by rewrite lte_fin.
have h:=hBound x hx r%:E hR hCutoff.
by rewrite -EFin_expe -!EFinM in h.
Qed.

(** Source for [federer_3_3_6]: COMPLETE Federer 3.3.6, pp. 293–294.
    For every original centre and every printed admissible positive rho,
    the actual original cylinder has outer mass at most
    2 times 84 to power m times lambda alpha(m) rho to power m;
    the original restricted upper m density is at most 2 times 84 to
    power m times lambda. The original finite-positive-radius cone hypothesis and the
    standing closed-measurable measure remain. All natural dimensions,
    arbitrary original A and infinite radial cutoffs are retained.
    No estimate at radius infinity is an additional premise. *)
Theorem federer_3_3_6 (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))-> \bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (s lam:R) (xi: \bar R):
  is_structure_measure phi ->is_purely_measure_m_unrectifiable phi m A ->
  0<s<1 ->0<lam ->(0<xi)%E ->
  (forall x,A x ->forall r:R,0<r ->(r%:E<=xi)%E ->
    (phi (A `&` structure_cone (structure_projection_kernel hmn p) x r%:E s)<=
      (lam*euclidean_unit_ball_volume R m*r^+m*s^+m)%:E)%E) ->
  forall a:inner_metric_space (@euclidean_inner_productP R n),
    (forall rho:R,0<rho ->(rho%:E<=s%:E*xi/(24:R)%:E)%E ->
      (phi (A `&` metric_closed_ball a (4*rho/s) `&`
        ((euclidean_projection_linear p) @^-1`
          metric_closed_ball (euclidean_projection_linear p a:inner_metric_space (@euclidean_inner_productP R m)) rho))<=
        (2*84^+m*lam*euclidean_unit_ball_volume R m*rho^+m)%:E)%E) /\
    (upper_metric_density m (measure_restrict phi A) a<=(2*84^+m*lam)%:E)%E.
Proof.
move=>hStructure hPure hs hLam hXi hBound a.
have [hs0 hs1]:=andP hs.
pose e:=s/4.
have he:0<e<1 by apply/andP; split; rewrite /e; lra.
have hFour:4*e=s by rewrite /e; lra.
have hFinite x:A x ->forall r:R,0<r ->(r%:E<=xi)%E ->
    (phi (A `&` structure_cone (structure_projection_kernel hmn p) x r%:E (4*e))<=
      (lam*euclidean_unit_ball_volume R m*r^+m*(4*e)^+m)%:E)%E.
  rewrite hFour; exact:(hBound x).
split.
- move=>rho hRho hRhoCutoff.
  have hCutoff:=structure_positive_cone_cutoff hs0 hXi hRhoCutoff.
  have hResult:=@structure_pure_cone_local_mass R n m hmn phi A p e lam rho xi a
    hPure he (ltW hLam) hRho hCutoff hFinite.
  have hRadius:rho/e= 4*rho/s by rewrite /e invfM invrK; ring.
  by rewrite hRadius in hResult.
- exact:(@structure_pure_cone_upper_density R n m hmn phi A p e lam xi a
    hPure he (ltW hLam) hXi hFinite).
Qed.
