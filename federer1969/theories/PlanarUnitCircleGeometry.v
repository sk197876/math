(** Federer 2.10.2(1), p. 171: geometry of the actual unit circle used
    to distinguish fixed-cutoff open and unrestricted approximations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerNormInequalities InnerMetric InnerNormedTopology ConstrainedUnitSphere
  EuclideanCoordinateMetric HausdorffMeasure HausdorffUnitSphereMass EuclideanBallVolume
  HausdorffIsometricEmbedding MetricDiameterUP MetricDiameter MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [planar_unit_circle]: Federer 2.10.2(1), p. 171;
    the actual radius-one Euclidean circle, before any covering claims. *)
Definition planar_unit_circle (R:realType):
    set (inner_metric_space (@euclidean_inner_productP R 2)):=
  [set x | inner_norm (@euclidean_inner_productP R 2) x = 1].

(** Source for [planar_unit_circle_nonempty]: Federer 2.10.2(1),
    p. 171; supporting nonempty original generator in the circle example. *)
Lemma planar_unit_circle_nonempty (R:realType):
  @planar_unit_circle R !=set0.
Proof.
exists (@coordinate_basis R 2 ord0); exact:euclidean_coordinate_unit_norm.
Qed.

(** Source for [planar_unit_circle_closed]: Federer 2.10.2(1),
    p. 171; supporting closedness, hence Borel measurability, of the circle. *)
Lemma planar_unit_circle_closed (R:realType):closed (@planar_unit_circle R).
Proof. exact:inner_unit_sphere_closed. Qed.

(** Source for [planar_unit_circle_length]: Federer 2.10.2(1),
    p. 171; supporting actual length supplied by the proved sphere formula
    of 3.2.13, p. 250. No circle length is an added hypothesis. *)
Lemma planar_unit_circle_length (R:realType):
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1
    (@planar_unit_circle R)=(2*euclidean_unit_ball_volume R 2)%:E.
Proof. exact:(@hausdorff_unit_sphere_mass R 2 (erefl true)). Qed.

(** Source for [inner_antipodal_hausdorff_invariance]: Federer 2.10.2(1),
    p. 171; supporting invariance under the actual antipodal isometry,
    derived from 2.10.11, p. 176. All natural degrees and sets are retained. *)
Lemma inner_antipodal_hausdorff_invariance (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:InnerProductUP.is_inner_product B) k
    (A:set (inner_metric_space hB)):
  @hausdorff_measure R (inner_metric_space hB) k ((fun x=> -x) @` A)=
    @hausdorff_measure R (inner_metric_space hB) k A.
Proof.
apply:(@hausdorff_isometric_embedding_invariance R
  (inner_metric_space hB) (inner_metric_space hB) (fun x=> -x) (fun x=> -x)).
- exact:opprK.
- move=>x y; rewrite !inner_metric_distanceE.
  have hEq: -x- -y= -(x-y) by rewrite opprB opprK addrC.
  by rewrite hEq inner_normN.
Qed.

(** Source for [open_planar_diameter_two_excludes_antipodes]: Federer
    2.10.2(1), p. 171, the obstruction in the fixed-cutoff circle example.
    Openness permits moving a unit point slightly outward; a set of
    diameter at most two therefore cannot contain its antipode too. *)
Theorem open_planar_diameter_two_excludes_antipodes (R:realType)
    (S:set (inner_metric_space (@euclidean_inner_productP R 2))) x:
  open S -> (extended_metric_diameter S<= (2:R)%:E)%E ->
  planar_unit_circle x -> S x -> ~S (-x).
Proof.
move=>hOpen hDiam hx hSx hSnx.
rewrite openE in hOpen.
have [eps he hBall]:=(metricType_numDomainType.nbhs_mdistP x S).1 (hOpen x hSx).
pose h:=eps/2.
have hh:0<h by rewrite /h divr_gt0 // ltr0n.
have h2:(0<2:>R) by rewrite ltr0n.
have hhe:h<eps.
  by rewrite /h (ltr_pdivrMr _ _ h2) -{1}[eps]mulr1 (ltr_pM2l he) ltr1n.
pose y:inner_metric_space (@euclidean_inner_productP R 2):=(1+h)*:x.
have hNear:mdist x y=h.
  rewrite inner_metric_distanceE.
  have hEq:x-y=(-h)*:x.
    rewrite /y -{1}(scale1r x) -scalerBl; congr (_*:x); ring.
  rewrite hEq inner_normZ normrN (ger0_norm (ltW hh)).
  by rewrite (hx : inner_norm (@euclidean_inner_productP R 2) x = 1) mulr1.
have hSy:S y.
  apply:(hBall y).
  change (mdist x y<eps).
  by rewrite hNear.
have hFar:mdist y (-x) = 2+h.
  rewrite inner_metric_distanceE.
  have hEq:y-(-x)=(2+h)*:x.
    rewrite /y opprK -{2}(scale1r x) -scalerDl; congr (_*:x); ring.
  rewrite hEq inner_normZ (ger0_norm (_:0<=2+h)); last by lra.
  by rewrite (hx : inner_norm (@euclidean_inner_productP R 2) x = 1) mulr1.
have hBound:=le_trans (metric_diameter_upper (extended_metric_diameter_specification S) hSy hSnx) hDiam.
rewrite hFar lee_fin in hBound.
have hStrict:(2:R)<2+h by rewrite ltrDl.
by have := lt_le_trans hStrict hBound; rewrite ltxx.
Qed.
