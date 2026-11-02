(** Federer (1969), 3.2.38, p. 275: the first displayed
    estimate omits the j=0 term of 3.2.35. A constant affine
    map on the actual unit line cube disproves that intermediate
    bound. The statement of 3.2.38 does not need modification. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm
  HilbertFormCompactness NormDifferentialUP NormDifferentialLinear LipschitzUP
  CoordinateEdgeBoxGeometry EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  MinkowskiContents LineSingletonMinkowskiTube IntegralGeometricGauge ConvexIntrinsicSingleton.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_missing_steiner_constant_example]: independent
    actual-source and map laws for the proof-display counterexample
    in Federer 3.2.38, p. 275. In m=n= 1 the printed j= 1 term
    has weight one; its actual intrinsic coefficient is zero. *)
Record is_missing_steiner_constant_example (R:realType) (r:R)
    (K:set (inner_metric_space (@euclidean_inner_productP R 1)))
    (g:inner_metric_space (@euclidean_inner_productP R 1)->
      inner_metric_space (@euclidean_inner_productP R 1)):Prop:={
  (** Source for [missing_constant_source]: actual unit coordinate
      cube in the good-cube estimate, Federer 3.2.38, p. 275. *)
  missing_constant_source:K=coordinate_edge_box (fun _:'I_1=>(1:R));
  (** Source for [missing_constant_compact]: the actual compact
      source cube, Federer 3.2.38, pp. 274--275. *)
  missing_constant_compact:compact K;
  (** Source for [missing_constant_source_mass]: the cube has
      actual positive unit length, Federer 3.2.38, p. 275. *)
  missing_constant_source_mass:@euclidean_lebesgue_measure R 1 K= 1%E;
  (** Source for [missing_constant_lipschitz]: an actual global
      Lipschitz map in Federer 3.2.38, pp. 274--275. *)
  missing_constant_lipschitz:is_metric_lipschitz_bound setT g 0;
  (** Source for [missing_constant_differential]: the actual zero
      differential at every source point, Federer 3.2.38, p. 275. *)
  missing_constant_differential:forall x,has_norm_differential
    (inner_norm (@euclidean_inner_productP R 1))
    (inner_norm (@euclidean_inner_productP R 1)) setT g x 0;
  (** Source for [missing_constant_image]: actual singleton image
      of the whole nonempty cube, Federer 3.2.38, p. 275. *)
  missing_constant_image:g @` K=[set (0%R:inner_metric_space (@euclidean_inner_productP R 1))];
  (** Source for [missing_constant_tube]: actual positive-radius
      normalized tube value, Federer 3.2.38, p. 275. *)
  missing_constant_tube:minkowski_tube_quotient 1 (g @` K) r=(2*r)%:E;
  (** Source for [missing_constant_printed_coefficient]: the sole
      printed positive-degree coefficient vanishes, Federer 3.2.38,
      p. 275. Its degree-zero coefficient must not be dropped. *)
  missing_constant_printed_coefficient:@integral_geometric_gauge R 1 1 (leqnn 1) 1 (g @` K)=0%E;
  (** Source for [missing_constant_failure]: the printed j= 1
      bound is false at every positive radius, Federer 3.2.38,
      p. 275. This correction is absent from the working erratum. *)
  missing_constant_failure:~(minkowski_tube_quotient 1 (g @` K) r<=
    @integral_geometric_gauge R 1 1 (leqnn 1) 1 (g @` K))%E
}.

(** Source for [missing_steiner_constant_counterexample_exists]:
    prove the actual counterexample to the first display of Federer
    3.2.38, p. 275, for every positive radius. The cube has
    unit length and the actual constant map has derivative zero;
    its positive tube disproves the omitted-constant intermediate
    estimate. The corrected proof retains j=0 in the error term. *)
Theorem missing_steiner_constant_counterexample_exists (R:realType) (r:R):
  0<r ->exists (K:set (inner_metric_space (@euclidean_inner_productP R 1)))
    (g:inner_metric_space (@euclidean_inner_productP R 1)->
      inner_metric_space (@euclidean_inner_productP R 1)),
    is_missing_steiner_constant_example r K g.
Proof.
move=>hr.
pose X:=[the metricType R of inner_metric_space (@euclidean_inner_productP R 1)].
pose K:set X:=coordinate_edge_box (fun _:'I_1=>(1:R)).
pose g:=fun _:X=>(0%R:X).
have hNonempty:K!=set0.
  apply:(@coordinate_edge_box_nonempty R 1 (fun _:'I_1=>(1:R))).
  by move=>i; exact:ler01.
have hImage:g @` K=[set (0%R:X)].
  apply/seteqP; split.
  - by move=>y [x hx <-].
  - move=>y ->; have [x hx]:=hNonempty; by exists x.
have hTube:minkowski_tube_quotient 1 (g @` K) r=(2*r)%:E.
  rewrite hImage; exact:(@line_singleton_minkowski_tube_quotient R 0%R r hr).
have hCoefficient:@integral_geometric_gauge R 1 1 (leqnn 1) 1 (g @` K)=0%E.
  rewrite hImage; exact:(@convex_intrinsic_singleton_positive_degree R 1 1 (leqnn 1) 0%R (ltnSn 0)).
exists K,g; constructor=>//.
- exact:(@coordinate_edge_box_compact R 1 (fun _:'I_1=>(1:R))).
- have h:=@euclidean_closed_box R 1 (fun _:'I_1=>(0:R)) (fun _:'I_1=>(1:R)) (fun _=>ler01).
  by rewrite big_ord1 subr0 in h.
- split; first exact:lexx.
  move=>x y _ _; by rewrite /g mdistxx mul0r.
- move=>x.
  apply:(@norm_differential_constant R (R_n R 1) (R_n R 1)
    (inner_norm (@euclidean_inner_productP R 1)) (inner_norm (@euclidean_inner_productP R 1))
    (inner_norm_real_norm (@euclidean_inner_productP R 1))
    (inner_norm_real_norm (@euclidean_inner_productP R 1)) setT x 0%R).
  exists 1; split; first exact:ltr01; by move=>h _.
- rewrite hTube hCoefficient lee_fin; move=>hBad.
  have hPositive:(0<2*r)%R:=mulr_gt0 (ltr0n R 2) hr.
  have hFalse:=lt_le_trans hPositive hBad; by rewrite ltxx in hFalse.
Qed.
