(** Federer (1969), 3.2.33, p. 270: the exact critical
    source X is Borel and has positive H^m mass. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric RealMetricBackground RealOpenIntervals
  NormMetricScaleContinuity EuclideanCoordinateMetric EuclideanOpenUnitCube EuclideanUnitCubeBorel
  EuclideanCoordinateSlabMass PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  RectifiablePositiveFibreCoareaUP HausdorffMeasure TopologicalBorel ContinuousBorelPreimages
  DenseSmallIntervalFamilyUP IntervalBumpPrimitiveUP ScalarCylinderMapUP ScalarCylinderCriticalSet LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_cylinder_critical_source_mass]: the
    equality H^m(X)=L^1(T minus V)>0 in Federer 3.2.33,
    p. 270. The exact original approximate rank locus is
    a Borel coordinate slab. The rectangle computation supplies
    its actual Hausdorff mass and the already proved interval
    family supplies strict positivity. This is not a rank
    assumption, measurable hull or an assumed integral bound. *)
Theorem scalar_cylinder_critical_source_mass (R:realType) mu k (a b:nat->R) (psi g:R->R)
    (F:R_n R ((mu+1)+k)->R_n R (mu+1)):
  is_scalar_cylinder_map g F ->is_dense_small_interval_family a b ->is_interval_bump_primitive a b psi g ->
  let f:=partial_function_source_restrict (@euclidean_open_unit_cube R ((mu+1)+k)) (partial_function_total F) in
  let X:=partial_approximate_image_dimension_locus ((mu+1)+k) mu f in
  @borel_set (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) X /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) ((mu+1)+k) X=
    lebesgue_scalar_measure (real_open_interval 0 1 `\` (\bigcup_j real_open_interval (a j) (b j))) /\
  (0< @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) ((mu+1)+k) X)%E.
Proof.
move=>hF hFamily hPrimitive f X.
pose K:=real_open_interval (0:R) 1 `\` (\bigcup_j real_open_interval (a j) (b j)).
have hK:borel_set K.
  apply:borel_set_difference; apply:open_borel_set; first exact:real_open_interval_open.
  apply:bigcup_open=>j _; exact:real_open_interval_open.
have hKT:K `<=` real_open_interval 0 1 by move=>t ht; exact ht.1.
have hExact:=scalar_cylinder_exact_critical_source hF hPrimitive.
have hP:continuous (fun x:inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))=>
    (x (lshift k (rshift mu ord0)):real_line_metric R)).
  apply:(@metric_fixed_lipschitz_continuous R (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k)))
    (real_line_metric R) (fun x=>x (lshift k (rshift mu ord0))) 1 (@ler01 R))=>x y.
  rewrite mul1r; exact:euclidean_coordinate_nonexpanding.
have hPre:=continuous_borel_preimage hP hK.
have hBorel:@borel_set (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) X.
  rewrite /X /f hExact.
  change (@borel_set (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k)))
    ((@euclidean_open_unit_cube R ((mu+1)+k)) `&`
    ((fun x=>x (lshift k (rshift mu ord0))) @^-1` K))).
  have hEq (A B:set (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k)))):
      A `&` B=A `\` (~` B) by rewrite setDE setCK.
  rewrite hEq.
  exact:(borel_set_difference (@euclidean_open_unit_cube_borel R ((mu+1)+k)) (borel_set_complement hPre)).
have hMass:@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R ((mu+1)+k))) ((mu+1)+k) X=
    lebesgue_scalar_measure K.
  rewrite /X /f hExact; exact:(euclidean_coordinate_slab_mass mu k hK hKT).
split; first exact hBorel.
split; first exact hMass.
rewrite hMass; exact:(dense_small_interval_positive_complement hFamily).
Qed.
