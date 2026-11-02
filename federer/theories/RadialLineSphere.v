(** Federer (1969), 3.2.13, p. 250: the
    positive-radius sphere in R^1 consists of
    the two points r and -r, each with
    H^0 mass one. This covers the boundary
    dimension omitted by strict-dimensional coarea. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanOneCoordinate EuclideanOneNormDifferential RadialSphereIntegral UnitAtomPairIntegral
  HausdorffMeasure HausdorffCountingMeasure CountingMeasure MeasureUP MeasureFiniteClosure
  PartialFunctionUP SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [radial_line_sphere_pair]: the m=1
    positive-radius sphere underlying polar integration
    in Federer 3.2.13, p. 250. *)
Lemma radial_line_sphere_pair (R:realType) (r:R):
  0<r ->[set x:R_n R 1|inner_norm (@euclidean_inner_productP R 1) x=r]=
    [set euclidean_one_embed r] `|` [set euclidean_one_embed (-r)].
Proof.
move=>hr; apply/seteqP; split=>x /=.
- rewrite euclidean_one_norm_coordinate=>hx.
  have hCases:(x ord0==r) || (x ord0== -r).
    have he:(`|x ord0|==r) by apply/eqP.
    by move:he; rewrite eqr_norml (ltW hr) andbT.
  have hX:euclidean_one_embed (x ord0)=x:=euclidean_one_projectK x.
  case/orP:hCases=>/eqP he.
  + left; by rewrite -hX he.
  + right; by rewrite -hX he.
- move=>[hx|hx]; rewrite hx euclidean_one_norm_coordinate /euclidean_one_embed ffunE.
  + exact:ger0_norm (ltW hr).
  + by rewrite normrN ger0_norm ?(ltW hr).
Qed.

(** Source for [radial_line_sphere_integral]: the
    actual inner H^0 integral on a positive
    radius sphere in the m=1 polar formula,
    Federer 3.2.13, p. 250, for arbitrary
    real weights with no sign or measurability restriction. *)
Lemma radial_line_sphere_integral (R:realType) (g:R_n R 1->R) (r:R):
  0<r ->partial_function_graph (radial_sphere_integral (real_total_integrand g)) r
    (g (euclidean_one_embed r)+g (euclidean_one_embed (-r)))%:E.
Proof.
move=>hr; apply/radial_sphere_integral_graph.
rewrite radial_line_sphere_pair //.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose mu:=@hausdorff_measure R X 0.
pose hm:=@hausdorff_measure_is_measure R X 0.
have hDistinct:euclidean_one_embed r!=euclidean_one_embed (-r).
  apply/eqP=>he; have hh:=congr1 (@euclidean_one_project R) he.
  rewrite !euclidean_one_embedK in hh; lra.
have he:mu=(@counting_measure R X).
  apply:funext=>A; exact:hausdorff_zero_counting_measure.
have hMeas (x:X):measure_measurable mu [set x].
  rewrite he; exact:counting_measure_measurable.
have hMass (x:X):mu [set x]=(1%R)%:E:=@hausdorff_zero_singleton R X x.
exact (@unit_atom_pair_subset_integral R X mu hm g
  (euclidean_one_embed r) (euclidean_one_embed (-r)) hDistinct
  (hMeas _) (hMeas _) (hMass _) (hMass _)).
Qed.
