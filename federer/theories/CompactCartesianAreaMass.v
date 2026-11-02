(** Federer (1969), 3.2.23, p. 260: the displayed area
    calculation on injective product parameter sets. Compact source
    pieces suffice for the subsequent countable decomposition. The
    proof retains the printed product differential and separated integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanCartesianBorel EuclideanCartesianCutoffs
  EuclideanCartesianJacobianAlmost EuclideanJacobianBorelRepresentatives OrdinaryJacobianSubsetRepresentative
  CompactLipschitzImageMass InjectiveAreaMass EuclideanJacobianMeasurable EuclideanSeparatedIntegral
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes HausdorffMeasure LipschitzUP
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureIntegralAlmostEquality MeasureDensityTransfer MeasureSubsetIntegral
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension TotalScalarCutoff SummableRealFunctionUP
  TopologicalBorel RealMetricBackground ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_cartesian_injective_area_mass]: the displayed
    product formula of Federer 3.2.23, p. 260, on Borel injective
    parameter pieces of finite image mass: H^(m+mu)(f(A) times g(B))=H^m(f(A)) H^mu(g(B)).
    The actual Jacobian is preserved up to a proved conull agreement;
    no arbitrary completed-measure representative is pulled back through
    a map. Finiteness is required only for this separated finite-integral step;
    compact parameter pieces discharge it in the following corollary. *)
Theorem euclidean_cartesian_injective_area_mass (R:realType) m mu n v
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (g:inner_metric_space (@euclidean_inner_productP R mu)->
      inner_metric_space (@euclidean_inner_productP R v))
    (A:set (R_n R m)) (B:set (R_n R mu)):
  is_metric_lipschitz setT f ->is_metric_lipschitz setT g ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R m)) A ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R mu)) B ->
  (forall x y,A x ->A y ->f x=f y ->x=y) ->
  (forall x y,B x ->B y ->g x=g y ->x=y) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (f @` A)< +oo ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu (g @` B)< +oo ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu)
    (euclidean_cartesian_set (f @` A) (g @` B))=
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (f @` A)*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu (g @` B).
Proof.
move=>hF hG hA hB hInjectF hInjectG hFiniteF hFiniteG.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R mu).
pose U:=inner_metric_space (@euclidean_inner_productP R n).
pose V:=inner_metric_space (@euclidean_inner_productP R v).
pose T:=inner_metric_space (@euclidean_inner_productP R (m+mu)).
pose H:=@hausdorff_measure R U m.
pose K:=@hausdorff_measure R V mu.
pose P:=euclidean_cartesian_map f g.
pose S:=euclidean_cartesian_set A B.
have hAM:=euclidean_borel_measurable hA.
have hBM:=euclidean_borel_measurable hB.
have hSM:=euclidean_borel_measurable (euclidean_cartesian_borel hA hB).
have hInjF:{in A &,injective f}.
  move=>x y hx hy; exact:(hInjectF x y (set_mem hx) (set_mem hy)).
have hInjG:{in B &,injective g}.
  move=>x y hx hy; exact:(hInjectG x y (set_mem hx) (set_mem hy)).
have hP:=euclidean_cartesian_map_lipschitz hF hG.
have hInjP:{in S &,injective P}.
  move=>x y hx hy; exact:(euclidean_cartesian_map_injective_on hInjectF hInjectG
    (set_mem hx) (set_mem hy)).
have [J [_ [_ hJ]]]:=euclidean_top_jacobian_borel_representative_exists hF.
have [L [_ [_ hL]]]:=euclidean_top_jacobian_borel_representative_exists hG.
have hIF:=(@ordinary_jacobian_subset_representative R m n m f A J hF hJ (H (f @` A))).1
  (euclidean_injective_area_mass hF hAM hInjF).
have hIG:=(@ordinary_jacobian_subset_representative R mu v mu g B L hG hL (K (g @` B))).1
  (euclidean_injective_area_mass hG hBM hInjG).
have hJF:=measure_integral_graph_equivalent (@total_embedded_scalar_cutoff_graph R (R_n R m) A J) hIF.
have hLG:=measure_integral_graph_equivalent (@total_embedded_scalar_cutoff_graph R (R_n R mu) B L) hIG.
have hFinF:H (f @` A) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (@hausdorff_measure_is_measure R U m) _)).
  exact hFiniteF.
have hFinG:K (g @` B) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (@hausdorff_measure_is_measure R V mu) _)).
  exact hFiniteG.
pose a:=fine (H (f @` A)).
pose b:=fine (K (g @` B)).
have hJA:is_measure_integral (@euclidean_lebesgue_measure R m)
    (real_total_integrand (total_scalar_cutoff A J)) a%:E.
  by rewrite /a fineK.
have hLB:is_measure_integral (@euclidean_lebesgue_measure R mu)
    (real_total_integrand (total_scalar_cutoff B L)) b%:E.
  by rewrite /b fineK.
have hProduct:=euclidean_separated_integral hJA hLB.
rewrite -(euclidean_cartesian_scalar_cutoff_product A B J L) in hProduct.
have hProductSubset:=measure_integral_graph_equivalent
  (fun p z=>iff_sym (@total_embedded_scalar_cutoff_graph R (R_n R (m+mu)) S
    (fun p=>(J (euclidean_block_split p).1*L (euclidean_block_split p).2)%R) p z)) hProduct.
have hArea:=euclidean_injective_area_mass hP hSM hInjP.
have hAgreement:=euclidean_cartesian_jacobian_almost hF hG hJ hL.
have hAreaRepresentative:=measure_integral_almost_equal (euclidean_lebesgue_is_measure R (m+mu))
  hArea (zero_extension_almost_equal (euclidean_lebesgue_is_measure R (m+mu)) 0 S hAgreement).
have hValue:=measure_integral_unique hAreaRepresentative hProductSubset.
rewrite -euclidean_cartesian_map_image.
change (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+v)))
  (m+mu) (P @` S)=H (f @` A)*K (g @` B)).
rewrite -(fineK hFinF) -(fineK hFinG) -EFinM.
exact hValue.
Qed.

(** Source for [compact_cartesian_injective_area_mass]: compact
    injective image pieces in Federer 3.2.23, p. 260. All Borel
    and finite-mass premises of the supporting area calculation are
    proved here, including empty pieces and dimension zero. *)
Theorem compact_cartesian_injective_area_mass (R:realType) m mu n v
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (g:inner_metric_space (@euclidean_inner_productP R mu)->
      inner_metric_space (@euclidean_inner_productP R v))
    (A:set (R_n R m)) (B:set (R_n R mu)):
  is_metric_lipschitz setT f ->is_metric_lipschitz setT g ->
  @compact (inner_metric_space (@euclidean_inner_productP R m)) A ->
  @compact (inner_metric_space (@euclidean_inner_productP R mu)) B ->
  (forall x y,A x ->A y ->f x=f y ->x=y) ->
  (forall x y,B x ->B y ->g x=g y ->x=y) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu)
    (euclidean_cartesian_set (f @` A) (g @` B))=
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (f @` A)*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu (g @` B).
Proof.
move=>hF hG hA hB hInjectF hInjectG.
exact:(euclidean_cartesian_injective_area_mass hF hG
  (closed_borel_set (compact_closed (@metric_hausdorff R _) hA))
  (closed_borel_set (compact_closed (@metric_hausdorff R _) hB)) hInjectF hInjectG
  (compact_lipschitz_image_finite_hausdorff_mass hF hA)
  (compact_lipschitz_image_finite_hausdorff_mass hG hB)).
Qed.
