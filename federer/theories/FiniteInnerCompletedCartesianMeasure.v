(** Federer (1969), 3.2.48, p. 286: the
    actual Hausdorff restriction on X times Y is the
    product of the two actual factor restrictions. Supporting
    signed Fubini through 3.2.23, p. 260, with
    completed measurable original factors and genuine rectifiability
    of one factor. Equality holds on all test subsets. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric ProductInner FiniteInnerChartUP
  FiniteInnerChartCompact FiniteInnerChartMeasuredImages FiniteInnerCartesianGeometry
  FiniteInnerCartesianChart FiniteInnerRectifiableCoordinates
  FiniteInnerChartMeasureTransport FiniteInnerRectifiableCartesianProduct
  RectifiableSetUP RectifiableCompletedCartesianProduct RectifiableCartesianProductUP
  EuclideanCartesianMap EuclideanBlockCoordinates LipschitzRectifiableImages
  HausdorffMeasure HausdorffIsometryMeasurability MeasureUP MeasureRestriction
  MeasurePushforward InjectiveRestrictionPushforward ProductMeasure ProductMeasureUP
  ProductMeasureBijections MeasureBijectionCoordinateTransport MeasureBijectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_completed_cartesian_measure]: the
    all-set product measure identity needed for the iterated
    integrals in 3.2.48, p. 286, derived from
    3.2.23, p. 260, in the original Cartesian
    metric. Completed measurable factors and zero dimensions remain. *)
Theorem finite_inner_completed_cartesian_measure (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C) n v
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (f:Hom (R_n R v) W) (q:Hom W (R_n R v)) r mu (E:set V) (Z:set W):
  is_finite_inner_chart B e p ->is_finite_inner_chart C f q ->
  @is_m_rectifiable R (inner_metric_space hB) r E ->
  measure_measurable (@hausdorff_measure R (inner_metric_space hB) r) E ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hC) mu) mu Z ->
  measure_measurable (@hausdorff_measure R (inner_metric_space hC) mu) Z ->
  measure_restrict (@hausdorff_measure R
    (inner_metric_space (product_inner_productP hB hC)) (r+mu))
    [set z:V*W|E z.1 /\Z z.2]=
  product_measure
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R (inner_metric_space hB) r) E)
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R (inner_metric_space hC) mu) Z).
Proof.
move=>hV hW hE hEM hZ hZM.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose T:=inner_metric_space (@euclidean_inner_productP R (n+v)).
pose EC:=p @` E.
pose ZC:=q @` Z.
pose source:=euclidean_cartesian_set EC ZC.
pose alpha:=measure_restrict (@hausdorff_measure R X r) EC.
pose beta:=measure_restrict (@hausdorff_measure R Y mu) ZC.
pose rho:=measure_restrict (@hausdorff_measure R T (r+mu)) source.
pose ha:=measure_restrict_is_measure (@hausdorff_measure_is_measure R X r) EC.
pose hb:=measure_restrict_is_measure (@hausdorff_measure_is_measure R Y mu) ZC.
have hEC:=rectifiable_lipschitz_image
  (@finite_inner_chart_inverse_lipschitz R V B hB n e p E hV) hE.
have hEMC:=@finite_inner_chart_coordinates_measurable R V B hB n e p r E hV hEM.
have hZC:=@finite_inner_chart_measure_rectifiable_coordinates R W C hC v f q mu Z hW hZ.
have hZMC:=@finite_inner_chart_coordinates_measurable R W C hC v f q mu Z hW hZM.
have [hProduct _]:=rectifiable_completed_cartesian_product hEC hEMC hZC hZMC.
have hProductChart:=finite_inner_cartesian_chart hB hC hV hW.
pose J:=finite_inner_cartesian_direct e f.
pose Q:=finite_inner_cartesian_inverse p q.
have hJInjective:injective J:=can_inj (finite_inner_chart_left_inverse hProductChart).
have hImage:J @` source=[set z:V*W|E z.1 /\Z z.2].
  have hMap:(fun z=>J z)=finite_inner_cartesian_parametrization e f.
    exact (funext (finite_inner_cartesian_directE e f)).
  apply:(eq_trans (congr1 (fun F:R_n R (n+v)->(V*W)%type=>F @` source) hMap)).
  exact (@finite_inner_cartesian_parametrization_image R V W B C n v e p f q E Z hV hW).
have hJoint:measure_pushforward J rho=measure_restrict (@hausdorff_measure R
    (inner_metric_space (product_inner_productP hB hC)) (r+mu)) [set z:V*W|E z.1 /\Z z.2].
  rewrite /rho (injective_restriction_pushforward _ _ hJInjective) hImage.
  rewrite (@finite_inner_chart_direct_hausdorff_pushforward R [the lmodType R of (V*W)%type]
    _ (product_inner_productP hB hC) (n+v)%N J Q (r+mu)%N hProductChart).
  reflexivity.
have hAlpha:measure_pushforward e alpha=
    measure_restrict (@hausdorff_measure R (inner_metric_space hB) r) E.
  rewrite /alpha (injective_restriction_pushforward _ _ (can_inj (finite_inner_chart_left_inverse hV)))
    (@finite_inner_chart_coordinates_image R V B n e p E hV)
    (@finite_inner_chart_direct_hausdorff_pushforward R V B hB n e p r hV).
  reflexivity.
have hBeta:measure_pushforward f beta=
    measure_restrict (@hausdorff_measure R (inner_metric_space hC) mu) Z.
  rewrite /beta (injective_restriction_pushforward _ _ (can_inj (finite_inner_chart_left_inverse hW)))
    (@finite_inner_chart_coordinates_image R W C v f q Z hW)
    (@finite_inner_chart_direct_hausdorff_pushforward R W C hC v f q mu hW).
  reflexivity.
have hCompose:measure_pushforward J rho=
    measure_pushforward (cartesian_map e f)
      (measure_pushforward (@euclidean_block_split R n v) rho).
  apply:funext=>A; rewrite /measure_pushforward.
  congr (rho _); apply/seteqP; split=>z;
    change (A (J z) ->A (cartesian_map e f (euclidean_block_split z))) ||
    change (A (cartesian_map e f (euclidean_block_split z)) ->A (J z));
    by rewrite /J finite_inner_cartesian_directE.
rewrite -hJoint hCompose (rectifiable_cartesian_measure_law hProduct).
rewrite (@product_measure_bijection R X Y (inner_metric_space hB) (inner_metric_space hC)
  alpha beta ha hb e p f q (finite_inner_chart_left_inverse hV)
  (finite_inner_chart_right_inverse hV) (finite_inner_chart_left_inverse hW)
  (finite_inner_chart_right_inverse hW)).
have hInputs:is_product_measure
    (measure_restrict (@hausdorff_measure R (inner_metric_space hB) r) E)
    (measure_restrict (@hausdorff_measure R (inner_metric_space hC) mu) Z)
    (product_measure (measure_pushforward_is_measure e ha) (measure_pushforward_is_measure f hb)).
  rewrite -hAlpha -hBeta; exact:product_measure_specification.
exact (product_measure_unique hInputs (product_measure_specification _ _)).
Qed.


(** Source for [finite_inner_completed_cartesian_measure_right]:
    the whole original X times Y measure identity used
    in 3.2.48, p. 286, with genuinely rectifiable Y.
    The actual Cartesian interchange is an isometry and
    transposes the proved product measure on every subset. *)
Theorem finite_inner_completed_cartesian_measure_right (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C) n v
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (f:Hom (R_n R v) W) (q:Hom W (R_n R v)) r mu (E:set V) (Z:set W):
  is_finite_inner_chart B e p ->is_finite_inner_chart C f q ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hB) r) r E ->
  measure_measurable (@hausdorff_measure R (inner_metric_space hB) r) E ->
  @is_m_rectifiable R (inner_metric_space hC) mu Z ->
  measure_measurable (@hausdorff_measure R (inner_metric_space hC) mu) Z ->
  measure_restrict (@hausdorff_measure R
    (inner_metric_space (product_inner_productP hB hC)) (r+mu))
    [set z:V*W|E z.1 /\Z z.2]=
  product_measure
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R (inner_metric_space hB) r) E)
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R (inner_metric_space hC) mu) Z).
Proof.
move=>hV hW hE hEM hZ hZM.
have hReverse:=@finite_inner_completed_cartesian_measure R W V C B hC hB v n
  f q e p mu r Z E hW hV hZ hZM hE hEM.
pose P:=inner_metric_space (product_inner_productP hC hB).
pose Q:=inner_metric_space (product_inner_productP hB hC).
pose swap:=fun z:P=>((z.2,z.1):Q).
pose unswap:=fun z:Q=>((z.2,z.1):P).
have hLeft:cancel swap unswap by move=>[x y].
have hRight:cancel unswap swap by move=>[x y].
have hDistance x y:@mdist R Q (swap x) (swap y)=@mdist R P x y.
  rewrite !inner_metric_distanceE.
  change (inner_norm (product_inner_productP hB hC) (x.2-y.2,x.1-y.1)=
    inner_norm (product_inner_productP hC hB) (x-y)).
  exact (product_inner_swap_norm hC hB (x-y)).
have hImage:swap @` [set z:W*V|Z z.1 /\E z.2]=[set z:V*W|E z.1 /\Z z.2].
  apply/seteqP; split=>z.
  - by move=>[w [hwZ hwE] <-]; split.
  - move=>[hzE hzZ]; exists (z.2,z.1); first by split.
    exact (esym (surjective_pairing z)).
have hAll:=@hausdorff_bijective_isometry_pushforward R P Q swap unswap
  hLeft hRight hDistance (mu+r)%N.
have hRestricted:=@injective_restriction_pushforward R P Q (@hausdorff_measure R P (mu+r)%N)
  swap [set z:W*V|Z z.1 /\E z.2] (can_inj hLeft).
rewrite hAll hImage hReverse (addnC mu r) in hRestricted.
rewrite -hRestricted.
exact (measure_bijection_pushforward (measure_bijection_swap
  (measure_restrict_is_measure (@hausdorff_measure_is_measure R (inner_metric_space hC) mu) Z)
  (measure_restrict_is_measure (@hausdorff_measure_is_measure R (inner_metric_space hB) r) E))).
Qed.
