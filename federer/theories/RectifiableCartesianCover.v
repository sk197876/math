(** Federer (1969), 3.2.23, p. 260: countable rectifiability
    of the Cartesian image, together with the null target remainder.
    The first factor retains actual m-rectifiability throughout. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap RectifiableSetUP RectifiableElementary
  RectifiableGlobalLipschitzCover EuclideanLipschitzRectifiableImage CountablyRectifiableUnions
  RectifiableProductNullFactor HausdorffMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_cartesian_countably_rectifiable]: the
    image inclusion W times Z contained in im(f times g) in
    Federer 3.2.23, p. 260. Both factors here are genuinely
    rectifiable; the result supplies the exact countable cover and
    includes all zero-dimensional conventions. *)
Lemma rectifiable_cartesian_countably_rectifiable (R:realType) m mu n v
    (W:set (R_n R n)) (Z:set (R_n R v)):
  (@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m W) ->(@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R v)) mu Z) ->
  @is_countably_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu) (euclidean_cartesian_set W Z).
Proof.
move=>hW hZ.
have [F [hF hCoverF]]:=rectifiable_global_lipschitz_cover hW.
have [G [hG hCoverG]]:=rectifiable_global_lipschitz_cover hZ.
pose Index:=(nat*nat)%type.
pose D:=fun p:Index=>euclidean_cartesian_map (F p.1) (G p.2) @` setT.
have hD p:@is_countably_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu) (D p).
  exact:(euclidean_lipschitz_image_countably_rectifiable
    (euclidean_cartesian_map_lipschitz (hF p.1) (hG p.2))).
have hAll:@is_countably_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu) (\bigcup_p D p).
  exact:(@countably_rectifiable_countable_union R
    (inner_metric_space (@euclidean_inner_productP R (n+v))) [the choiceType of (Index:Type)]
    (m+mu) setT D (countableP setT) (fun p _=>hD p)).
apply:(countably_rectifiable_subset _ hAll)=>p [hpW hpZ].
have [i _ [x _ hfx]]:=hCoverF _ hpW.
have [j _ [y _ hgy]]:=hCoverG _ hpZ.
exists (i,j); first exact Logic.I.
exists (euclidean_block_join (x,y)); first exact Logic.I.
rewrite /euclidean_cartesian_map euclidean_block_joinK /= hfx hgy.
exact:euclidean_block_splitK.
Qed.

(** Source for [rectifiable_cartesian_countable_second]: supporting
    countable target-image reduction in Federer 3.2.23, p. 260,
    using the family definition in 3.2.14(2), p. 251. *)
Lemma rectifiable_cartesian_countable_second (R:realType) m mu n v
    (W:set (R_n R n)) (Z:set (R_n R v)):
  (@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m W) ->(@is_countably_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R v)) mu Z) ->
  @is_countably_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu) (euclidean_cartesian_set W Z).
Proof.
move=>hW [C [hCount [hC hUnion]]].
have hSet:euclidean_cartesian_set W Z=\bigcup_(A in C) euclidean_cartesian_set W A.
  apply/seteqP; split.
  - move=>p [hpW hpZ]; rewrite hUnion in hpZ; have [A hA hpA]:=hpZ.
    exists A; first exact hA; by split.
  - move=>p [A hA [hpW hpA]]; split; first exact hpW.
    rewrite hUnion; by exists A.
rewrite hSet; apply:(countably_rectifiable_countable_union hCount)=>A hA.
exact:(rectifiable_cartesian_countably_rectifiable hW (hC A hA)).
Qed.

(** Source for [rectifiable_cartesian_countably_measure_rectifiable]:
    the first conclusion of Federer 3.2.23, p. 260, before
    finite mass is identified. The first factor is genuinely
    m-rectifiable; its product with the omitted H^mu-null target
    part is null by the printed 2.10.45 argument. *)
Theorem rectifiable_cartesian_countably_measure_rectifiable (R:realType) m mu n v
    (W:set (R_n R n)) (Z:set (R_n R v)):
  (@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m W) ->
  is_countably_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  is_countably_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu))
    (m+mu) (euclidean_cartesian_set W Z).
Proof.
move=>hW [_ [S [hS hNull]]]; split; first exact:hausdorff_measure_is_measure.
exists (euclidean_cartesian_set W S); split.
- exact:(rectifiable_cartesian_countable_second hW hS).
- apply:(measure_null_subset (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu)) _
    (rectifiable_product_null_factor hW hNull)).
  move=>p [[hpW hpZ] hNot]; split; first exact hpW.
  split; first exact hpZ.
  move=>hSp; apply:hNot; by split.
Qed.
