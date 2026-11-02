(** Federer (1969), 3.2.4, p. 244: every measurable
    source set has a Borel subset on which f is univalent,
    the actual Jacobian is positive, and the image loses
    only a Hausdorff-null set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanMetricCompleteness EuclideanMetricSeparability NormMetricScaleContinuity LipschitzUP Jacobian EuclideanLinearJacobian
  PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostBasic TopologicalBorel BorelFunctionBasic
  BorelPartition BorelSubordinatePartition InjectiveBorelImage InnerOwnNormTopology
  InjectiveDifferentialPieceUP InjectiveDifferentialCover EuclideanLipschitzClassZero
  AreaBorelReductionUP MeasurableAreaBorelReduction HausdorffMeasure CountableUnivalentSelection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_euclidean_jacobian_locus]: the set
    {x:J_m f(x)>0} in Federer 3.2.4, p. 244,
    using only actual values of the sealed Jacobian graph. *)
Definition positive_euclidean_jacobian_locus (R:realType) m n (f:R_n R m->R_n R n):=
  [set x|exists j,partial_function_graph (euclidean_jacobian m setT f) x j /\ 0<j].

(** Source for [positive_jacobian_injective_locus]: the equality
    of positive Jacobian and injective differential loci used
    in Federer 3.2.4, p. 244, by 1.7.6 and 3.2.1.
    Neither locus includes an undefined differential. *)
Lemma positive_jacobian_injective_locus (R:realType) m n (f:R_n R m->R_n R n):
  positive_euclidean_jacobian_locus f=injective_differential_locus f.
Proof.
apply/seteqP; split=>x.
- move=>[j [hj hPos]].
  have [D [hD hJ]]:=(euclidean_jacobian_graph m setT f x j).1 hj.
  exists D; split=>//; apply:((euclidean_linear_jacobian_top_positive D).1).
  by rewrite hJ.
- move=>[D [hD hInj]]; exists (euclidean_linear_jacobian m D); split.
  + apply:(euclidean_jacobian_graph m setT f x _).2; by exists D.
  + exact ((euclidean_linear_jacobian_top_positive D).2 hInj).
Qed.

(** Source for [euclidean_borel_area_selection]: the full
    corollary Federer 3.2.4, p. 244. Apply the Borel
    reduction of 3.2.3, cover by the injective pieces of
    3.2.2, and remove preimages of earlier piece images.
    Supports arbitrary ambient dimensions and source masses. *)
Theorem euclidean_borel_area_selection (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  exists B,@borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] B /\
    B `<=` A `&` positive_euclidean_jacobian_locus f /\
    (forall x y,B x -> B y -> f x=f y -> x=y) /\
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m
      ((f @` A) `\` (f @` B))=0)%E.
Proof.
move=>hLip hA.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
have [C [hC [hCA [hCLocus [hNu hNull]]]]]:=measurable_injective_area_subset hLip hA.
have [M [hM hBound]]:=hLip.
have hCont:continuous f.
  apply:(@metric_fixed_lipschitz_continuous R X Y f M (ltW hM)).
  by move=>x y; exact (hBound.2 x y I I).
have hZero:=euclidean_lipschitz_norm_class_zero hLip.
have hTwo:(1<(2:R)) by rewrite ltr1n.
have [G hG]:=injective_differential_borel_cover_exists hZero hTwo.
have hGB E:G E -> @borel_set X E.
  move=>hE; exact ((inner_own_norm_borel_iff (@euclidean_inner_productP R m) E).2 (hG.2.2 E hE).1).
have hCover:C `<=` \bigcup_(E in G) E by rewrite hG.2.1.
have [H [hH hSub]]:=borel_countable_cover_subordinate_partition hC hG.1 hGB hCover.
have hInj E:H E -> forall x y,E x -> E y -> f x=f y -> x=y.
  move=>hE x y hx hy he.
  have [_ [F [hF hEF]]]:=hSub E hE.
  exact ((hG.2.2 F hF).2.2.1 x y (mem_set (hEF x hx)) (mem_set (hEF y hy)) he).
have hImage E:H E -> @borel_set Y (f @` E).
  move=>hE; exact (@injective_borel_image_borel R X Y f E
    (@euclidean_metric_complete R m) (@euclidean_metric_separable R m)
    (@metric_hausdorff R Y) hCont (borel_partition_members hH hE) (hInj E hE)).
have [B [hB [hBH [hBi hImageB]]]]:=borel_univalent_countable_selection
  (continuous_borel_function hCont) (borel_partition_countable hH)
  (fun E hE=>borel_partition_members hH hE) hInj hImage.
rewrite (borel_partition_union hH) in hBH hImageB.
exists B; split=>//; split.
- move=>x hx; have hCx:=hBH x hx; split; first exact (hCA x hCx).
  rewrite positive_jacobian_injective_locus; exact (hCLocus x hCx).
split; first exact hBi.
apply:(@measure_null_subset R Y _ (@hausdorff_measure_is_measure R Y m)
  ((f @` A) `\` (f @` B)) (f @` (A `\` C)) _ hNull).
move=>y [[x hx hxy] hy]; exists x; last exact hxy.
split=>//; move=>hCx; apply:hy; rewrite hImageB; by exists x.
Qed.

(** Source for [federer_3_2_4]: Federer 3.2.4, p. 244,
    in the Lipschitz m<=n setting of 3.2.3. The Borel
    subset and its univalence and null image deficit are
    conclusions, not additional hypotheses. *)
Theorem federer_3_2_4 (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  (m<=n)%N -> is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  exists B,@borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] B /\
    B `<=` A `&` positive_euclidean_jacobian_locus f /\
    (forall x y,B x -> B y -> f x=f y -> x=y) /\
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m
      ((f @` A) `\` (f @` B))=0)%E.
Proof. move=>hmn; exact:euclidean_borel_area_selection. Qed.
