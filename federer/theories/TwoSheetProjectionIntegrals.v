(** Federer (1969), 3.2.27, pp. 262–263: local
    correction of the unrestricted upper inequality. These
    supporting two-sheet fibre computations use the actual
    counting integral of 2.10.10, p. 176, and
    retain nonmeasurable source pieces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanOneCoordinate EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  EuclideanLebesgueHaar EuclideanHausdorffLebesgue
  PartialFunctionUP PartialFunctionBasic ExtendedRealOrderTopology MappingMultiplicity MappingMultiplicityLaws
  PartitionMultiplicityIntegral MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureConullZeroIntegral BorelRegularMeasureUP TopologicalBorel
  HausdorffMeasure HausdorffCountableNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [two_sheet_horizontal_univalent]: actual
    horizontal fibre count in the local counterexample
    to 3.2.27, pp. 262–263. Complementary source
    pieces occupy exactly one sheet at each parameter,
    so projection is univalent despite nonmeasurability. *)
Lemma two_sheet_horizontal_univalent (R:realType) (X:choiceType)
    (L0 L1:real_line_metric R->X) (F:X->R_n R 1)
    (A V:set (real_line_metric R)):
  (forall t,F (L0 t)=euclidean_one_embed t) ->
  (forall t,F (L1 t)=euclidean_one_embed t) ->
  {in ((L0 @` V) `|` (L1 @` (A `\` V))) &,injective F}.
Proof.
move=>h0 h1 x y /set_mem hx /set_mem hy hF.
have hParameter (s t:real_line_metric R):euclidean_one_embed s=euclidean_one_embed t ->s=t.
  move=>h; have hEqual:=congr1 (@euclidean_one_project R) h.
  by rewrite !euclidean_one_embedK in hEqual.
case:hx=>[[s hs hS]|[s [hs hn] hS]]; case:hy=>[[t ht hT]|[t [ht hnt] hT]].
- have hp:=hF; rewrite -hS -hT !h0 in hp.
  by rewrite -hS -hT (hParameter s t hp).
- have hp:=hF; rewrite -hS -hT h0 h1 in hp; have he:=hParameter s t hp.
  exfalso; apply:hnt; by rewrite -he.
- have hp:=hF; rewrite -hS -hT h1 h0 in hp; have he:=hParameter s t hp.
  exfalso; apply:hn; by rewrite he.
- have hp:=hF; rewrite -hS -hT !h1 in hp.
  by rewrite -hS -hT (hParameter s t hp).
Qed.

(** Source for [two_sheet_horizontal_image]: the complete
    horizontal image in the local counterexample to
    3.2.27, pp. 262–263. Complementary sheets cover
    exactly the original parameter interval. *)
Lemma two_sheet_horizontal_image (R:realType) (X:choiceType)
    (L0 L1:real_line_metric R->X) (F:X->R_n R 1)
    (A V:set (real_line_metric R)):
  V `<=` A ->
  (forall t,F (L0 t)=euclidean_one_embed t) ->
  (forall t,F (L1 t)=euclidean_one_embed t) ->
  F @` ((L0 @` V) `|` (L1 @` (A `\` V)))=(@euclidean_one_embed R) @` A.
Proof.
move=>hVA h0 h1; apply/seteqP; split.
- move=>y [x [[t ht <-]|[t [ht hn] <-]] <-].
  + rewrite h0; exists t; first exact:hVA t ht; reflexivity.
  + rewrite h1; by exists t.
- move=>y [t ht <-]; have [hv|hv]:=pselect (V t).
  + exists (L0 t).
    * left; by exists t.
    * exact:h0 t.
  + exists (L1 t).
    * right; exists t; first exact:(conj ht hv); reflexivity.
    * exact:h1 t.
Qed.

(** Source for [two_sheet_horizontal_unit_integral]: the
    horizontal coordinate mass a_0=1 in the local
    counterexample to 3.2.27, pp. 262–263. The
    actual counting function is integrable because its
    univalent image is the whole unit interval, even
    though its two source pieces are nonmeasurable. *)
Lemma two_sheet_horizontal_unit_integral (R:realType) (X:choiceType)
    (L0 L1:real_line_metric R->X) (F:X->R_n R 1)
    (V:set (real_line_metric R)):
  V `<=` `[(0%R:R),1%R] ->
  (forall t,F (L0 t)=euclidean_one_embed t) ->
  (forall t,F (L1 t)=euclidean_one_embed t) ->
  is_measure_integral (@euclidean_lebesgue_measure R 1)
    (partial_function_total (fun y=>(@mapping_multiplicity R X (R_n R 1) F
      ((L0 @` V) `|` (L1 @` (`[(0%R:R),1%R] `\` V))) y:extended_real_line R))) 1.
Proof.
move=>hV h0 h1.
pose Y:=inner_metric_space (@euclidean_inner_productP R 1).
pose beta:=@euclidean_lebesgue_measure R 1.
pose W:=(L0 @` V) `|` (L1 @` (`[(0%R:R),1%R] `\` V)).
pose Q:set Y:=[set x|forall i,0<=x i<=1]%R.
have hImage:F @` W=Q.
  rewrite (@two_sheet_horizontal_image R X L0 L1 F `[(0%R:R),1%R] V hV h0 h1).
  apply/seteqP; split.
  - move=>x [t ht <-] i; by rewrite /euclidean_one_embed ffunE.
  - move=>x hx; exists (euclidean_one_project x); first exact:hx ord0.
    exact:euclidean_one_projectK.
have hQ:measure_measurable beta Q.
  apply:(borel_regular_borel_measurable (@euclidean_lebesgue_is_measure R 1)
    (@euclidean_lebesgue_borel_regular R 1)).
  apply:closed_borel_set.
  exact:(compact_closed (@metric_hausdorff R Y)
    (@euclidean_closed_box_compact R 1 (fun _:'I_1=>0%R) (fun _:'I_1=>1%R))).
have hMass:beta Q= 1.
  rewrite /beta (@euclidean_closed_box R 1 (fun _:'I_1=>0%R) (fun _:'I_1=>1%R)); last by move=>i; exact:ler01.
  by rewrite big_ord_recl big_ord0 subr0 mulr1.
have hMeasImage:measure_measurable beta (F @` W) by rewrite hImage.
have hIntegral:=@injective_multiplicity_integral R X (Choice.clone Y _) F W beta
  (@euclidean_lebesgue_is_measure R 1) (@two_sheet_horizontal_univalent R X L0 L1 F
    `[(0%R:R),1%R] V h0 h1) hMeasImage.
by rewrite hImage hMass in hIntegral.
Qed.

(** Source for [two_sheet_vertical_integral_zero]: vertical
    coordinate mass a_1=0 in the local counterexample
    to 3.2.27, pp. 262–263. The possibly infinite
    counting values are supported on two Lebesgue-null
    target points. They are retained until the exact
    conull-zero integral law is applied. *)
Lemma two_sheet_vertical_integral_zero (R:realType) (X:choiceType)
    (L0 L1:real_line_metric R->X) (F:X->R_n R 1)
    (A V:set (real_line_metric R)):
  (forall t,F (L0 t)=euclidean_one_embed 0%R) ->
  (forall t,F (L1 t)=euclidean_one_embed 1%R) ->
  is_measure_integral (@euclidean_lebesgue_measure R 1)
    (partial_function_total (fun y=>(@mapping_multiplicity R X (R_n R 1) F
      ((L0 @` V) `|` (L1 @` (A `\` V))) y:extended_real_line R))) 0.
Proof.
move=>h0 h1.
pose Y:=inner_metric_space (@euclidean_inner_productP R 1).
pose beta:=@euclidean_lebesgue_measure R 1.
pose W:=(L0 @` V) `|` (L1 @` (A `\` V)).
pose N:set Y:=[set euclidean_one_embed 0%R] `|` [set euclidean_one_embed 1%R].
have hBeta:=@euclidean_lebesgue_is_measure R 1.
have hSingleton t:beta [set euclidean_one_embed t]=0.
  rewrite /beta -(euclidean_hausdorff_spherical_lebesgue [set euclidean_one_embed t]).1.
  exact:(@hausdorff_positive_degree_singleton_zero R Y 1 (euclidean_one_embed t) (erefl true)).
have hNull:beta N=0.
  have hCover:=@measure_binary_cover R (Choice.clone Y _) beta hBeta N
    [set euclidean_one_embed 0%R] [set euclidean_one_embed 1%R] (fun x hx=>hx).
  rewrite !hSingleton add0e in hCover.
  apply/eqP; by rewrite eq_le hCover (measure_nonnegative hBeta N).
have hOutside:measure_almost_everywhere beta (~` N).
  by rewrite /measure_almost_everywhere setCK.
apply:(measure_almost_zero_integral hBeta).
apply:(measure_almost_everywhere_mono hBeta _ hOutside)=>y hn.
apply:(@mapping_multiplicity_zero_iff R X Y F W y).2.
move=>[x [[t ht <-]|[t ht <-]] he]; apply:hn.
- left; rewrite -he h0; reflexivity.
- right; rewrite -he h1; reflexivity.
Qed.
