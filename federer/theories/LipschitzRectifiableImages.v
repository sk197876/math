(** Federer (1969), 3.2.22(2), p. 258: pass
    coordinate fibre rectifiability through the Lipschitz source
    chart. The supporting consequences use the definitions
    of 3.2.14, pp. 251–252, and 2.10.11. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import LipschitzUP LipschitzBasic RectifiableSetUP RectifiableElementary
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialMetricLipschitz
  HausdorffMeasure HausdorffRestrictedLipschitz MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_lipschitz_image]: supporting
    source-chart images of fibres in Federer 3.2.22(2),
    p. 258, from 3.2.14(1), p. 251.
    Compose the actual bounded partial parametrization with
    the Lipschitz map. Degree zero uses the printed finite-set
    convention, so all degrees and empty images are retained. *)
Lemma rectifiable_lipschitz_image (R:realType) (X Y:metricType R) m
    (S:set X) (f:X->Y):
  is_metric_lipschitz S f ->is_m_rectifiable m S ->is_m_rectifiable m (f @` S).
Proof.
move=>[M [hM hF]]; case:m=>[|m]; first by move=>hFinite; exact:(finite_image f hFinite).
move=>[p [hBounded [[L hL] hRange]]].
pose g:=partial_function_postcompose p f.
exists g; split.
- by rewrite /g partial_function_postcompose_domain.
- split.
  + exists (M*L); split; first exact:(mulr_ge0 hF.1 hL.1).
    move=>a b y z [x [hax hxy]] [t [hbt htz]].
    have hx:S x by rewrite -hRange; by exists a.
    have ht:S t by rewrite -hRange; by exists b.
    rewrite -hxy -htz.
    apply:(le_trans (hF.2 x t hx ht) _); rewrite -mulrA.
    exact:(ler_wpM2l hF.1 (hL.2 a b x t hax hbt)).
  + apply/seteqP; split=>y.
    * move=>[a [x [hax hxy]]]; exists x; last exact hxy.
      rewrite -hRange; by exists a.
    * move=>[x hx hxy]; have hxP:partial_function_range p x by rewrite hRange.
      have [a ha]:=hxP; exists a; exists x; by split.
Qed.

(** Source for [countably_rectifiable_lipschitz_image]:
    supporting countable source-chart fibre images in Federer
    3.2.22(2), p. 258, by the countable-family
    definition 3.2.14(2), p. 251. No boundedness
    of the whole source set or fibre mass is required. *)
Lemma countably_rectifiable_lipschitz_image (R:realType) (X Y:metricType R) m
    (S:set X) (f:X->Y):
  is_metric_lipschitz S f ->is_countably_m_rectifiable m S ->
  is_countably_m_rectifiable m (f @` S).
Proof.
move=>[M [hM hF]] [C [hCount [hC hUnion]]].
exists ((fun E:set X=>f @` E) @` C); split.
- exact:(sub_countable (card_image_le _ C) hCount).
- split.
  + move=>E [A hA <-]; apply:(rectifiable_lipschitz_image _ (hC A hA)).
    exists M; split; first exact hM.
    apply:(metric_lipschitz_bound_restrict _ hF)=>x hx; rewrite hUnion; by exists A.
  + apply/seteqP; split=>y.
    * move=>[x hx hxy]; rewrite hUnion in hx; have [A hA hAx]:=hx.
      exists (f @` A); first by exists A.
      by exists x.
    * move=>[E [A hA <-] [x hx hxy]]; exists x; last exact hxy.
      rewrite hUnion; by exists A.
Qed.

(** Source for [countably_hausdorff_rectifiable_lipschitz_image]:
    supporting almost-everywhere fibre parametrizations in
    Federer 3.2.22(2), p. 258. Restrict the
    countable rectifiable cover to the actual source;
    2.10.11 transports its null remainder. No completed-
    measure image measurability or finite mass is assumed. *)
Lemma countably_hausdorff_rectifiable_lipschitz_image (R:realType) (X Y:metricType R) m
    (S:set X) (f:X->Y):
  is_metric_lipschitz S f ->
  is_countably_measure_m_rectifiable (@hausdorff_measure R X m) m S ->
  is_countably_measure_m_rectifiable (@hausdorff_measure R Y m) m (f @` S).
Proof.
move=>hLip [hm [C [hC hNull]]].
have [M [hM hF]]:=hLip.
pose C0:=C `&` S.
have hC0:is_countably_m_rectifiable m C0:=@countably_rectifiable_subset R X m C C0
  (fun x hx=>hx.1) hC.
have hLip0:is_metric_lipschitz C0 f.
  exists M; split; first exact hM; apply:(metric_lipschitz_bound_restrict _ hF)=>x hx; exact hx.2.
have hImageC:is_countably_m_rectifiable m (f @` C0):=countably_rectifiable_lipschitz_image hLip0 hC0.
have hImageNull:@hausdorff_measure R Y m (f @` (S `\` C))=0%E.
  have hBound:=@hausdorff_lipschitz_on_bound R X Y S f M m (S `\` C) hF (fun x hx=>hx.1).
  rewrite hNull mule0 in hBound.
  apply/eqP; by rewrite eq_le hBound (measure_nonnegative (@hausdorff_measure_is_measure R Y m)).
split; first exact:hausdorff_measure_is_measure.
exists (f @` C0); split; first exact hImageC.
apply:(measure_null_subset (@hausdorff_measure_is_measure R Y m) _ hImageNull)=>y [[x hx hxy] hNot].
exists x; last exact hxy; split; first exact hx.
move=>hCx; apply:hNot; exists x; last exact hxy; by split.
Qed.
