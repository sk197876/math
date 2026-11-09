(** Federer (1969), 3.3.16, pp. 299–300: finite actual
    I-infinity outer mass makes EVERY original exponent agree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffMeasure IntegralGeometricMeasure
  IntegralGeometricNullSets StructureInfinityRectifiability StructureReplacementCarrierAgreement
  CountablyRectifiableBorelEnlargement RectifiableSetUP RectifiableFiniteHausdorffMass
  RectifiableGeometricMeasureEquality BorelRegularMeasureUP MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_countably_rectifiable_agreement]:
    supporting 3.2.26/countable-carrier argument in Federer
    3.3.16, p. 299. Actual bounded-image agreement and Borel
    splitting extend to EVERY original subset of a countably
    rectifiable carrier. No finite whole-carrier mass is needed. *)
Lemma integral_geometric_countably_rectifiable_agreement (R:realType) n m (hmn:(m<=n)%N)
    (A S:set (inner_metric_space (@euclidean_inner_productP R n))) (t: \bar R):
  1<=t ->is_countably_m_rectifiable m S ->A `<=` S ->
  @integral_geometric_measure R n m hmn t A=@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m A.
Proof.
move=>ht.
apply:(@countably_rectifiable_measure_agreement R n m
  (@integral_geometric_measure R n m hmn t) A S
  (@integral_geometric_measure_is_measure R n m hmn t ht)
  (@integral_geometric_measure_borel_regular R n m hmn t ht)).
move=>F hF; exact:((@federer_3_2_26 R m n hmn F (rectifiable_hausdorff_measure_rectifiable hF)).2.2.2 t ht).2.
Qed.

(** Source for [federer_3_3_16_exponent_agreement]: the second
    mathematical assertion in Federer 3.3.16, pp. 299–300.
    If ORIGINAL I-infinity(E) is finite, I_t(E)=I-infinity(E)
    for EVERY 1<=t<=infinity. Actual 3.3.14 supplies the carrier;
    actual 2.10.5 transfers its original null remainder to every
    exponent, and proved countable carrier agreement handles the
    unchanged original intersection. No finite Hausdorff mass,
    source measurability or deferred comparison theorem is assumed. *)
Theorem federer_3_3_16_exponent_agreement (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))) (t: \bar R):
  @integral_geometric_measure R n m hmn +oo E< +oo ->1<=t ->
  @integral_geometric_measure R n m hmn t E=@integral_geometric_measure R n m hmn +oo E.
Proof.
move=>hFinite ht.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose I:=@integral_geometric_measure R n m hmn t.
pose J:=@integral_geometric_measure R n m hmn +oo.
have [[hJ [S [hS hNull]]] hJFinite]:=@federer_3_3_14 R n m hmn E hFinite.
have [U [hSU [hU hURect]]]:=countably_rectifiable_borel_enlargement hS.
have hUNull:J (E `\` U)=0.
  apply:(@measure_null_subset R [the choiceType of X] J hJ _ _ _ hNull).
  by move=>x [hx hn]; split=>//; move=>hs; exact:hn (hSU x hs).
have hINull:I (E `\` U)=0.
  apply:(@integral_geometric_projection_null_iff R n m hmn t (E `\` U) ht).2.
  exact:(@integral_geometric_projection_null_iff R n m hmn +oo (E `\` U) (leey 1)).1 hUNull.
have hI:is_measure I:=@integral_geometric_measure_is_measure R n m hmn t ht.
have hISplit:=borel_regular_borel_measurable hI (@integral_geometric_measure_borel_regular R n m hmn t ht) hU E.
have hJSplit:=borel_regular_borel_measurable hJ (@integral_geometric_measure_borel_regular R n m hmn +oo (leey 1)) hU E.
change (I E=I (E `&` U)+I (E `\` U)) in hISplit.
rewrite hINull adde0 in hISplit.
change (J E=J (E `&` U)+J (E `\` U)) in hJSplit.
rewrite hUNull adde0 in hJSplit.
change (I E=J E).
rewrite hISplit hJSplit /I /J.
have hSub:E `&` U `<=` U by move=>x [_ hx].
rewrite (@integral_geometric_countably_rectifiable_agreement R n m hmn _ U t ht hURect hSub).
exact:esym (@integral_geometric_countably_rectifiable_agreement R n m hmn _ U +oo (leey 1) hURect hSub).
Qed.
