(** Federer (1969), 3.3.16, p. 299: the literal mass
    identity and rectifiable equality for the replacement measures. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric StructureReplacementMeasureUP
  StructureReplacementCarrierAgreement StructureReplacementNullSets CountablyRectifiableBorelEnlargement
  RectifiableSetUP RectifiableGeometricMeasureEquality HausdorffMeasure
  IntegralGeometricMeasure MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_replacement_rectifiable_mass_split]:
    the literal subsidiary mass display of 3.3.13, p. 298,
    with the replacement required by Federer 3.3.16, p. 299.
    Actual arbitrary-subset carrier agreement proves finite H^m
    on the ORIGINAL intersection E intersect B. Actual 3.2.26
    and Borel splitting of both original measures give the identity. *)
Lemma structure_replacement_rectifiable_mass_split (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E B:set (inner_metric_space (@euclidean_inner_productP R n))) (t: \bar R):
  is_structure_replacement_measure m phi ->phi E< +oo ->1<=t ->
  borel_set B ->is_countably_m_rectifiable m B ->
  @integral_geometric_measure R n m hmn t (E `\` B)=0 ->
  phi E=@integral_geometric_measure R n m hmn t E+phi (E `\` B).
Proof.
move=>hLaws hFinite ht hB hRect hNull.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R [the metricType R of X] m.
pose I:=@integral_geometric_measure R n m hmn t.
have hPhi:=structure_replacement_measure_law hLaws.
have hI:is_measure I:=@integral_geometric_measure_is_measure R n m hmn t ht.
have hPart:@is_countably_m_rectifiable R [the metricType R of X] m B:=hRect.
have hEquality:phi (E `&` B)=H (E `&` B).
  apply:(@structure_replacement_carrier_agreement R n m phi _ B hLaws hRect).
  by move=>x [_ hx].
have hHFinite:H (E `&` B)< +oo.
  rewrite -hEquality; apply:le_lt_trans _ hFinite.
  apply:(@measure_mono R _ phi hPhi)=>x [hx _]; exact:hx.
have hPartRect:is_measure_m_rectifiable H m (E `&` B).
  split; last exact:hHFinite.
  split; first exact:hausdorff_measure_is_measure.
  exists B; split; first exact:hRect.
  have hEmpty:(E `&` B) `\` B=set0 by apply/seteqP; split=>x; [move=>[[_ hx] hn]; exact:hn hx|by case].
  rewrite /measure_almost_included hEmpty; exact:measure_empty (@hausdorff_measure_is_measure R [the metricType R of X] m).
have hIEquality:=((@federer_3_2_26 R m n hmn (E `&` B) hPartRect).2.2.2 t ht).2.
have hPhiSplit:phi E=phi (E `&` B)+phi (E `\` B):=
  borel_regular_borel_measurable hPhi (structure_replacement_borel_regular hLaws) hB E.
have hISplit:I E=I (E `&` B).
  have h:=borel_regular_borel_measurable hI (@integral_geometric_measure_borel_regular R n m hmn t ht) hB E.
  by rewrite /I hNull adde0 in h.
change (I (E `&` B)=H (E `&` B)) in hIEquality.
change (phi E=I E+phi (E `\` B)).
by rewrite hPhiSplit hEquality -hIEquality -hISplit.
Qed.

(** Source for [structure_replacement_rectifiable_integral_geometric]:
    the rectifiable-to-equality direction in Federer 3.3.16,
    p. 299, replacing the corresponding direction of 3.3.13.
    A Borel countably rectifiable enlargement contains the actual
    rectifiable carrier. Its original phi-null omitted subset is
    integral-geometric null by actual projection domination. *)
Lemma structure_replacement_rectifiable_integral_geometric (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))) (t: \bar R):
  is_structure_replacement_measure m phi ->is_measure_m_rectifiable phi m E ->1<=t ->
  phi E=@integral_geometric_measure R n m hmn t E.
Proof.
move=>hLaws [[hPhi [S [hRect hNull]]] hFinite] ht.
have [U [hSU [hU hURect]]]:=countably_rectifiable_borel_enlargement hRect.
have hUNull:phi (E `\` U)=0.
  apply:(@measure_null_subset R _ phi hPhi _ _ _ hNull).
  by move=>x [hx hn]; split=>//; move=>hs; exact:hn (hSU x hs).
have hINull:=@structure_replacement_null_integral_geometric R n m hmn phi (E `\` U) t hLaws hUNull ht.
have hSplit:=@structure_replacement_rectifiable_mass_split R n m hmn phi E U t
  hLaws hFinite ht hU hURect hINull.
by rewrite hUNull adde0 in hSplit.
Qed.
