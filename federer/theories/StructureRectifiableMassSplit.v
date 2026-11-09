(** Federer (1969), 3.3.13, p. 298: the literal subsidiary
    mass identity on the ORIGINAL arbitrary finite-Hausdorff-mass source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffMeasure HausdorffClosedCoverAgreement IntegralGeometricMeasure
  RectifiableSetUP RectifiableGeometricMeasureEquality MeasureUP MeasureBasic MeasureAlmostUP
  TopologicalBorel BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_rectifiable_mass_split]: the literal second
    display in Federer 3.3.13, p. 298. Original E need not be measurable;
    the actual Borel rectifiable B and actual null integral-geometric
    remainder give H^m(E)=I_t^m(E)+H^m(E minus B). Actual 3.2.26 acts
    only on the finite original intersection E intersect B. *)
Lemma structure_rectifiable_mass_split (R:realType) n m (hmn:(m<=n)%N)
    (E B:set (inner_metric_space (@euclidean_inner_productP R n))) (t: \bar R):
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  let I:=@integral_geometric_measure R n m hmn t in
  H E< +oo ->1<=t ->borel_set B ->is_countably_m_rectifiable m B ->I (E `\` B)=0 ->
  H E=I E+H (E `\` B).
Proof.
cbn zeta; move=>hFinite ht hBorel hRectifiable hNull.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R [the metricType R of X] m.
pose I:=@integral_geometric_measure R n m hmn t.
have hH:is_measure H:=@hausdorff_measure_is_measure R [the metricType R of X] m.
have hI:is_measure I:=@integral_geometric_measure_is_measure R n m hmn t ht.
have hHB:=borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R [the metricType R of X] m) hBorel.
have hIB:=borel_regular_borel_measurable hI (@integral_geometric_measure_borel_regular R n m hmn t ht) hBorel.
have hPartFinite:H (E `&` B)< +oo.
  apply:le_lt_trans _ hFinite; apply:(@measure_mono R _ H hH)=>x [hx _]; exact:hx.
have hPartRectifiable:is_measure_m_rectifiable H m (E `&` B).
  split; last exact:hPartFinite.
  split; first exact:hH.
  exists B; split; first exact:hRectifiable.
  have hEmpty:(E `&` B) `\` B=set0.
    apply/seteqP; split; [by move=>x [[_ hx] hn]; exact:hn hx|by move=>x []].
  rewrite /measure_almost_included hEmpty; exact:measure_empty hH.
have hAgreement:=((@federer_3_2_26 R m n hmn (E `&` B) hPartRectifiable).2.2.2 t ht).2.
have hHSplit:=hHB E.
have hISplit:=hIB E; rewrite /I hNull adde0 in hISplit.
rewrite /H in hHSplit.
by rewrite hHSplit -hAgreement -hISplit.
Qed.
