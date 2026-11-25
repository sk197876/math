(** Federer (1969), 3.3.13, pp. 297–298: the complete original
    theorem, every exponent and both directions of the equality criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffMeasure IntegralGeometricMeasure
  StructureHausdorffPureDecomposition StructureRectifiableMassSplit
  RectifiableSetUP RectifiableGeometricMeasureEquality MeasureUP MeasureBasic MeasureAlmostUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_3_13]: COMPLETE Federer 3.3.13, pp. 297–298.
    Original arbitrary E of finite H^m outer mass has an original pure
    remainder of I_t^m mass zero after removing a Borel countably
    m rectifiable part. Moreover actual H^m(E)=I_t^m(E) if and only
    if original E is (H^m,m) rectifiable. Retain every natural
    0<=m<=n, every exponent 1<=t<=infinity, and original nonmeasurable
    sources. All actual projection, decomposition, mass splitting
    and finite cancellation premises are proved. *)
Theorem federer_3_3_13 (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))) (t: \bar R):
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  let I:=@integral_geometric_measure R n m hmn t in
  H E< +oo ->1<=t ->
  (exists B,borel_set B /\is_countably_m_rectifiable m B /\
    is_purely_measure_m_unrectifiable H m (E `\` B) /\I (E `\` B)=0) /\
  (H E=I E <->is_measure_m_rectifiable H m E).
Proof.
cbn zeta; move=>hFinite ht.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R [the metricType R of X] m.
pose I:=@integral_geometric_measure R n m hmn t.
have hH:is_measure H:=@hausdorff_measure_is_measure R [the metricType R of X] m.
have [B [hBorel [hRectifiable [hPure hNullAll]]]]:=
  @structure_hausdorff_pure_decomposition R n m hmn E hFinite.
have hNull:I (E `\` B)=0:=hNullAll t ht.
split; first by exists B; split=>//; split=>//; split.
split.
- move=>hEqual.
  have hSplit:=@structure_rectifiable_mass_split R n m hmn E B t hFinite ht hBorel hRectifiable hNull.
  rewrite -hEqual in hSplit.
  change (H E=H E+H (E `\` B)) in hSplit.
  have hRemainderFinite:H (E `\` B)< +oo.
    apply:le_lt_trans _ hFinite; apply:(@measure_mono R _ H hH)=>x [hx _]; exact:hx.
  have hEFin:H E \is a fin_num.
    by rewrite (ge0_fin_numE (@measure_nonnegative R [the choiceType of X] H hH E)).
  have hAFin:H (E `\` B) \is a fin_num.
    by rewrite (ge0_fin_numE (@measure_nonnegative R [the choiceType of X] H hH (E `\` B))).
  have hEValue:H E=(fine (H E))%:E by rewrite fineK.
  have hAValue:H (E `\` B)=(fine (H (E `\` B)))%:E by rewrite fineK.
  rewrite hEValue hAValue -EFinD in hSplit.
  have hReal:fine (H E)=(fine (H E)+fine (H (E `\` B)))%R:=EFin_inj hSplit.
  have hCancel:=congr1 (fun z:R=>(z-fine (H E))%R) hReal.
  rewrite subrr addrAC subrr add0r in hCancel.
  have hZero:H (E `\` B)=0 by rewrite hAValue -hCancel.
  split; last exact:hFinite.
  split; first exact:hH.
  exists B; by split.
- move=>hRect.
  exact:esym (((@federer_3_2_26 R m n hmn E hRect).2.2.2 t ht).2).
Qed.
