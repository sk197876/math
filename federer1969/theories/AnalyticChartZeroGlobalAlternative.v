(** Federer (1969), 3.2.33, p. 270: connectedness
    propagates the analytic rank bound over W. This expands
    the corrected appeal to 3.1.24 without assuming a
    global analytic coordinate chart or rank dichotomy. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  NormCoordinateSystemUP EuclideanLebesgueHaar CountableBaseLindelof
  HausdorffMeasure MeasureUP MeasureAlmostBasic AnalyticChartZeroLocusUP
  AnalyticChartZeroLocalAlternative CoordinateRelativeOpenMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_chart_zero_locus_global_alternative]:
    the analytic rank continuation in Federer 3.2.33,
    p. 270, by the corrected reference 3.1.24
    (erratum p. 5, book p. 270 line 25).
    The relative interior of the zero locus is clopen:
    a null coordinate root set cannot meet a nonempty
    relatively open zero piece. Connectedness makes that
    interior all or empty; in the latter case a countable
    open subcover gives global nullity. No finite-mass,
    source measurability or positive-dimension premise is added. *)
Theorem analytic_chart_zero_locus_global_alternative (R:realType) n m
    (W P:set (R_n R n)):
  @is_analytic_chart_zero_locus R n m W P ->
  @connected (inner_metric_space (@euclidean_inner_productP R n)) W ->
  P = W \/@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m P=0%E.
Proof.
move=>hP hConnected.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
pose hH:=@hausdorff_measure_is_measure R X m.
pose Good:set (set X):=[set U:set X|open U /\W `&` U `<=` P].
pose O:set X:=\bigcup_(U in Good) U.
pose I:set X:=W `&` O.
have hO:open O by apply:bigcup_open=>U hU; exact hU.1.
have hIP:I `<=` P.
  move=>x [hx [U hU hxu]]; exact:hU.2 x (conj hx hxu).
have hGerm x:W x ->
    (I x <->exists U:set X,open U /\U x /\W `&` U `<=` P).
  move=>hx; split.
  - move=>[_ [U hU hxu]]; exists U; split; first exact hU.1.
    split; first exact hxu; exact hU.2.
  - move=>[U [hU [hxu hSub]]]; split; first exact hx.
    exists U; last exact hxu; by split.
have hLocalNull x (hx:W x) (hn:~I x):
    exists T:set X,open T /\T x /\H (P `&` T)=0%E.
  have [T [hT [hxT hAlternative]]]:=analytic_chart_zero_locus_local_alternative hP hx.
  exists T; split; first exact hT.
  split; first exact hxT.
  case:hAlternative=>[hAll|hNull]; last exact hNull.
  exfalso; apply:hn; apply:(hGerm x hx).2.
  exists T; by split=>//; split.
have hNullAvoidsInterior (T:set X) (hT:open T) (hNull:H (P `&` T)=0%E):
    forall y,W y ->T y ->~I y.
  move=>y hy hyT hyI.
  have [U [hU [hyU hSub]]]:=(hGerm y hy).1 hyI.
  have [C [V [phi [psi [h [hyC [hConvex [hc hRest]]]]]]]]:=
    analytic_chart_zero_locus_coordinates hP hy.
  have hNotNull:=coordinate_relative_open_nonnull hc (openI hT hU) hy hyC (conj hyT hyU).
  apply:hNotNull.
  apply:(measure_null_subset hH _ hNull)=>z [[hz hzC] [hzT hzU]].
  split; last exact hzT; exact:hSub z (conj hz hzU).
pose Bad:set (set X):=[set T:set X|open T /\forall y,W y ->T y ->~I y].
pose B:set X:=\bigcup_(T in Bad) T.
have hB:open B by apply:bigcup_open=>T hT; exact hT.1.
have hComplement:W `\` I = W `&` B.
  apply/seteqP; split=>x [hx hn].
  - have [T [hT [hxT hNull]]]:=hLocalNull x hx hn.
    split; first exact hx.
    exists T; last exact hxT.
    split; first exact hT.
    exact:hNullAvoidsInterior T hT hNull.
  - split; first exact hx.
    have [T hT hxT]:=hn; exact:hT.2 x hx hxT.
have hRelativeClosed:exists2 C:set X,closed C & I = W `&` C.
  exists (~` B); first exact:open_closedC hB.
  apply/seteqP; split=>x hx.
  - split; first exact hx.1.
    move=>hxB; have hxBad:(W `\` I) x by rewrite hComplement; by split; [exact hx.1|exact hxB].
    exact:hxBad.2 hx.
  - have [hxW hxNoB]:=hx.
    case:(pselect (I x))=>[hi|hn]; first exact hi.
    exfalso; apply:hxNoB.
    have hxBad:(W `\` I) x by split.
    rewrite hComplement in hxBad; exact hxBad.2.
case:(pselect (I!=set0))=>[hNonempty|hEmpty].
- left.
  have hRelativeOpen:exists2 C:set X,open C & I = W `&` C by exists O.
  have hIW:I = W:=hConnected I hNonempty hRelativeOpen hRelativeClosed.
  apply/seteqP; split=>x hx; first exact:(@analytic_chart_zero_locus_subset R n m W P hP x hx).
  apply:hIP; by rewrite hIW.
- right.
  pose Cover:set (set X):=[set T:set X|open T /\H (P `&` T)=0%E].
  have hCover:W `<=` \bigcup_(T in Cover) T.
    move=>x hx.
    have hn:~I x by move=>hi; apply:hEmpty; by exists x.
    have [T [hT [hxT hNull]]]:=hLocalNull x hx hn.
    exists T; last exact hxT; by split.
  have [Base hBase]:=euclidean_countable_open_base R n.
  have [C [hCC [hCount hWC]]]:=@countable_base_open_subcover
    [the topologicalType of X] Base W Cover hBase (fun T hT=>hT.1) hCover.
  have hUnion:=@measure_null_countable_union R X [the choiceType of set X]
    H hH C (fun T=>P `&` T) hCount (fun T hT=>(hCC T hT).2).
  apply:(measure_null_subset hH _ hUnion)=>x hx.
  have [T hT hxT]:=hWC x (analytic_chart_zero_locus_subset hP hx).
  exists T; first exact hT; by split.
Qed.
