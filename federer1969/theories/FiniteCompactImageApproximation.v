(** Federer (1969), 3.2.39, p. 275: compact original
    source pieces approximate a finite sum of continuous image costs. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology lra.
From Federer Require Import CompleteMetricUP SuslinSetUP SuslinCompactImageApproximation
  MeasureUP MeasureBasic BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_continuous_compact_image_approximation]:
    supporting the compact-family consequence of 2.10.8 used in
    Federer 3.2.39, p. 275. The earlier Suslin compact-image
    approximation is applied with one divided total error. All
    compact sets lie in their original source pieces. Empty
    finite families are retained; choices remain local. The
    finite target restriction is discharged in the application. *)
Theorem finite_continuous_compact_image_approximation (R:realType)
    (X:metricType R) (Y:topologicalType) (I:finType)
    (mu:set Y->\bar R) (f:X->Y) (S:I->set X) (e:R):
  is_complete_metric_space X ->(exists D:set X,countable D /\dense D) ->
  hausdorff_space Y ->continuous f ->is_measure mu ->is_borel_regular_measure mu ->
  mu setT< +oo ->(forall i,is_suslin_set R (S i)) ->(0<e)%R ->
  exists K:I->set X,(forall i,compact (K i) /\K i `<=` S i) /\
    (\sum_i mu (f @` S i))<=(\sum_i mu (f @` K i))+e%:E.
Proof.
move=>hX hSep hY hf hm hr hFinite hS he.
pose delta:=(e/(#|I|.+1)%:R)%R.
have hCard:(0<((#|I|.+1)%:R:R))%R by rewrite ltr0n.
have hDelta:(0<delta)%R by rewrite /delta divr_gt0.
have hData i:exists K,compact K /\K `<=` S i /\
    mu (f @` S i)-(delta/2)%:E<=mu (f @` K).
  exact:(@finite_measure_suslin_compact_image_approximation R X Y f mu (S i) delta
    hX hSep hY hf hm hr hFinite (hS i) hDelta).
pose K i:=projT1 (cid (hData i)).
have hK i:compact (K i) /\K i `<=` S i /\
    mu (f @` S i)-(delta/2)%:E<=mu (f @` K i):=projT2 (cid (hData i)).
have hFin (T:set X):mu (f @` T) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  exact:le_lt_trans (@measure_mono R Y mu hm _ setT (@subsetT _ _)) hFinite.
pose a i:=fine (mu (f @` S i)).
pose b i:=fine (mu (f @` K i)).
have hA i:mu (f @` S i)=(a i)%:E by rewrite /a fineK.
have hB i:mu (f @` K i)=(b i)%:E by rewrite /b fineK.
have hPoint i:(a i<=b i+delta)%R.
  have h:=(hK i).2.2; rewrite hA hB -EFinB lee_fin in h.
  have hHalf:(delta/2<=delta)%R by rewrite ler_pdivrMr ?ltr0n //; lra.
  lra.
have hSum:(\sum_i a i<=\sum_i b i+(#|I|)%:R*delta)%R.
  have h:(\sum_i a i<=\sum_i (b i+delta))%R.
    apply:ler_sum=>i _; exact:hPoint.
  have hConst:((\sum_(i:I) delta)=(#|I|)%:R*delta)%R.
    rewrite sumr_const cardT; exact:esym (mulr_natl delta _).
  by rewrite big_split hConst in h.
have hError:((#|I|)%:R*delta<=e)%R.
  have hCount:(((#|I|)%:R:R)<=((#|I|.+1)%:R:R))%R by rewrite ler_nat.
  have h:=ler_wpM2r (ltW hDelta) hCount.
  have hEq:((#|I|.+1)%:R*delta=e)%R by rewrite mulrC /delta divfK ?gt_eqF.
  by rewrite hEq in h.
exists K; split; first by move=>i; split; [exact:(hK i).1|exact:(hK i).2.1].
have hASum:(\sum_i mu (f @` S i))=(\sum_i a i)%:E.
  rewrite -sumEFin; apply:eq_bigr=>i _; exact:hA.
have hBSum:(\sum_i mu (f @` K i))=(\sum_i b i)%:E.
  rewrite -sumEFin; apply:eq_bigr=>i _; exact:hB.
rewrite hASum hBSum -EFinD lee_fin.
exact:le_trans hSum (lerD (lexx _) hError).
Qed.
