(** Federer (1969), 3.2.38, p. 274: choose one common good
    radius after the pointwise differential and mean limits are proved. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure MeasureContinuityAbove
  ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_measure_increasing_good_sets]: supporting
    the uniform choice of delta and E in Federer 3.2.38, p. 274.
    Increasing measurable good sets with conull union exhaust any
    measurable finite-mass original source. Continuity from above is
    applied only to measurable sets; no false continuity property of
    arbitrary outer-measure subsets is used. *)
Lemma finite_measure_increasing_good_sets (R:realType) (X:choiceType)
    (mu:set X->\bar R) (A:set X) (F:nat->set X) (e:R):
  is_measure mu ->measure_measurable mu A ->(mu A< +oo)%E ->
  (forall j,measure_measurable mu (F j)) ->
  (forall j k,(j<=k)%N ->F j `<=` F k) ->
  mu (A `\` \bigcup_j F j)=0%E ->0<e ->exists j,(mu (A `\` F j)<e%:E)%E.
Proof.
move=>hm hA hFinite hF hMono hNull he.
pose D j:=A `\` F j.
have hMeas j:measure_measurable mu (D j):=measure_measurable_difference hm hA (hF j).
have hDecreasing j k:(j<=k)%N ->D k `<=` D j.
  move=>hjk x [hx hNot]; split=>// hFj; apply:hNot; exact:hMono j k hjk x hFj.
have hFirst:(mu (D 0%N)< +oo)%E.
  exact:le_lt_trans (measure_mono hm (fun x (hx:D 0%N x)=>hx.1)) hFinite.
have hIntersection:(\bigcap_j D j)=A `\` \bigcup_j F j.
  apply/seteqP; split=>x.
  - move=>hx; split; first exact:(hx 0%N Logic.I).1.
    move=>[j _ hj]; exact:(hx j Logic.I).2 hj.
  - move=>[hx hNot] j _; split=>// hj; apply:hNot; by exists j.
have hLimit:=@measure_continuity_above R X mu hm D hMeas hDecreasing hFirst.
rewrite hIntersection hNull in hLimit.
have hPositive:(0<e%:E)%E by rewrite lte_fin.
have [j hj]:=hLimit.2.2 e%:E hPositive.
exists j; exact:hj j (leqnn j).
Qed.
