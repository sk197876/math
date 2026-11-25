(** Federer (1969), 3.2.41, printed p. 277, last displayed
    finite-family induction step. This supporting lemma combines
    the actual separated sum sets and proportional cut masses.
    Finiteness is a premise here and is separately proved for the
    bounded box unions; it is not a premise of the numbered theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  VectorSetSum VectorSumCoordinateCuts CoordinateSeparatedVolumeLower
  EuclideanVolumeRootSum ExtendedPositivePower ProportionalRootRecombination
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_coordinate_cut_root_recombination]: supporting
    actual induction recombination in Federer 3.2.41, p. 277.
    The smaller-pair inequalities are induction arguments, and all
    four displayed mass laws concern the original strict cuts.
    Every scalar finite part is justified; no sum measurability
    or false additivity of arbitrary disjoint outer sets is used. *)
Lemma finite_coordinate_cut_root_recombination (R:realType) n
    (A B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (k:'I_n) (t u lambda:R):
  (0<n)%N ->
  (@euclidean_lebesgue_measure R n A < +oo)%E ->
  (@euclidean_lebesgue_measure R n B < +oo)%E ->
  (@euclidean_lebesgue_measure R n (vector_set_sum A B) < +oo)%E ->
  0<=lambda ->lambda<=1 ->
  @euclidean_lebesgue_measure R n (A `&` [set x|x k<t])=
    (lambda*fine (@euclidean_lebesgue_measure R n A))%:E ->
  @euclidean_lebesgue_measure R n (A `&` [set x|t<x k])=
    ((1-lambda)*fine (@euclidean_lebesgue_measure R n A))%:E ->
  @euclidean_lebesgue_measure R n (B `&` [set x|x k<u])=
    (lambda*fine (@euclidean_lebesgue_measure R n B))%:E ->
  @euclidean_lebesgue_measure R n (B `&` [set x|u<x k])=
    ((1-lambda)*fine (@euclidean_lebesgue_measure R n B))%:E ->
  euclidean_volume_root_sum_bound (A `&` [set x|x k<t]) (B `&` [set x|x k<u]) ->
  euclidean_volume_root_sum_bound (A `&` [set x|t<x k]) (B `&` [set x|u<x k]) ->
  euclidean_volume_root_sum_bound A B.
Proof.
move=> hn hAF hBF hCF hLambda hLambda1 hAL hAR hBL hBR hOne hTwo.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose C:=vector_set_sum A B.
pose AL:=A `&` [set x:E|x k<t].
pose AR:=A `&` [set x:E|t<x k].
pose BL:=B `&` [set x:E|x k<u].
pose BR:=B `&` [set x:E|u<x k].
pose P:=vector_set_sum AL BL.
pose Q:=vector_set_sum AR BR.
have hm:=euclidean_lebesgue_is_measure R n.
have hCutsL:=@vector_sum_lower_coordinate_cuts R n A B k t u.
have hCutsR:=@vector_sum_upper_coordinate_cuts R n A B k t u.
have hPC:P `<=` C by move=> x hx; exact:(hCutsL x hx).1.
have hQC:Q `<=` C by move=> x hx; exact:(hCutsR x hx).1.
have hPF:(mu P < +oo)%E:=le_lt_trans (@measure_mono R E mu hm P C hPC) hCF.
have hQF:(mu Q < +oo)%E:=le_lt_trans (@measure_mono R E mu hm Q C hQC) hCF.
have hValue (S:set E):(mu S < +oo)%E ->mu S=(fine (mu S))%:E.
  move=> hSF; have hFinite:mu S \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative hm S)); exact hSF.
  by rewrite fineK.
have hSign (S:set E):(mu S < +oo)%E ->(0<=fine (mu S))%R.
  move=> hSF; have h:=measure_nonnegative hm S.
  change (is_true (0<=mu S)%E) in h.
  by rewrite (hValue S hSF) lee_fin in h.
pose p:R:=n%:R.
pose a:R:=fine (mu A).
pose b:R:=fine (mu B).
pose c:R:=fine (mu C).
pose c1:R:=fine (mu P).
pose c2:R:=fine (mu Q).
have hp:0<p by rewrite /p ltr0n.
have hMA:mu A=a%:E:=hValue A hAF.
have hMB:mu B=b%:E:=hValue B hBF.
have hMC:mu C=c%:E:=hValue C hCF.
have hMP:mu P=c1%:E:=hValue P hPF.
have hMQ:mu Q=c2%:E:=hValue Q hQF.
change (mu AL=(lambda*a)%:E) in hAL.
change (mu AR=((1-lambda)*a)%:E) in hAR.
change (mu BL=(lambda*b)%:E) in hBL.
change (mu BR=((1-lambda)*b)%:E) in hBR.
have hSum:=@coordinate_separated_volume_lower R n k (t+u) C P Q hPC hQC
  (fun x hx=>(hCutsL x hx).2) (fun x hx=>(hCutsR x hx).2).
change (is_true (mu P+mu Q<=mu C)%E) in hSum.
rewrite hMP hMQ hMC -EFinD lee_fin in hSum.
change (is_true (extended_positive_power (mu AL) p^-1+
  extended_positive_power (mu BL) p^-1<=extended_positive_power (mu P) p^-1)%E) in hOne.
change (is_true (extended_positive_power (mu AR) p^-1+
  extended_positive_power (mu BR) p^-1<=extended_positive_power (mu Q) p^-1)%E) in hTwo.
rewrite hAL hBL hMP /extended_positive_power -EFinD lee_fin in hOne.
rewrite hAR hBR hMQ /extended_positive_power -EFinD lee_fin in hTwo.
change (is_true (extended_positive_power (mu A) p^-1+
  extended_positive_power (mu B) p^-1<=extended_positive_power (mu C) p^-1)%E).
rewrite hMA hMB hMC /extended_positive_power -EFinD lee_fin.
exact:(@proportional_two_piece_root_recombination R p a b c c1 c2 lambda hp
  (hSign A hAF) (hSign B hBF) (hSign P hPF) (hSign Q hQF)
  hLambda hLambda1 hSum hOne hTwo).
Qed.
