(** Federer (1969), 3.2.41, printed p. 277: the nontrivial
    finite-family induction step. Construct the first cut and its
    strict fraction, realize that fraction in the second family,
    apply induction to the actual smaller unions, then combine
    the genuine separated sum volumes. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions VectorSetSum FiniteDisjointOpenBoxFamilyUP FiniteOpenBoxInductionUP
  FiniteOpenBoxLeftCutFamily FiniteOpenBoxRightCutFamily FiniteOpenBoxNontrivialFraction
  FiniteOpenBoxPrescribedCut FinitePredicateRestrictionCardinality
  FiniteOpenBoxUnionBounds FiniteOpenBoxSumFinite FiniteCoordinateCutRecombination
  EuclideanVolumeRootSum MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_open_box_induction_step]: supporting complete
    nontrivial induction step in Federer 3.2.41, p. 277. The
    only induction argument concerns strictly smaller cardinal sums.
    Every family, cut, fraction, nonempty source and finite scalar
    normalization used in the step is derived from the original data. *)
Theorem finite_open_box_induction_step (R:realType) n (I J:finType)
    (a b:I->R_n R n) (c d:J->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (H:J->set (inner_metric_space (@euclidean_inner_productP R n))):
  (0<n)%N ->
  finite_open_box_smaller_pair_bounds R n (#|I|+#|J|)%N ->
  is_finite_disjoint_open_box_family a b G ->
  is_finite_disjoint_open_box_family c d H ->
  (1<#|I|)%N ->(\bigcup_i G i) !=set0 ->(\bigcup_j H j) !=set0 ->
  euclidean_volume_root_sum_bound (\bigcup_i G i) (\bigcup_j H j).
Proof.
move=> hn hLess hG hH hCard hGNe hHNe.
have [k [t [lambda [hLC [hRC [/andP[hLambda hLambda1] [hAL hAR]]]]]]]:=
  @finite_open_box_nontrivial_fraction R n I a b G hG hCard.
have [y [j0 _ hj0]]:=hHNe.
have [u [hBL hBR]]:=@finite_open_box_prescribed_fraction_cut R n J c d H j0 k lambda
  hH hLambda hLambda1.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose A:set E:=\bigcup_i G i.
pose B:set E:=\bigcup_j H j.
pose AL:=A `&` [set x:E|x k<t].
pose AR:=A `&` [set x:E|t<x k].
pose BL:=B `&` [set x:E|x k<u].
pose BR:=B `&` [set x:E|u<x k].
pose IL:=[the finType of {i:I|a i k<t}].
pose IR:=[the finType of {i:I|t<b i k}].
pose JL:=[the finType of {j:J|c j k<u}].
pose JR:=[the finType of {j:J|u<d j k}].
have [dGL [hGL hUGL]]:=@finite_open_box_left_cut_family_exists R n I a b G k t hG.
have [cGR [hGR hUGR]]:=@finite_open_box_right_cut_family_exists R n I a b G k t hG.
have [dHL [hHL hUHL]]:=@finite_open_box_left_cut_family_exists R n J c d H k u hH.
have [cHR [hHR hUHR]]:=@finite_open_box_right_cut_family_exists R n J c d H k u hH.
have hJLC:(#|JL|<=#|J|)%N:=@finite_predicate_restriction_cardinality J (fun j=>c j k<u).
have hJRC:(#|JR|<=#|J|)%N:=@finite_predicate_restriction_cardinality J (fun j=>u<d j k).
have hSizeL:(#|IL|+#|JL|<#|I|+#|J|)%N.
  have hWeak:(#|IL|+#|JL|<=#|IL|+#|J|)%N:=leq_add (leqnn _) hJLC.
  have hStrict:(#|IL|+#|J|<#|I|+#|J|)%N by rewrite ltn_add2r; exact:(andP hLC).2.
  exact:leq_ltn_trans hWeak hStrict.
have hSizeR:(#|IR|+#|JR|<#|I|+#|J|)%N.
  have hWeak:(#|IR|+#|JR|<=#|IR|+#|J|)%N:=leq_add (leqnn _) hJRC.
  have hStrict:(#|IR|+#|J|<#|I|+#|J|)%N by rewrite ltn_add2r; exact:(andP hRC).2.
  exact:leq_ltn_trans hWeak hStrict.
have hm:=euclidean_lebesgue_is_measure R n.
have hAF:(mu A < +oo)%E:=finite_open_box_union_finite_volume hG.
have hBF:(mu B < +oo)%E:=finite_open_box_union_finite_volume hH.
have hCF:(mu (vector_set_sum A B) < +oo)%E:=finite_open_box_sum_finite_volume hG hH.
have hAPos:(0<mu A)%E:=finite_open_box_union_positive_volume hG hGNe.
have hBPos:(0<mu B)%E:=finite_open_box_union_positive_volume hH hHNe.
have hAFn:mu A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm A)); exact hAF.
have hBFn:mu B \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm B)); exact hBF.
have hMA:mu A=(fine (mu A))%:E by rewrite fineK.
have hMB:mu B=(fine (mu B))%:E by rewrite fineK.
have ha:(0<fine (mu A))%R by rewrite hMA lte_fin in hAPos.
have hb:(0<fine (mu B))%R by rewrite hMB lte_fin in hBPos.
change (mu AL=(lambda*fine (mu A))%:E) in hAL.
change (mu AR=((1-lambda)*fine (mu A))%:E) in hAR.
change (mu BL=(lambda*fine (mu B))%:E) in hBL.
change (mu BR=((1-lambda)*fine (mu B))%:E) in hBR.
have hComplement:(0<1-lambda)%R by rewrite subr_gt0.
have hALPos:(0<mu AL)%E by rewrite hAL lte_fin; exact:mulr_gt0 hLambda ha.
have hARPos:(0<mu AR)%E by rewrite hAR lte_fin; exact:mulr_gt0 hComplement ha.
have hBLPos:(0<mu BL)%E by rewrite hBL lte_fin; exact:mulr_gt0 hLambda hb.
have hBRPos:(0<mu BR)%E by rewrite hBR lte_fin; exact:mulr_gt0 hComplement hb.
have hALNe:AL !=set0:=@positive_measure_set_nonempty R E mu AL hm hALPos.
have hARNe:AR !=set0:=@positive_measure_set_nonempty R E mu AR hm hARPos.
have hBLNe:BL !=set0:=@positive_measure_set_nonempty R E mu BL hm hBLPos.
have hBRNe:BR !=set0:=@positive_measure_set_nonempty R E mu BR hm hBRPos.
have hGLNe:(\bigcup_(i:IL) (G (val i) `&` [set x|x k<t])) !=set0 by rewrite hUGL.
have hGRNe:(\bigcup_(i:IR) (G (val i) `&` [set x|t<x k])) !=set0 by rewrite hUGR.
have hHLNe:(\bigcup_(j:JL) (H (val j) `&` [set x|x k<u])) !=set0 by rewrite hUHL.
have hHRNe:(\bigcup_(j:JR) (H (val j) `&` [set x|u<x k])) !=set0 by rewrite hUHR.
have hOne:=hLess IL JL (fun i=>a (val i)) dGL (fun j=>c (val j)) dHL
  (fun i=>G (val i) `&` [set x|x k<t]) (fun j=>H (val j) `&` [set x|x k<u])
  hSizeL hGL hHL hGLNe hHLNe.
have hTwo:=hLess IR JR cGR (fun i=>b (val i)) cHR (fun j=>d (val j))
  (fun i=>G (val i) `&` [set x|t<x k]) (fun j=>H (val j) `&` [set x|u<x k])
  hSizeR hGR hHR hGRNe hHRNe.
rewrite hUGL hUHL in hOne; rewrite hUGR hUHR in hTwo.
exact:(@finite_coordinate_cut_root_recombination R n A B k t u lambda hn
  hAF hBF hCF (ltW hLambda) (ltW hLambda1) hAL hAR hBL hBR hOne hTwo).
Qed.
