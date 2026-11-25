(** Federer (1969), 3.2.38, p. 275: sum pointwise Jacobian
    estimates over closed good cubes and retain the mass outside the core. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure MeasureAlmostBasic
  FiniteNullOverlapAdditivity FiniteCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_core_weighted_measure_bound]: supporting the
    finite good-cube sum in Federer 3.2.38, p. 275, in the
    compact Lusin-core proof. Pairwise null faces allow exact sums
    for both Lebesgue and Jacobian measures. The core-cell integral
    comparison controls its actual mass; a uniform upper Jacobian
    bound controls the remaining cube mass. No measurable inverse,
    disjoint boundary deletion or null difference for a nonmeasurable
    hull is assumed. Empty families and infinite integral values remain. *)
Lemma finite_core_weighted_measure_bound (R:realType) (X:choiceType) (I:finType)
    (mu nu:set X->\bar R) (Q:I->set X) (E:set X) (c:I->R) (e M:R):
  is_measure mu ->is_measure nu ->measure_measurable mu E ->measure_measurable nu E ->
  (forall i,measure_measurable mu (Q i)) ->(forall i,measure_measurable nu (Q i)) ->
  (forall i j,i!=j ->mu (Q i `&` Q j)=0) ->
  (forall i j,i!=j ->nu (Q i `&` Q j)=0) ->
  (forall i,(0<=c i<=M)%R) ->(0<=e)%R ->(0<=M)%R ->
  (forall i,(c i)%:E*mu (Q i `&` E)<=nu (Q i `&` E)+e%:E*mu (Q i `&` E)) ->
  (\sum_i (c i)%:E*mu (Q i))<=
    nu E+e%:E*mu E+M%:E*mu ((\bigcup_i Q i) `\` E).
Proof.
move=>hm hn hE hEN hQ hQN hOverlap hOverlapN hc he hM hLocal.
pose A i:=Q i `&` E.
pose B i:=Q i `\` E.
pose D:=\bigcup_i Q i.
have hUnionA:(\bigcup_i A i)=D `&` E.
  apply/seteqP; split=>x.
  - move=>[i _ [hx hxe]]; split=>//; by exists i.
  - move=>[[i _ hx] hxe]; exists i=>//; by split.
have hUnionB:(\bigcup_i B i)=D `\` E.
  apply/seteqP; split=>x.
  - move=>[i _ [hx hnE]]; split=>//; by exists i.
  - move=>[[i _ hx] hnE]; exists i=>//; by split.
have hFiniteSum (rho:set X->\bar R) (hRho:is_measure rho) (P:I->set X):
    (forall i,measure_measurable rho (P i)) ->
    (forall i j,i!=j ->rho (P i `&` P j)=0) ->
    rho (\bigcup_i P i)=\sum_i rho (P i).
  move=>hP hDisjoint.
  have h:=@measure_finite_family_null_overlap_additivity R X I rho hRho P setT
    (@finite_finset I setT) (fun i _=>hP i) (fun i j _ _=>hDisjoint i j).
  by rewrite (@finite_type_nonnegative_sum R I (fun i=>rho (P i))
    (fun i=>measure_nonnegative hRho (P i))) in h.
have hANull i j:i!=j ->mu (A i `&` A j)=0.
  move=>hij; apply:(@measure_null_subset R X mu hm _ (Q i `&` Q j)) _ (hOverlap i j hij).
  by move=>x [[hi _] [hj _]]; split.
have hANullN i j:i!=j ->nu (A i `&` A j)=0.
  move=>hij; apply:(@measure_null_subset R X nu hn _ (Q i `&` Q j)) _ (hOverlapN i j hij).
  by move=>x [[hi _] [hj _]]; split.
have hBNull i j:i!=j ->mu (B i `&` B j)=0.
  move=>hij; apply:(@measure_null_subset R X mu hm _ (Q i `&` Q j)) _ (hOverlap i j hij).
  by move=>x [[hi _] [hj _]]; split.
have hASum:mu (D `&` E)=\sum_i mu (A i).
  rewrite -hUnionA; exact:(@hFiniteSum mu hm A
    (fun i=>@measure_measurable_intersection R X mu hm (Q i) E (hQ i) hE) hANull).
have hANSum:nu (D `&` E)=\sum_i nu (A i).
  rewrite -hUnionA; exact:(@hFiniteSum nu hn A
    (fun i=>@measure_measurable_intersection R X nu hn (Q i) E (hQN i) hEN) hANullN).
have hBSum:mu (D `\` E)=\sum_i mu (B i).
  rewrite -hUnionB; exact:(@hFiniteSum mu hm B
    (fun i=>@measure_measurable_difference R X mu hm (Q i) E (hQ i) hE) hBNull).
have hCell i:(c i)%:E*mu (Q i)<=nu (A i)+e%:E*mu (A i)+M%:E*mu (B i).
  rewrite (hE (Q i)) (ge0_muleDr _ (measure_nonnegative hm _) (measure_nonnegative hm _)).
  apply:leeD (hLocal i) _.
  apply:lee_wpmul2r; first exact:measure_nonnegative hm _.
  rewrite lee_fin; exact:(andP (hc i)).2.
have hSum:(\sum_i (c i)%:E*mu (Q i))<=
    \sum_i (nu (A i)+e%:E*mu (A i)+M%:E*mu (B i)).
  apply:lee_sum=>i _; exact:hCell.
have hESum:(\sum_i e%:E*mu (A i))=e%:E*(\sum_i mu (A i)).
  symmetry; apply:ge0_sume_distrr=>i _; exact:measure_nonnegative hm _.
have hMSum:(\sum_i M%:E*mu (B i))=M%:E*(\sum_i mu (B i)).
  symmetry; apply:ge0_sume_distrr=>i _; exact:measure_nonnegative hm _.
rewrite !big_split hESum hMSum -hASum -hANSum -hBSum in hSum.
apply:le_trans hSum _.
apply:leeD; last exact:lexx.
apply:leeD.
- apply:(@measure_mono R X nu hn)=>x hx; exact:hx.2.
- apply:lee_wpmul2l; first by rewrite lee_fin.
  apply:(@measure_mono R X mu hm)=>x hx; exact:hx.2.
Qed.
