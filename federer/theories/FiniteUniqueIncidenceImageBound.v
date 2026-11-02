(** Federer (1969), 3.2.39, p. 275: fine
    source cells meet at most one compact core, so their
    image costs bound the sum of all core image costs. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic FiniteCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_unique_predicate_weight_bound]: supporting
    finite counting of the source cells in the compact-family
    step of Federer 3.2.39, p. 275. Each cell's
    nonnegative image cost is charged at most once. Empty
    index types and infinite costs remain. *)
Lemma finite_unique_predicate_weight_bound (R:realType) (I:finType)
    (P:I->Prop) (w : \bar R):
  0<=w ->(forall i j,P i ->P j ->i=j) ->
  (\sum_i if pselect (P i) is left _ then w else 0)<=w.
Proof.
move=>hw hUnique.
case:(pselect (exists i,P i))=>[[i hi]|hNo].
- rewrite (bigD1 i) //.
  have hHead:(if pselect (P i) is left _ then w else 0)=w.
    by case:pselect=>[h|hn]=>//; exfalso; exact:hn hi.
  rewrite hHead.
  have hRest:(\sum_(j:I|j!=i) if pselect (P j) is left _ then w else 0)=0.
    apply:big1=>j hji; case:pselect=>[hj|_]; last reflexivity.
    exfalso; have hEq:=hUnique j i hj hi; by move:hji; rewrite hEq eqxx.
  rewrite hRest.
  change (w+0<=w)%E; by rewrite adde0.
- have hAll:(\sum_i if pselect (P i) is left _ then w else 0)=0.
    apply:big1=>i _; case:pselect=>[hi|_]; last reflexivity.
    exfalso; apply:hNo; by exists i.
  by rewrite hAll.
Qed.

(** Source for [finite_unique_incidence_image_cost_bound]:
    supporting compact-core to closed-cell cost comparison in
    Federer 3.2.39, p. 275. Each original core is
    covered by its incident cells. The actual measure covering
    law bounds its image cost, and unique core incidence of
    each cell permits finite summation without duplication.
    No source or image measurability is required. *)
Lemma finite_unique_incidence_image_cost_bound (R:realType) (X:Type) (Y:choiceType)
    (I J:finType) (mu:set Y->\bar R) (f:X->Y) (K:I->set X) (D:J->set X):
  is_measure mu ->(forall i,K i `<=` \bigcup_j D j) ->
  (forall j i k,(D j `&` K i)!=set0 ->(D j `&` K k)!=set0 ->i=k) ->
  (\sum_i mu (f @` K i))<=\sum_j mu (f @` D j).
Proof.
move=>hm hCover hUnique.
pose P i j:Prop:=exists x,D j x /\K i x.
pose w i j:=if pselect (P i j) is left _ then mu (f @` D j) else 0.
have hLocal i:mu (f @` K i)<=\sum_j w i j.
  pose U j:=if pselect (P i j) is left _ then f @` D j else set0.
  have hImage:f @` K i `<=` \bigcup_j U j.
    move=>y [x hx <-]; have [j _ hj]:=hCover i x hx.
    exists j; first exact Logic.I.
    rewrite /U; case:pselect=>[hP|hn].
    + by exists x.
    + exfalso; apply:hn; exists x; by split.
  have h:=@measure_finite_indexed_cover R Y J mu hm _ U hImage.
  apply:le_trans h _; apply:lee_sum=>j _.
  rewrite /U /w; case:pselect=>[hP|hn]; first exact:lexx.
  by rewrite (measure_empty hm).
have hSum:(\sum_i mu (f @` K i))<=\sum_i \sum_j w i j.
  apply:lee_sum=>i _; exact:hLocal i.
apply:le_trans hSum _; rewrite exchange_big.
apply:lee_sum=>j _.
apply:(@finite_unique_predicate_weight_bound R I (fun i=>P i j)
  (mu (f @` D j)) (measure_nonnegative hm _)).
move=>i k hi hk; exact (hUnique j i k hi hk).
Qed.
