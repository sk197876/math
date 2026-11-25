(** Federer (1969), 3.3.19, p. 303: the
    original first split exists below every split level,
    has a single actual parent hit, and confines all
    actual split-level hits to that parent's children. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets.
From Federer Require Import EuclideanInnerProduct InnerMetric FactorialDiscScalesSealed
  CircularDiscTreeUP CircularDiscRefinement CircularDiscHitCount CircularDiscFirstSplitUP
  FiniteCellHitMeasureUP FiniteCellHitIndicesLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.
Section Split.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Variable H:nat->{fset E}.
Variable T:set E.

(** Source for [circular_disc_first_split_exists]: actual
    existence of the smallest original splitting level
    below an original split level, 3.3.19,
    p. 303. Natural well-ordering proves existence;
    no first level is supplied as an extra premise. *)
Theorem circular_disc_first_split_exists v:
  (2<=#|` @circular_disc_hit_indices R H v T|)%N ->
  exists j:nat,(j<= v)%N /\is_circular_first_split H T j.
Proof.
move=>hv.
have hExists:exists j:nat,(2<=#|` @circular_disc_hit_indices R H j T|)%N by exists v.
have [j hj hMinimal]:= ex_minnP hExists.
exists j;split;first exact:hMinimal v hv.
split=>//;move=>i hij.
case:(leqP 2 #|` @circular_disc_hit_indices R H i T|)=>[hSplit|hSmall].
- have hBack:= hMinimal i hSplit.
  have hFalse:= leq_ltn_trans hBack hij;by rewrite ltnn in hFalse.
- by move:hSmall;rewrite ltnS.
Qed.

Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_first_split_positive]: the
    auxiliary root cannot be the original first split,
    supporting n>= 4 in 3.3.19, p. 303. *)
Lemma circular_disc_first_split_positive j:is_circular_first_split H T j ->(0<j)%N.
Proof.
case:j=>[|j] hFirst;last by [].
have hSubset:=@finite_cell_hit_indices_subset E E (H 0%N)
  (fun z=>MetricClosedBalls.metric_closed_ball z (rho 0%N)) T.
have hCount:= fsubset_leq_card hSubset.
have hRoot:#|` H 0%N|= 1%N by rewrite (circular_disc_tree_root hH) cardfs1.
rewrite hRoot in hCount.
have hFalse:= leq_trans hFirst.1 hCount;discriminate hFalse.
Qed.

(** Source for [circular_disc_first_split_parent_count]:
    exactly one original parent disc meets T before
    its first splitting level, 3.3.19, p. 303.
    The fine hit count proves nonemptiness; minimality
    supplies the upper count one. *)
Lemma circular_disc_first_split_parent_count j:is_circular_first_split H T j.+1 ->
  #|` @circular_disc_hit_indices R H j T|= 1%N.
Proof.
move=>hFirst.
have hBefore:= hFirst.2 j (ltnSn j).
have hRefinement:=@circular_disc_hit_count_refinement R H hH j T.
case hCard:#|` @circular_disc_hit_indices R H j T| hBefore hRefinement=>[|[|k]] hBefore hRefinement.
- have hFalse:= leq_trans hFirst.1 hRefinement;by move:hFalse;rewrite mul0n.
- exact:erefl.
- by move:hBefore;rewrite !ltnS ltn0.
Qed.

(** Source for [circular_disc_first_split_parent]: an
    actual single original parent disc accounts for
    every actual first-split hit, 3.3.19, p. 303.
    The parent stays existential; it is not a
    globally selected address. *)
Theorem circular_disc_first_split_parent j:is_circular_first_split H T j.+1 ->
  exists z:E,z \in H j /\@circular_disc_hit_indices R H j T=[fset z] /\
    forall w:E,w \in @circular_disc_hit_indices R H j.+1 T ->
      exists k:'I_(j+4),w= circular_disc_child_center z (rho j) k.
Proof.
move=>hFirst.
have hCount:=@circular_disc_first_split_parent_count j hFirst.
have /cardfs1P[z hZ]:(#|` @circular_disc_hit_indices R H j T|== 1)%N by rewrite hCount.
have hzHit:z \in @circular_disc_hit_indices R H j T by rewrite hZ in_fset1 eqxx.
have [hz _]:=(@finite_cell_hit_indices_membership E E (H j)
  (fun a=>MetricClosedBalls.metric_closed_ball a (rho j)) T z).1 hzHit.
exists z;split=>//;split=>//;move=>w hw.
have hRefinement:=(@fsubsetP E _ _ (@circular_disc_hit_refinement_subset R H hH j T)) w hw.
rewrite hZ in hRefinement.
have [a [k [ha hW]]]:=(@circular_disc_refinement_membership R [fset z] (rho j) (j+4)%N w).1 hRefinement.
have hEqual:a= z by move:ha;rewrite in_fset1=>/eqP.
exists k;by rewrite -hEqual.
Qed.
End Split.
