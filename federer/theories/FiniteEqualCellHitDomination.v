(** Federer (1969), 3.3.20, p. 308:
    the original equal cell masses are dominated by literal hit counts. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP FiniteCoverMeasureBounds
  FiniteCellHitMeasureUP FiniteCellHitIndicesLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_equal_cell_hit_domination]: supporting
    passage from the actual level-square hit measures
    to the original product restriction in 3.3.20,
    p. 308. A finite cover by actual
    hit cells and their proved mass bounds suffice;
    the original test set need not be measurable. *)
Theorem finite_equal_cell_hit_domination (R:realType) (I X:choiceType)
    (F:{fset I}) (S:I->set X) (w:R) (nu psi:set X->\bar R) (E:set X):
  is_measure nu ->is_finite_cell_hit_measure F S w psi ->
  (forall T,nu T=nu (T `&` E)) ->
  (forall x,E x ->exists i,i \in F /\S i x) ->
  (forall i,i \in F ->(nu (S i)<=w%:E)%E) ->
  forall T,(nu T<=psi T)%E.
Proof.
move=>hNu hPsi hSupport hCover hCell T.
pose H:=finite_cell_hit_indices F S T.
pose J:=[the finType of (H:Type)].
have hCoverT:T `&` E `<=` \bigcup_(i in @setT J) S (val i).
  move=>x [hxT hxE].
  have [i [hi hxS]]:=hCover x hxE.
  have hHit:i \in H.
    apply/finite_cell_hit_indices_membership;split=>//;exists x;by split.
  exists (Sub i hHit);by [].
have hBound:=@measure_finite_indexed_cover R X J nu hNu (T `&` E)
  (fun i=>S (val i)) hCoverT.
have hSum:(\sum_(i:J) nu (S (val i))<=\sum_(i:J) w%:E)%E.
  apply:lee_sum=>i _;apply:hCell.
  have hHit:val i \in H:=valP i.
  move:hHit=>/finite_cell_hit_indices_membership[hi _];exact:hi.
rewrite (hSupport T) hPsi.
apply:le_trans hBound (le_trans hSum _).
by rewrite sumEFin sumr_const cardT -cardE /J -cardfE mulr_natl.
Qed.
