(** Federer (1969), 3.2.28(4), p. 267:
    pass the compact-piece area identity to its
    countable increasing union by 2.1.3(4), p. 55. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import MeasureUP MeasureContinuityBelow ExtendedRealOrderLimit
  ExtendedIncreasingLimitSupremum FiniteWeightedTruncationLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_exhaustion_image_identity]: supporting
    countable passage in the general manifold area
    identity, Federer 3.2.28(4), p. 267.
    Only compact pieces must have finite mass in
    its application; infinite union masses are retained. *)
Theorem measure_exhaustion_image_identity (R:realType) (X Y:choiceType)
    (mu:set X->\bar R) (nu:set Y->\bar R) (S:set X)
    (F:X->Y) (K:nat->set X) (c:R):
  is_measure mu ->is_measure nu ->(0<=c)%R ->
  (forall i,measure_measurable mu (K i)) ->
  (forall i,measure_measurable nu (F @` K i)) ->
  (forall i,K i `<=` K i.+1) ->S=\bigcup_i K i ->
  (forall i,mu (K i)=c%:E*nu (F @` K i)) ->
  mu S=c%:E*nu (F @` S).
Proof.
move=>hMu hNu hc hK hFK hInc hCover hValue.
have hAdd i s:K i `<=` K (i+s)%N.
  elim:s=>[|s IH]; first by rewrite addn0.
  rewrite addnS; exact:subset_trans IH (hInc _).
have hMono i j:(i<=j)%N ->K i `<=` K j.
  move=>hij; have h:=hAdd i (j-i)%N; by rewrite (subnKC hij) in h.
have hImageMono i j:(i<=j)%N ->F @` K i `<=` F @` K j.
  move=>hij z [x hx <-]; exists x; first exact:hMono i j hij x hx.
  reflexivity.
have hImageCover:F @` S=\bigcup_i (F @` K i).
  apply/seteqP; split=>y.
  - move=>[x hx <-]; have [i _ hi]:(\bigcup_i K i) x by rewrite -hCover.
    exists i; first exact I; by exists x.
  - move=>[i _ [x hx <-]]; exists x; last reflexivity.
    rewrite hCover; by exists i.
have hLeft:=@measure_continuity_below R X mu hMu K hK hMono.
have hRight:=@measure_continuity_below R Y nu hNu (fun i=>F @` K i) hFK hImageMono.
rewrite -hCover in hLeft.
rewrite -hImageCover in hRight.
have hScaled:=extended_increasing_finite_right_scale hc hRight.
have hSeq:(fun i=>nu (F @` K i)*c%:E)=(fun i=>mu (K i)).
  apply:funext=>i; by rewrite hValue muleC.
rewrite hSeq in hScaled.
rewrite muleC; exact:extended_order_limit_unique hLeft.2 hScaled.2.
Qed.
