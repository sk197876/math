(** Federer (1969), 3.2.32, p. 270: supporting
    exact target summation over disjoint Borel pieces.
    Infinite fibre masses are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [disjoint_nonnegative_target_series]: supporting the
    limit in Federer 3.2.32, p. 270. A nonnegative
    function supported on a disjoint countable union is exactly
    the sum of its restrictions, with zero outside each piece.
    This is an algebraic consequence of the existing sum laws,
    without a measurability or finite-value assumption. *)
Lemma disjoint_nonnegative_target_series (R:realType) (X:Type)
    (D:nat->set X) (f:X->extended_real_line R):
  (forall x,0<=f x) ->
  (forall i j,i!=j ->forall x,D i x ->D j x ->False) ->
  (forall x,~(\bigcup_i D i) x ->f x=0) ->forall x,
  nonnegative_sum setT (fun i=>if pselect (D i x) then f x else 0)=f x.
Proof.
move=>hPos hDisj hOff x.
have [hIn|hIn]:=pselect ((\bigcup_i D i) x).
- have [i _ hi]:=hIn.
  have hAt:(if pselect (D i x) then f x else 0)=f x.
    by case:pselect=>// hNot; exfalso; exact:hNot hi.
  have hSum:nonnegative_sum setT (fun j=>if pselect (D j x) then f x else 0)=
      (if pselect (D i x) then f x else 0).
    apply:(@nonnegative_sum_single_support R [the choiceType of (nat:Type)] setT
      (fun j=>if pselect (D j x) then f x else 0) i Logic.I).
    + rewrite hAt; exact:hPos.
    + move=>j _ hji; case:pselect=>// hj; exfalso; exact:(hDisj j i hji x hj hi).
  by rewrite hSum hAt.
- rewrite (hOff x hIn); apply:nonnegative_sum_zero=>i _.
  case:pselect=>// hi; exfalso; apply:hIn; by exists i.
Qed.
