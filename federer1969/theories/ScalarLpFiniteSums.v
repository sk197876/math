(** Supporting finite-sum bounds for Federer (1969), 2.10.9, p. 175, from
    the triangle inequality of 2.4.12, pp. 86–87. Use total scalar Lp laws
    only; no concrete norm construction is imported. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP TotalScalarLpUP TotalScalarLpClosure TotalScalarLpNormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_lp_finite_sum_bound]: supporting finite
    triangle inequality for the cost-cover proof in Federer
    2.10.9, p. 175, from 2.4.12, pp. 86–87. Both finite
    exponents and infinity are allowed, and an empty sum is zero. *)
Theorem scalar_lp_finite_sum_bound (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (t : \bar R)
    (C : {fset J}) (u : J -> X -> R) :
  1<=t -> (forall j, j \in C -> total_scalar_lp mu t (u j)) ->
  total_scalar_lp mu t (fun x => (\sum_(j <- C) u j x)%R) /\
  total_scalar_lp_norm mu t (fun x => (\sum_(j <- C) u j x)%R)<=
    \sum_(j <- C) total_scalar_lp_norm mu t (u j).
Proof.
move=> ht; elim/fset1U_rect: C=> [|j C hj ih] hu.
- have he : (fun x => (\sum_(j <- fset0) u j x)%R)=(fun _ : X => 0%R).
    by apply: funext=> x; rewrite big_seq_fset0.
  rewrite he big_seq_fset0; split.
  + exact: (@total_scalar_lp_zero R X mu hm t ht).
  + by rewrite (@total_scalar_lp_norm_zero R X mu hm t ht).
- have huj := hu j (fset1U1 j C).
  have huC k : k \in C -> total_scalar_lp mu t (u k).
    move=> hk; apply: hu; by rewrite in_fset1U hk orbT.
  have [hmem hbound] := ih huC.
  have he : (fun x => (\sum_(k <- (j |` C)%fset) u k x)%R)=
      (fun x => (u j x+(\sum_(k <- C) u k x)%R)%R).
    by apply: funext=> x; rewrite big_fsetU1.
  rewrite he big_fsetU1 //; split.
  + exact: (@total_scalar_lp_add R X mu hm t (u j) _ huj hmem).
  + apply: le_trans (@total_scalar_lp_norm_triangle R X mu hm t (u j) _ ht huj.2.1 hmem.2.1) _.
    exact: leeD (lexx _) hbound.
Qed.
