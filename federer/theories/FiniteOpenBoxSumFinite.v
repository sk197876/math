(** Federer (1969), 3.2.41, printed p. 277, finite-family
    induction: finite unions of bounded boxes and their actual
    sums have finite outer volume. This fact is proved before
    scalar finite-part and subtraction arguments are used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes FiniteDisjointOpenBoxFamilyUP
  FiniteRealEndpointBounds VectorSetSum MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_open_box_sum_finite_volume]: supporting legal
    finite scalar volumes in Federer 3.2.41, p. 277. The original
    sum is contained in an actual bounded closed coordinate box;
    no sum measurability, nonemptiness or finite-volume premise is added. *)
Lemma finite_open_box_sum_finite_volume (R:realType) n (I J:finType)
    (a b:I->R_n R n) (c d:J->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (H:J->set (inner_metric_space (@euclidean_inner_productP R n))):
  is_finite_disjoint_open_box_family a b G ->
  is_finite_disjoint_open_box_family c d H ->
  (@euclidean_lebesgue_measure R n (vector_set_sum (\bigcup_i G i) (\bigcup_j H j)) < +oo)%E.
Proof.
move=> hG hH.
have [l [u [hLU hAB]]]:=@finite_real_endpoint_bounds R [the finType of (I*'I_n)%type]
  (fun p=>a p.1 p.2) (fun p=>b p.1 p.2).
have [l' [u' [hLU' hCD]]]:=@finite_real_endpoint_bounds R [the finType of (J*'I_n)%type]
  (fun p=>c p.1 p.2) (fun p=>d p.1 p.2).
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose Q:set E:=[set z|forall k,(l+l'<=z k<=u+u')%R].
have hSub:vector_set_sum (\bigcup_i G i) (\bigcup_j H j) `<=` Q.
  move=> z /vector_set_sum_membership [x [y [[i _ hi] [[j _ hj] ->]]]] k.
  have /andP[hAx hXb]:=((finite_disjoint_open_box_law hG i).2 x).1 hi k.
  have /andP[hCy hYd]:=((finite_disjoint_open_box_law hH j).2 y).1 hj k.
  have [hLa hBu]:=hAB (i,k); have [hLc hDu]:=hCD (j,k).
  rewrite !ffunE; apply/andP; split; lra.
apply:le_lt_trans (@measure_mono R E (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) _ Q hSub) _.
rewrite /Q (euclidean_closed_box (fun _=>ltW (ltrD hLU hLU'))).
exact:ltry.
Qed.
