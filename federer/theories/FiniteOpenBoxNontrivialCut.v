(** Federer (1969), 3.2.41, printed p. 277, induction on
    card(G)+card(H): two disjoint original boxes give a coordinate
    cut with a nonempty, strictly smaller subfamily on each side. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanOpenCoordinateBoxUP EuclideanOpenBoxSeparation FiniteDisjointOpenBoxFamilyUP
  FinitePredicateRestrictionCardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_box_separating_cut_cardinalities]: supporting
    exact strict descent for G_1,G_2 in Federer 3.2.41, p. 277.
    One entire original box lies on each side, so each retained
    index predicate has both an included and an excluded member. *)
Lemma open_box_separating_cut_cardinalities (R:realType) n (I:finType)
    (a b:I->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (k:'I_n) (t:R) (l r:I):
  is_finite_disjoint_open_box_family a b G ->b l k<=t ->t<=a r k ->
  (0<#|{: {i:I|(a i k<t)%R}}|<#|I|)%N /\
    (0<#|{: {i:I|(t<b i k)%R}}|<#|I|)%N.
Proof.
move=> hG hLT hTR.
have hLeft:a l k<t:=lt_le_trans ((finite_disjoint_open_box_law hG l).1 k) hLT.
have hRight:t<b r k:=le_lt_trans hTR ((finite_disjoint_open_box_law hG r).1 k).
have hNotLeft:~~(a r k<t) by rewrite -leNgt.
have hNotRight:~~(t<b l k) by rewrite -leNgt.
split; apply/andP; split.
- exact:(@finite_predicate_restriction_positive_cardinality I (fun i=>a i k<t) l hLeft).
- exact:(@finite_predicate_restriction_strict_cardinality I (fun i=>a i k<t) r hNotLeft).
- exact:(@finite_predicate_restriction_positive_cardinality I (fun i=>t<b i k) r hRight).
- exact:(@finite_predicate_restriction_strict_cardinality I (fun i=>t<b i k) l hNotRight).
Qed.

(** Source for [finite_open_box_nontrivial_coordinate_cut]: supporting
    proved choice of i,a when card(G)>1 in Federer 3.2.41, p. 277.
    The strict cardinal bounds follow from actual disjoint boxes;
    neither cut nonemptiness nor induction descent is assumed. *)
Theorem finite_open_box_nontrivial_coordinate_cut (R:realType) n (I:finType)
    (a b:I->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n))):
  is_finite_disjoint_open_box_family a b G ->(1<#|I|)%N ->
  exists (k:'I_n) (t:R),
    (0<#|{: {i:I|(a i k<t)%R}}|<#|I|)%N /\
      (0<#|{: {i:I|(t<b i k)%R}}|<#|I|)%N.
Proof.
move=> hG hCard.
have [i [j hDifferent]]:=finite_type_two_distinct_members hCard.
have hI:=finite_disjoint_open_box_law hG i.
have hJ:=finite_disjoint_open_box_law hG j.
have hDisjoint x:G i x ->G j x ->False.
  exact:(@finite_disjoint_open_box_disjoint_law R n I a b G hG i j hDifferent x).
have [k [hIJ|hJI]]:=@disjoint_open_boxes_coordinate_separation R n
  (a i) (b i) (a j) (b j) (G i) (G j) hI hJ hDisjoint.
- exists k,(b i k).
  exact:(@open_box_separating_cut_cardinalities R n I a b G k (b i k) i j hG (lexx _) hIJ).
- exists k,(b j k).
  exact:(@open_box_separating_cut_cardinalities R n I a b G k (b j k) j i hG (lexx _) hJI).
Qed.
