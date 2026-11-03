(** Federer (1969), 3.2.41, printed p. 277, definition of
    G_2 and H_2: retain exactly the original boxes whose right
    coordinate cut is nonempty. The actual intersections form
    a disjoint proper open-box family with the exact cut union. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanOpenCoordinateBoxUP EuclideanOpenBoxCuts EuclideanOpenBoxRightCutBoundary FiniteDisjointOpenBoxFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_open_box_right_cut_family_exists]: supporting
    actual G_2,H_2 in Federer 3.2.41, p. 277. The finite subtype
    retains each original index exactly when t<b_i(k). Every actual
    intersection is proved a proper box; endpoint witnesses remain
    local and no cut-family or measure conclusion is assumed. *)
Lemma finite_open_box_right_cut_family_exists (R:realType) n (I:finType)
    (a b:I->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n))) (k:'I_n) (t:R):
  is_finite_disjoint_open_box_family a b G ->
  exists c:{i:I|t<b i k}->R_n R n,
    is_finite_disjoint_open_box_family c (fun i=>b (val i))
      (fun i=>G (val i) `&` [set x|t<x k]) /\
    (\bigcup_(i:{j:I|t<b j k}) (G (val i) `&` [set x|t<x k]))=
      ((\bigcup_i G i) `&` [set x|t<x k]).
Proof.
move=> hG.
pose J:=[the finType of {i:I|t<b i k}].
pose C(i:J):=G (val i) `&` [set x|t<x k].
have hEndpoint(i:J):exists c:R_n R n,
    is_euclidean_open_coordinate_box c (b (val i)) (C i).
  have hBox:=finite_disjoint_open_box_law hG (val i).
  have hCut:t<b (val i) k:=valP i.
  case:(leP t (a (val i) k))=>[hWhole|hInside].
  - exists (a (val i)); rewrite /C (open_box_right_cut_whole hBox hWhole).
    exact hBox.
  - have [c [_ hc]]:=open_box_right_cut_exists hBox (ltW hInside) hCut.
    by exists c.
have [c hc]:=choice hEndpoint.
exists c; split.
- constructor; first exact hc.
  move=> i j hDifferent x hi hj.
  have hValues:val i!=val j.
    apply/eqP=> he; have hEqual:i=j:=val_inj he.
    by move:hDifferent; rewrite hEqual eqxx.
  exact:(@finite_disjoint_open_box_disjoint_law R n I a b G hG
    (val i) (val j) hValues x hi.1 hj.1).
- apply/seteqP; split.
  + move=> x [i _ [hi hCut]]; split=>//; by exists (val i).
  + move=> x [[i _ hi] hCut].
    have /andP[_ hHigh]:=((finite_disjoint_open_box_law hG i).2 x).1 hi k.
    have hAdmissible:t<b i k:=lt_trans hCut hHigh.
    exists (Sub i hAdmissible:J)=>//; by split.
Qed.
