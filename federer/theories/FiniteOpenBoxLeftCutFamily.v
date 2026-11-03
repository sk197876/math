(** Federer (1969), 3.2.41, printed p. 277, definition of
    G_1 and H_1: retain exactly the original boxes whose left
    coordinate cut is nonempty. The actual intersections form
    a disjoint proper open-box family with the exact cut union. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanOpenCoordinateBoxUP EuclideanOpenBoxCuts FiniteDisjointOpenBoxFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_open_box_left_cut_family_exists]: supporting
    actual G_1,H_1 in Federer 3.2.41, p. 277. The finite subtype
    retains each original index exactly when a_i(k)<t. Every actual
    intersection is proved a proper box; endpoint witnesses remain
    local and no cut-family or measure conclusion is assumed. *)
Lemma finite_open_box_left_cut_family_exists (R:realType) n (I:finType)
    (a b:I->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n))) (k:'I_n) (t:R):
  is_finite_disjoint_open_box_family a b G ->
  exists d:{i:I|a i k<t}->R_n R n,
    is_finite_disjoint_open_box_family (fun i=>a (val i)) d
      (fun i=>G (val i) `&` [set x|x k<t]) /\
    (\bigcup_(i:{j:I|a j k<t}) (G (val i) `&` [set x|x k<t]))=
      ((\bigcup_i G i) `&` [set x|x k<t]).
Proof.
move=> hG.
pose J:=[the finType of {i:I|a i k<t}].
pose C(i:J):=G (val i) `&` [set x|x k<t].
have hEndpoint(i:J):exists d:R_n R n,
    is_euclidean_open_coordinate_box (a (val i)) d (C i).
  have hBox:=finite_disjoint_open_box_law hG (val i).
  have hCut:a (val i) k<t:=valP i.
  case:(leP (b (val i) k) t)=>[hWhole|hInside].
  - exists (b (val i)); rewrite /C (open_box_left_cut_whole hBox hWhole).
    exact hBox.
  - have [d [_ hd]]:=open_box_left_cut_exists hBox hCut (ltW hInside).
    by exists d.
have [d hd]:=choice hEndpoint.
exists d; split.
- constructor; first exact hd.
  move=> i j hDifferent x hi hj.
  have hValues:val i!=val j.
    apply/eqP=> he; have hEqual:i=j:=val_inj he.
    by move:hDifferent; rewrite hEqual eqxx.
  exact:(@finite_disjoint_open_box_disjoint_law R n I a b G hG
    (val i) (val j) hValues x hi.1 hj.1).
- apply/seteqP; split.
  + move=> x [i _ [hi hCut]]; split=>//; by exists (val i).
  + move=> x [[i _ hi] hCut].
    have /andP[hLow _]:=((finite_disjoint_open_box_law hG i).2 x).1 hi k.
    have hAdmissible:a i k<t:=lt_trans hLow hCut.
    exists (Sub i hAdmissible:J)=>//; by split.
Qed.
