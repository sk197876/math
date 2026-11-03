(** Federer (1969), 3.2.41, printed p. 277, finite-family proof:
    the nonempty intersections with strict coordinate halfspaces are
    again members of the original proper open-box family. Endpoint
    replacements serve as local existence witnesses only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanOpenCoordinateBoxUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_box_left_cut_exists]: supporting G_1 and H_1
    in Federer 3.2.41, p. 277. Cutting strictly above the lower
    endpoint and at or below the upper endpoint gives the actual
    proper box with the single upper endpoint replaced. *)
Lemma open_box_left_cut_exists (R:realType) n (a b:R_n R n)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (k:'I_n) (t:R):
  is_euclidean_open_coordinate_box a b A ->a k<t ->t<=b k ->
  exists b':R_n R n,
    (forall i,b' i=if i==k then t else b i) /\
    is_euclidean_open_coordinate_box a b' (A `&` [set x|x k<t]).
Proof.
move=> hA hat htb.
pose b':R_n R n:=[ffun i=>if i==k then t else b i].
exists b'; split; first by move=> i; rewrite /b' ffunE.
split.
- move=> i; rewrite /b' ffunE; case:(eqVneq i k)=>[->|hNe]; first exact hat.
  exact:hA.1.
- move=> x; split.
  + move=> [hx hCut] i; have /andP[hLow hHigh]:=(hA.2 x).1 hx i.
    rewrite /b' ffunE; case:(eqVneq i k)=>[->|hNe].
    * apply/andP; split=>//; exact:(andP ((hA.2 x).1 hx k)).1.
    * by apply/andP; split.
  + move=> hx; split.
    * apply:(hA.2 x).2=> i.
      have hi:=hx i; rewrite /b' ffunE in hi.
      case:(eqVneq i k)=>[->|hNe] in hi *; last exact hi.
      have /andP[hLow hHigh]:=hi; apply/andP; split=>//.
      exact:lt_le_trans hHigh htb.
    * have hi:=hx k; rewrite /b' ffunE eqxx in hi.
      exact:(andP hi).2.
Qed.

(** Source for [open_box_right_cut_exists]: supporting G_2 and H_2
    in Federer 3.2.41, p. 277. Cutting at or above the lower
    endpoint and strictly below the upper endpoint replaces the
    one lower endpoint and retains the original upper bounds. *)
Lemma open_box_right_cut_exists (R:realType) n (a b:R_n R n)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (k:'I_n) (t:R):
  is_euclidean_open_coordinate_box a b A ->a k<=t ->t<b k ->
  exists a':R_n R n,
    (forall i,a' i=if i==k then t else a i) /\
    is_euclidean_open_coordinate_box a' b (A `&` [set x|t<x k]).
Proof.
move=> hA hat htb.
pose a':R_n R n:=[ffun i=>if i==k then t else a i].
exists a'; split; first by move=> i; rewrite /a' ffunE.
split.
- move=> i; rewrite /a' ffunE; case:(eqVneq i k)=>[->|hNe]; first exact htb.
  exact:hA.1.
- move=> x; split.
  + move=> [hx hCut] i; have /andP[hLow hHigh]:=(hA.2 x).1 hx i.
    rewrite /a' ffunE; case:(eqVneq i k)=>[->|hNe].
    * apply/andP; split=>//; exact:(andP ((hA.2 x).1 hx k)).2.
    * by apply/andP; split.
  + move=> hx; split.
    * apply:(hA.2 x).2=> i.
      have hi:=hx i; rewrite /a' ffunE in hi.
      case:(eqVneq i k)=>[->|hNe] in hi *; last exact hi.
      have /andP[hLow hHigh]:=hi; apply/andP; split=>//.
      exact:le_lt_trans hat hLow.
    * have hi:=hx k; rewrite /a' ffunE eqxx in hi.
      exact:(andP hi).1.
Qed.

(** Source for [open_box_left_cut_empty]: supporting deletion of
    empty cut members in G_1,H_1 in Federer 3.2.41, p. 277. *)
Lemma open_box_left_cut_empty (R:realType) n (a b:R_n R n)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (k:'I_n) (t:R):
  is_euclidean_open_coordinate_box a b A ->t<=a k ->
  A `&` [set x|x k<t]=set0.
Proof.
move=> hA hta; apply/seteqP; split; last by move=> x [].
move=> x [hx hCut]; have /andP[hLow _]:=(hA.2 x).1 hx k.
exfalso; have hBad:=lt_trans (le_lt_trans hta hLow) hCut; by rewrite ltxx in hBad.
Qed.

(** Source for [open_box_left_cut_whole]: supporting unchanged
    members of G_1,H_1 in Federer 3.2.41, p. 277. Open endpoints
    permit equality of the cut and the original upper endpoint. *)
Lemma open_box_left_cut_whole (R:realType) n (a b:R_n R n)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (k:'I_n) (t:R):
  is_euclidean_open_coordinate_box a b A ->b k<=t ->
  A `&` [set x|x k<t]=A.
Proof.
move=> hA hbt; apply/seteqP; split=> x hx; first exact hx.1.
split=>//; have /andP[_ hHigh]:=(hA.2 x).1 hx k.
exact:lt_le_trans hHigh hbt.
Qed.
