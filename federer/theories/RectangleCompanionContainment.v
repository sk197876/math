(** Boundary containment for the rectangle construction supporting
    Federer (1969), 2.8.20, p. 152; Saks1934
    Lemma B, p. 258. Closed eligible companions stay
    in the closed parent whenever the positive half-open cells
    stay in its half-open version. This elementary endpoint fact
    ensures small covering rectangles. Source titles:
    VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import ScalarPlaneRectangles ScalarHalfOpenRectangles BohrPatchUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectangle_companion_parent_inclusion]: supporting
    preservation of the closed parent bound for the eligible
    rectangles in Federer 2.8.20, p. 152.
    Positivity supplies the lower corner, and a putative upper
    endpoint beyond the parent would put a parent boundary
    point inside the half-open cell, a contradiction. *)
Lemma rectangle_companion_parent_inclusion (R : realType)
    (H K : set (R*R)) (a b c d : R) :
  are_rectangle_companions H K -> H `<=` scalar_half_open_rectangle a b c d ->
  K `<=` scalar_closed_rectangle a b c d.
Proof.
move=> [u [v [w [z [huv [hwz [-> ->]]]]]]] hsub.
have hbase : scalar_half_open_rectangle u v w z (u,w).
  by rewrite /scalar_half_open_rectangle /= !in_itv /= !lexx huv hwz.
have hb := hsub (u,w) hbase.
move: hb; rewrite /scalar_half_open_rectangle /= !in_itv /=.
move=> [/andP [hau hub] /andP [hcw hwd]].
have hvb : v<=b.
  case: (leP v b)=> // hbv; exfalso.
  have hcell : scalar_half_open_rectangle u v w z (b,w).
    rewrite /scalar_half_open_rectangle /= !in_itv /=; split; apply/andP; split=> //; lra.
  have hh := (hsub (b,w) hcell).1.
  have hbfalse : (b<b)%R := (andP hh).2.
  by rewrite ltxx in hbfalse.
have hzd : z<=d.
  case: (leP z d)=> // hdz; exfalso.
  have hcell : scalar_half_open_rectangle u v w z (u,d).
    rewrite /scalar_half_open_rectangle /= !in_itv /=; split; apply/andP; split=> //; lra.
  have hh := (hsub (u,d) hcell).2.
  have hdfalse : (d<d)%R := (andP hh).2.
  by rewrite ltxx in hdfalse.
move=> [x y]; rewrite /scalar_closed_rectangle /= !in_itv /=.
move=> [/andP [hux hxv] /andP [hwy hyz]]; split; apply/andP; split; lra.
Qed.
