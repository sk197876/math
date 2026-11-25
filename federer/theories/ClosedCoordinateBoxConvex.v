(** Federer (1969), 4.1.23, pp. 379–380:
    the last subcase is a closed coordinate box,
    and every simplex produced by the original
    rectangular decomposition has its vertices
    in that box. Convexity keeps each entire
    simplex hull in the original compact. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric InnerConvex ConvexHull EuclideanLebesgueBoxes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_coordinate_box]: the original
    set {x:u_i<=x_i<=v_i for all i}
    in Federer 4.1.23, p. 379.
    This aliases the existing coordinate-box operation;
    no interval construction is hidden here. *)
Definition closed_coordinate_box (R:realType) n
    (a b:R_n R n):set (R_n R n):=
  euclidean_coordinate_box
    (fun i=>[set t:R|a i<=t<=b i]).

(** Source for [closed_coordinate_box_convex]:
    the original closed box is convex,
    supporting the support bound in Federer
    4.1.23, pp. 379–380. Empty
    boxes and empty coordinate families are allowed. *)
Lemma closed_coordinate_box_convex (R:realType) n
    (a b:R_n R n):
  is_inner_convex (closed_coordinate_box a b).
Proof.
move=>x y hx hy t ht ht1 i.
have /andP[hAX hXB]:=hx i.
have /andP[hAY hYB]:=hy i.
change (is_true (a i<=((1-t)*:x+t*:y) i<=b i)).
rewrite !ffunE;apply/andP;split.
- have h0:0<=1-t by lra.
  have h:=lerD (ler_wpM2l h0 hAX) (ler_wpM2l ht hAY).
  have hA:(1-t)*a i+t*a i=a i by ring.
  by rewrite hA in h.
- have h0:0<=1-t by lra.
  have h:=lerD (ler_wpM2l h0 hXB) (ler_wpM2l ht hYB).
  have hB:(1-t)*b i+t*b i=b i by ring.
  by rewrite hB in h.
Qed.

(** Source for [closed_coordinate_box_vertex_hull]:
    all original rectangle corners lie in A,
    so the convex hull of each listed simplex
    lies in A, Federer 4.1.23, p. 380.
    This is the stronger generator condition in
    4.1.22, p. 379; support of a
    cancelling sum alone would not establish it. *)
Lemma closed_coordinate_box_vertex_hull (R:realType) n
    (a b:R_n R n) (I:Type) (v:I->R_n R n):
  (forall i,closed_coordinate_box a b (v i))->
  forall x,convex_hull [set y|exists i,v i=y] x->
    closed_coordinate_box a b x.
Proof.
move=>hv;apply:convex_hull_least.
- by move=>x [i <-];exact:hv.
- exact:closed_coordinate_box_convex.
Qed.
