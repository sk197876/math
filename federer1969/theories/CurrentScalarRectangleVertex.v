(** Federer (1969), 4.1.11, p. 366: every
    vertex in the rectangular simplex decomposition is
    an original vertex of the parallelepiped. Specify
    corners by their original endpoint coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanOneCoordinate EuclideanBlockCoordinates
  EuclideanCartesianMap OrientedRectangleDomain ScalarSegmentFactors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentScalarRectangleVertex.
Variable R:realType.
Local Notation D := (fun f=>oriented_rectangle_dimension (@scalar_segment_factors R f)).

(** Source for [is_current_scalar_rectangle_vertex]: each
    coordinate is one of its two original endpoints,
    the vertices in Federer 4.1.11, p. 366. *)
Definition is_current_scalar_rectangle_vertex (f:seq (R*R)) (x:R_n R (D f)):Prop:=
  forall i:'I_(D f),x i=(nth (0,0) f (val i)).1 \/
    x i=(nth (0,0) f (val i)).2.
Arguments is_current_scalar_rectangle_vertex f x : clear implicits.

(** Source for [current_scalar_rectangle_empty_vertex]: the
    empty product has its unique R^0 vertex,
    supporting Federer 4.1.11, p. 366. *)
Lemma current_scalar_rectangle_empty_vertex (x:R_n R 0%N):
  is_current_scalar_rectangle_vertex [::] x.
Proof. move=>i;have:=ltn_ord i;by rewrite ltn0. Qed.

(** Source for [current_scalar_rectangle_single_vertex]: the
    two original endpoints are the vertices of one
    scalar factor, supporting Federer 4.1.11, p. 366. *)
Lemma current_scalar_rectangle_single_vertex (a:R*R) (x:R_n R 1%N):
  is_current_scalar_rectangle_vertex [::a] x <->
    x ord0=a.1 \/ x ord0=a.2.
Proof. split=>h;first exact:(h ord0);move=>i;by rewrite (ord1 i). Qed.

(** Source for [current_scalar_rectangle_vertex_split]: an
    original corner has a first endpoint and an
    original tail corner, supporting the induction in
    Federer 4.1.11, p. 366. *)
Lemma current_scalar_rectangle_vertex_split (a b:R*R) t (x:R_n R (D (a::b::t))):
  is_current_scalar_rectangle_vertex (a::b::t) x <->
    ((euclidean_block_split x).1 ord0=a.1 \/ (euclidean_block_split x).1 ord0=a.2) /\
    is_current_scalar_rectangle_vertex (b::t) (euclidean_block_split x).2.
Proof.
split.
- move=>h;split.
  + have hFirst:=h (lshift (D (b::t)) ord0).
    by move:hFirst;rewrite /euclidean_block_split /= ffunE.
  + move=>j;have hLast:=h (rshift 1%N j).
    by move:hLast;rewrite /euclidean_block_split /= ffunE.
- move=>[ha hTail] i;case:(split_ordP i)=>j->.
  + rewrite (ord1 j).
    change (x (lshift (D (b::t)) ord0)=a.1 \/ x (lshift (D (b::t)) ord0)=a.2).
    by move:ha;rewrite /euclidean_block_split /= ffunE.
  + change (x (rshift 1%N j)=(nth (0,0) (b::t) (val j)).1 \/
      x (rshift 1%N j)=(nth (0,0) (b::t) (val j)).2).
    by move:(hTail j);rewrite /euclidean_block_split /= ffunE.
Qed.

(** Source for [current_scalar_rectangle_vertex_join]: either
    endpoint joined to an original tail corner is an
    original corner, supporting Federer 4.1.11, p. 366. *)
Lemma current_scalar_rectangle_vertex_join (a b:R*R) t (s:R) (y:R_n R (D (b::t))):
  (s=a.1 \/ s=a.2)->is_current_scalar_rectangle_vertex (b::t) y->
  is_current_scalar_rectangle_vertex (a::b::t)
    (@euclidean_block_join R 1%N (D (b::t)) (@euclidean_one_embed R s,y)).
Proof.
move=>hs hy;apply/current_scalar_rectangle_vertex_split.
rewrite euclidean_block_joinK;split;last exact:hy.
by rewrite /euclidean_one_embed ffunE.
Qed.
End CurrentScalarRectangleVertex.
