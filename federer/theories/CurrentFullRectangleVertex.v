(** Federer (1969), 4.1.11, p. 366: original
    vertices of a finite rectangular product with
    independent Euclidean factor dimensions. Each factor
    contributes one of its two original endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanBlockCoordinates OrientedSegmentFactor
  OrientedRectangleDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section CurrentFullRectangleVertex.
Variable R:realType.
Local Notation Factor := (oriented_segment_factor R).
Local Notation D := (@oriented_rectangle_dimension R).

(** Source for [current_full_rectangle_vertex_step]: a single
    factor contributes an endpoint; attaching a factor
    retains an original tail vertex, supporting Federer
    4.1.11, p. 366. This specifies a geometric
    property, not a selected vertex family. *)
Definition current_full_rectangle_vertex_step (a:Factor) (t:seq Factor):
    (R_n R (D t)->Prop)->R_n R (D (a::t))->Prop:=
  match t as q return (R_n R (D q)->Prop)->R_n R (D (a::q))->Prop with
  |[::]=>fun _ x=>x=oriented_segment_factor_start a \/ x=oriented_segment_factor_end a
  |b::s=>fun P x=>
    ((euclidean_block_split x).1=oriented_segment_factor_start a \/
     (euclidean_block_split x).1=oriented_segment_factor_end a) /\ P (euclidean_block_split x).2
  end.

(** Source for [is_current_full_rectangle_vertex]: each original
    coordinate block is one of its factor endpoints,
    the original rectangle vertices in Federer 4.1.11,
    p. 366. The unique empty-product vertex is included. *)
Fixpoint is_current_full_rectangle_vertex (f:seq Factor):R_n R (D f)->Prop:=
  match f as q return R_n R (D q)->Prop with
  |[::]=>fun _=>True
  |a::t=>@current_full_rectangle_vertex_step a t (@is_current_full_rectangle_vertex t)
  end.
Arguments is_current_full_rectangle_vertex f x : clear implicits.

(** Source for [current_full_rectangle_empty_vertex]: the original
    empty rectangle has its unique R^0 vertex, supporting
    Federer 4.1.11, p. 366. *)
Lemma current_full_rectangle_empty_vertex (x:R_n R 0%N):
  is_current_full_rectangle_vertex [::] x.
Proof. exact:Logic.I. Qed.

(** Source for [current_full_rectangle_single_vertex]: the original
    single-factor vertices are exactly its two endpoints,
    supporting Federer 4.1.11, p. 366. *)
Lemma current_full_rectangle_single_vertex (a:Factor) x:
  is_current_full_rectangle_vertex [::a] x <->
    x=oriented_segment_factor_start a \/ x=oriented_segment_factor_end a.
Proof. by []. Qed.

(** Source for [current_full_rectangle_vertex_join]: either original
    first endpoint combined with an original tail vertex
    is an original product vertex, supporting Federer
    4.1.11, p. 366. Every factor dimension is retained. *)
Lemma current_full_rectangle_vertex_join (a b:Factor) t
    (x:R_n R (oriented_segment_factor_dimension a)) (y:R_n R (D (b::t))):
  (x=oriented_segment_factor_start a \/ x=oriented_segment_factor_end a)->
  is_current_full_rectangle_vertex (b::t) y->
  is_current_full_rectangle_vertex (a::b::t)
    (@euclidean_block_join R (oriented_segment_factor_dimension a) (D (b::t)) (x,y)).
Proof.
move=>hx hy.
change (((euclidean_block_split (euclidean_block_join (x,y))).1=oriented_segment_factor_start a \/
  (euclidean_block_split (euclidean_block_join (x,y))).1=oriented_segment_factor_end a) /\
  is_current_full_rectangle_vertex (b::t) (euclidean_block_split (euclidean_block_join (x,y))).2).
by rewrite euclidean_block_joinK;split.
Qed.
End CurrentFullRectangleVertex.
