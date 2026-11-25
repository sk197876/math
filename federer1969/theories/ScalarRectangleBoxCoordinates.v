(** Federer (1969), 4.1.8, p. 362: the
    derived Cartesian box is exactly the original
    set of coordinate inequalities. The block identification
    retains the original order of the coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanBlockCoordinates EuclideanCartesianMap
  OrientedRectangleDomain ScalarSegmentFactors ScalarRectangleBox.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_rectangle_box_coordinates]: membership is
    exactly u_k<x_k<v_k for every original coordinate,
    the final box in Federer 4.1.8, p. 362.
    Its ambient dimension equals the number of
    factors by scalar_rectangle_dimension; no new coordinate
    or ambient space is introduced. *)
Theorem scalar_rectangle_box_coordinates (R:realType) (f:seq (R*R))
    (x:R_n R (oriented_rectangle_dimension (@scalar_segment_factors R f))):
  @scalar_rectangle_box R f x <->
    forall i:'I_(oriented_rectangle_dimension (@scalar_segment_factors R f)),
      (nth (0,0) f (val i)).1<x i<(nth (0,0) f (val i)).2.
Proof.
elim:f=>[|a [|b t] IH] in x *.
- split;last by [].
  move=>_ i;have:=ltn_ord i;by rewrite ltn0.
- split.
  + move=>h i;by rewrite (ord1 i).
  + move=>h;exact:(h ord0).
- change ((a.1<(euclidean_block_split x).1 ord0<a.2 /\
      @scalar_rectangle_box R (b::t) (euclidean_block_split x).2) <->
    forall i:'I_(1+oriented_rectangle_dimension (@scalar_segment_factors R (b::t))),
      (nth (0,0) (a::b::t) (val i)).1<x i<(nth (0,0) (a::b::t) (val i)).2).
  rewrite (IH (euclidean_block_split x).2).
  split.
  + move=>[ha hTail] i;case:(split_ordP i)=>j->.
    * rewrite (ord1 j).
      change (is_true (a.1<x (lshift (oriented_rectangle_dimension (@scalar_segment_factors R (b::t))) ord0)<a.2)).
      by move:ha;rewrite /euclidean_block_split /= ffunE.
    * change (is_true ((nth (0,0) (b::t) (val j)).1<x (rshift 1%N j)<
        (nth (0,0) (b::t) (val j)).2)).
      by move:(hTail j);rewrite /euclidean_block_split /= ffunE.
  + move=>h;split.
    * have hFirst:=h (lshift (oriented_rectangle_dimension (@scalar_segment_factors R (b::t))) ord0).
      change (is_true (a.1<x (lshift (oriented_rectangle_dimension (@scalar_segment_factors R (b::t))) ord0)<a.2)) in hFirst.
      by rewrite /euclidean_block_split /= ffunE.
    * move=>j.
      have hLast:=h (rshift 1%N j).
      change (is_true ((nth (0,0) (b::t) (val j)).1<x (rshift 1%N j)<
        (nth (0,0) (b::t) (val j)).2)) in hLast.
      by rewrite /euclidean_block_split /= ffunE.
Qed.
