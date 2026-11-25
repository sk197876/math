(** Federer (1969), 4.1.8, p. 362: the
    original finite product exists as an actual
    current. Iterating the proved original binary
    product supplies only an existence witness. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import OrientedSegmentFactor OrientedRectangleDomain OrientedRectangleSpaces
  OrientedRectangleCurrentUP EuclideanFundamentalCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [oriented_rectangle_current_exists]: the
    original ordered product of any finite family
    of segments defines an actual current, supporting
    the induction in Federer 4.1.8, p. 362.
    The empty family uses the original E^0 convention. *)
Theorem oriented_rectangle_current_exists (R:realType) (h2:(1+1:R)!=0):
  exists P:forall f:seq (oriented_segment_factor R),@oriented_rectangle_space R h2 f (size f),
    @is_oriented_rectangle_current R h2 P.
Proof.
pose C f:=@oriented_rectangle_space R h2 f (size f).
pose Step (a:oriented_segment_factor R) (t:seq (oriented_segment_factor R)):C t->C (a::t):=
  match t as q return C q->C (a::q) with
  |[::]=>fun _=>@oriented_segment_factor_current R h2 a
  |b::s=>fun T=>@oriented_rectangle_product R h2 a b s 1%N (size (b::s))
      (@oriented_segment_factor_current R h2 a) T
  end.
pose P:=(fix P (f:seq (oriented_segment_factor R)):C f:=
  match f as g return C g with
  |[::]=>@euclidean_fundamental_current R h2 0%N
  |a::t=>Step a t (P t)
  end).
exists P;split;first by [].
split;by [].
Qed.
