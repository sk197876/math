(** Federer (1969), 4.1.8, p. 362: all
    original rectangular faces exist as actual currents.
    Iterating only the original binary product proves
    their independent ordered-product specification. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import OrientedSegmentFactor OrientedRectangleDomain OrientedRectangleSpaces
  OrientedRectangleCurrentSealed OrientedRectangleFacesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [oriented_rectangle_faces_exists]: the
    original finite family of endpoint-difference faces
    consists of actual currents, supporting Federer
    4.1.8, p. 362. The construction proves
    existence only; no boundary law is used. *)
Theorem oriented_rectangle_faces_exists (R:realType) (h2:(1+1:R)!=0):
  exists F:forall f:seq (oriented_segment_factor R),'I_(size f)->
      @oriented_rectangle_space R h2 f (size f).-1,
    @is_oriented_rectangle_faces R h2 F.
Proof.
have hEmpty (k:'I_0):False by have:=ltn_ord k;rewrite ltn0.
pose Face f:=@oriented_rectangle_space R h2 f (size f).-1.
pose Step (a:oriented_segment_factor R) (t:seq (oriented_segment_factor R)):
    ('I_(size t)->Face t)->'I_(size (a::t))->Face (a::t):=
  match t as q return ('I_(size q)->Face q)->'I_(size (a::q))->Face (a::q) with
  |[::]=>fun _ _=>@oriented_segment_factor_endpoint_difference R h2 a
  |b::s=>fun F k=>
      if unlift ord0 k is Some j then
        @oriented_rectangle_product R h2 a b s 1%N (size (b::s)).-1
          (@oriented_segment_factor_current R h2 a) (F j)
      else @oriented_rectangle_product R h2 a b s 0%N (size (b::s))
        (@oriented_segment_factor_endpoint_difference R h2 a)
        (@OrientedRectangleCurrent.value R h2 (b::s))
  end.
pose F:=(fix F (f:seq (oriented_segment_factor R)):'I_(size f)->Face f:=
  match f as g return 'I_(size g)->Face g with
  |[::]=>fun k=>False_rect _ (hEmpty k)
  |a::t=>Step a t (F t)
  end).
exists F;split;first by [].
split.
- move=>a b t;by rewrite /F /Step unlift_none.
- move=>a b t k;by rewrite /F /Step liftK.
Qed.
