(** Federer (1969), 4.1.8, p. 362: the
    original ordered-product equations determine every
    rectangular face uniquely. This is finite induction,
    independent of the boundary identity to be proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import OrientedSegmentFactor OrientedRectangleDomain OrientedRectangleSpaces OrientedRectangleFacesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [oriented_rectangle_faces_unique]: the
    original face products are uniquely specified,
    supporting Federer 4.1.8, p. 362. *)
Theorem oriented_rectangle_faces_unique (R:realType) (h2:(1+1:R)!=0)
    (F G:forall f:seq (oriented_segment_factor R),'I_(size f)->
      @oriented_rectangle_space R h2 f (size f).-1):
  @is_oriented_rectangle_faces R h2 F ->@is_oriented_rectangle_faces R h2 G ->F = G.
Proof.
move=>[hFS [hFH hFT]] [hGS [hGH hGT]].
apply:functional_extensionality_dep=>f.
elim:f=>[|a t hTail].
- apply:funext=>k;by have:=ltn_ord k;rewrite ltn0.
- case:t hTail=>[|b t] hTail.
  + apply:funext=>k;by rewrite hFS hGS.
  + apply:funext=>k;case:(unliftP ord0 k)=>[j ->|->].
    * by rewrite hFT hGT hTail.
    * by rewrite hFH hGH.
Qed.
