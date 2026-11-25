(** Federer (1969), 4.1.11, p. 366: the original
    ordered prism vertices commute with their prescribed
    images. Derive this from the two public vertex
    ranges alone, for the affine transfer of the prism
    formula after compact top-degree uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CurrentPrismVerticesUP CurrentPrismVerticesSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [current_prism_vertex_ranges_ext]: the
    two original index ranges cover every prism vertex,
    supporting Federer 4.1.11, p. 366. Their overlap
    concerns distinct lower and upper vertex positions. *)
Theorem current_prism_vertex_ranges_ext (Y:Type) m (k:'I_(m.+1))
    (f g:'I_(m.+2)->Y):
  (forall r:'I_(m.+1),(r<=k)%N->
    f (widen_ord (leqnSn m.+1) r)=g (widen_ord (leqnSn m.+1) r))->
  (forall r:'I_(m.+1),(k<=r)%N->f (lift ord0 r)=g (lift ord0 r))->f=g.
Proof.
move=>hLower hUpper;apply:funext=>l;case:(unliftP ord0 l)=>[r ->|->].
- case:(leqP k r)=>hkr.
  + exact:(hUpper r hkr).
  + have hBound:(r.+1<m.+1)%N:=leq_ltn_trans hkr (ltn_ord k).
    pose q:'I_(m.+1):=Ordinal hBound.
    have hLow:(q<=k)%N:=hkr.
    have hIndex:widen_ord (leqnSn m.+1) q=lift ord0 r.
      apply:val_inj;reflexivity.
    rewrite -hIndex;exact:(hLower q hLow).
- rewrite -current_prism_widen_zero;exact:(hLower ord0 (leq0n k)).
Qed.

(** Source for [current_prism_vertices_image]: taking
    the prescribed images of every original prism vertex
    gives the prism vertices of the prescribed endpoint
    images, supporting the affine transfer in Federer
    4.1.11, p. 366. This finite-family identity itself
    requires no affineness or nondegeneracy. *)
Theorem current_prism_vertices_image (X Y X' Y':Type)
    (A B:X->Y) (A' B':X'->Y') (C:Y->Y') m
    (v:'I_(m.+1)->X) (w:'I_(m.+1)->X') (k:'I_(m.+1)):
  (forall r,C (A (v r))=A' (w r))->
  (forall r,C (B (v r))=B' (w r))->
  (fun l=>C (@CurrentPrismVertices.value X Y A B m v k l))=
    @CurrentPrismVertices.value X' Y' A' B' m w k.
Proof.
move=>hA hB;apply:(@current_prism_vertex_ranges_ext Y' m k).
- move=>r hr.
  rewrite ((@CurrentPrismVertices.laws X Y A B).1 m v k r hr)
    ((@CurrentPrismVertices.laws X' Y' A' B').1 m w k r hr).
  exact:hA.
- move=>r hr.
  rewrite ((@CurrentPrismVertices.laws X Y A B).2 m v k r hr)
    ((@CurrentPrismVertices.laws X' Y' A' B').2 m w k r hr).
  exact:hB.
Qed.
