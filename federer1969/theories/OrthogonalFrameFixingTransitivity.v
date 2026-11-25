(** Federer (1969), 3.4.8(6),(8), pp. 328–329:
    the groups fixing an orthonormal frame act
    transitively on the unit sphere of its orthogonal
    complement. The project frame-extension theorem supplies
    the actual orthogonal transformation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom InnerProductUP InnerNorm LinearBasis InfiniteSequence
  OrthonormalFamilies InnerNormalization OrthogonalMaps GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct CoordinateProjection OrthonormalFrameMap OrthogonalInjectionSpaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [orthogonal_frame_fixing_transitive]: the
    sphere transitivity of H_j and Q_m in the
    proofs of 3.4.8(6),(8), pp. 328–329. Two
    actual unit vectors perpendicular to the fixed
    frame can be matched while each frame vector
    stays fixed. No group element is assumed. *)
Theorem orthogonal_frame_fixing_transitive (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  m (f:'I_m->X) (hF:orthonormal_family B f) (u v:X):
  B u u = 1 ->B v v = 1 ->
  (forall i,B u (f i) = 0) ->(forall i,B v (f i) = 0) ->
  exists g:{linear X->X},is_orthogonal_map B B g /\g u = v /\forall i,g (f i) = f i.
Proof.
move=>hU hV hUF hVF.
pose source:=ordinal_snoc f u.
pose target:=ordinal_snoc f v.
have hSource:orthonormal_family B source:=@orthonormal_snoc R X B hB m f u hF hU hUF.
have hTarget:orthonormal_family B target:=@orthonormal_snoc R X B hB m f v hF hV hVF.
have [p [hP hPAxis]]:=@orthonormal_frame_map_exists R X B hB m.+1 source hSource.
have [q [hQ hQAxis]]:=@orthonormal_frame_map_exists R X B hB m.+1 target hTarget.
have [g [hG hGP]]:=@orthogonal_injection_transitive R (R_n R m.+1) X
  (@euclidean_inner_product R m.+1) B (@euclidean_inner_productP R m.+1) hB
  m.+1 (@coordinate_basis R m.+1) n e (@coordinate_basisP R m.+1) he p q hP hQ.
exists g;split;first exact:hG.
split.
- have h:=hGP (@coordinate_basis R m.+1 ord_max).
  by rewrite hPAxis hQAxis /source /target !ordinal_snoc_last in h.
- move=>i;have h:=hGP (@coordinate_basis R m.+1 (lift ord_max i)).
  by rewrite hPAxis hQAxis /source /target !ordinal_snoc_lift in h.
Qed.
