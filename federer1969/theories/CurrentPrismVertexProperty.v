(** Federer (1969), 4.1.11, p. 366: every
    original prism vertex is a lower or upper image
    of an original simplex vertex. Derive this from
    the two independently specified ordered ranges. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CurrentPrismVerticesUP CurrentPrismVerticesSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [current_prism_vertex_property]: a property
    of both original vertex ranges holds for every
    vertex in the prism family, supporting the rectangle
    decomposition in Federer 4.1.11, p. 366. *)
Lemma current_prism_vertex_property (X Y:Type) (A B:X->Y) m
    (v:'I_(m.+1)->X) (k:'I_(m.+1)) (P:Y->Prop):
  (forall r,P (A (v r)))->(forall r,P (B (v r)))->
  forall l,P (@CurrentPrismVertices.value X Y A B m v k l).
Proof.
move=>hLower hUpper l;case:(unliftP ord0 l)=>[r ->|->].
- case:(leqP k r)=>hkr.
  + rewrite ((@CurrentPrismVertices.laws X Y A B).2 m v k r hkr).
    exact:hUpper.
  + have hBound:(r.+1<m.+1)%N:=leq_ltn_trans hkr (ltn_ord k).
    pose q:'I_(m.+1):=Ordinal hBound.
    have hLow:(q<=k)%N:=hkr.
    have hIndex:widen_ord (leqnSn m.+1) q=lift ord0 r.
      apply:val_inj;reflexivity.
    rewrite -hIndex ((@CurrentPrismVertices.laws X Y A B).1 m v k q hLow).
    exact:hLower.
- rewrite -current_prism_widen_zero
    ((@CurrentPrismVertices.laws X Y A B).1 m v k ord0 (leq0n k)).
  exact:hLower.
Qed.
