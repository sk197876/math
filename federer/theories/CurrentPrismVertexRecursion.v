(** Federer (1969), 4.1.11, p. 366: recover
    the first cell and ordered tail recursion from the
    independent prism-vertex ranges. Consumers use only
    those public laws, never the existence construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Biorthogonal OrientedSimplexCurrentUP CurrentPrismVerticesUP
  CurrentPrismVerticesSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section CurrentPrismVertexRecursion.
Variables X Y:Type.
Variables A B:X->Y.
Variable P:forall m,('I_(m.+1)->X)->'I_(m.+1)->'I_(m.+2)->Y.
Arguments P : clear implicits.
Hypothesis hP:is_current_prism_vertices A B P.

(** Source for [current_prism_vertices_head]: every original
    prism cell starts with A(u_0), supporting Federer
    4.1.11, p. 366. *)
Theorem current_prism_vertices_head m (v:'I_(m.+1)->X) k:
  P m v k ord0=A (v ord0).
Proof.
rewrite -current_prism_widen_zero.
exact:(hP.1 m v k ord0 (leq0n k)).
Qed.

(** Source for [current_prism_vertices_first]: the first
    original cell has vertices A(u_0),B(u_0),...,B(u_m),
    supporting Federer 4.1.11, p. 366. *)
Theorem current_prism_vertices_first m (v:'I_(m.+1)->X):
  P m v ord0=ordinal_cons (A (v ord0)) (fun r=>B (v r)).
Proof.
apply:funext=>l;case:(unliftP ord0 l)=>[r ->|->].
- rewrite ordinal_consS;exact:(hP.2 m v ord0 r (leq0n r)).
- rewrite ordinal_cons0;exact:current_prism_vertices_head.
Qed.

(** Source for [current_prism_vertices_successor]: each
    later original prism cell is A(u_0) followed by the
    corresponding tail cell, supporting the inductive
    decomposition in Federer 4.1.11, p. 366. *)
Theorem current_prism_vertices_successor m (v:'I_(m.+2)->X) (k:'I_(m.+1)):
  P m.+1 v (lift ord0 k)=ordinal_cons (A (v ord0))
    (P m (current_simplex_tail v) k).
Proof.
apply:funext=>l;case:(unliftP ord0 l)=>[r ->|->].
- rewrite ordinal_consS.
  case:(unliftP ord0 r)=>[s ->|->].
  + case:(leqP k s)=>hks.
    * have hLarge:(lift ord0 k<=lift (ord0:'I_(m.+2)) s)%N by rewrite !lift0 ltnS.
      rewrite (hP.2 m.+1 v (lift ord0 k) (lift ord0 s) hLarge).
      exact:esym (hP.2 m (current_simplex_tail v) k s hks).
    * have hBound:(s.+1<m.+1)%N:=leq_ltn_trans hks (ltn_ord k).
      pose q: 'I_(m.+1):=Ordinal hBound.
      have hLow:(q<=k)%N:=hks.
      have hOuter:(lift ord0 q<=lift (ord0:'I_(m.+2)) k)%N by rewrite !lift0 ltnS.
      have hInnerIndex:widen_ord (leqnSn m.+1) q=lift ord0 s.
        apply:val_inj;reflexivity.
      have hOuterIndex:widen_ord (leqnSn m.+2) (lift ord0 q)=lift ord0 (lift ord0 s).
        by rewrite current_prism_widen_lift hInnerIndex.
      have hOuterValue:=hP.1 m.+1 v (lift ord0 k) (lift ord0 q) hOuter.
      have hInnerValue:=hP.1 m (current_simplex_tail v) k q hLow.
      rewrite hOuterIndex in hOuterValue.
      rewrite hInnerIndex in hInnerValue.
      exact:(eq_trans hOuterValue (esym hInnerValue)).
  + have hLow:(lift (ord0:'I_(m.+2)) ord0<=lift ord0 k)%N by rewrite !lift0 ltnS leq0n.
    have hIndex:widen_ord (leqnSn m.+2) (lift (ord0:'I_(m.+2)) ord0)=lift ord0 ord0.
      apply:val_inj;reflexivity.
    have hValue:=hP.1 m.+1 v (lift ord0 k) (lift ord0 ord0) hLow.
    rewrite hIndex in hValue.
    exact:(eq_trans hValue (esym (current_prism_vertices_head (current_simplex_tail v) k))).
- rewrite ordinal_cons0;exact:current_prism_vertices_head.
Qed.
End CurrentPrismVertexRecursion.
