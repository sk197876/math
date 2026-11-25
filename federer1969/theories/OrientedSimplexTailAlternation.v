(** Federer (1969), 4.1.11, p. 366: the first-pair
    sign and induction on the ordered tail give all
    vertex exchanges. Reuse the original opaque simplex
    recursion and the proved linearity of its point join. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology fingroup perm.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDirac CurrentDegreeTransportIdentity CurrentCompactElementaryPushforwards
  CurrentCompactCurrentArithmetic CurrentJoinSealed CurrentJoinCongruence CurrentJoinFiniteLinearity
  OrientedSimplexCurrentUP OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_simplex_positive_swap_head]:
    exchanging two later vertices fixes the first point,
    supporting the permutation argument in Federer 4.1.11,
    p. 366. This is only the original ordinal indexing. *)
Lemma current_simplex_positive_swap_head (X:Type) m
    (v:'I_(m.+2)->X) (i j:'I_(m.+1)):
  v (tperm (lift ord0 i) (lift ord0 j) ord0)=v ord0.
Proof. by rewrite tpermD // eq_sym neq_lift. Qed.

(** Source for [current_simplex_positive_swap_tail]:
    the same exchange acts on the original ordered tail,
    supporting Federer 4.1.11, p. 366. *)
Lemma current_simplex_positive_swap_tail (X:Type) m
    (v:'I_(m.+2)->X) (i j:'I_(m.+1)):
  current_simplex_tail (fun k=>v (tperm (lift ord0 i) (lift ord0 j) k))=
    (fun k=>current_simplex_tail v (tperm i j k)).
Proof.
apply:funext=>k.
have h:=@inj_tperm (Finite.clone 'I_(m.+1) _) (Finite.clone 'I_(m.+2) _)
  (lift ord0) i j k (@lift_inj (m.+2) ord0).
change (v (tperm (lift ord0 i) (lift ord0 j) (lift ord0 k))=
  v (lift ord0 (tperm i j k))).
by rewrite -h.
Qed.

Section OrientedSimplexTailAlternation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation F := (fun (m:nat) (w:'I_(m.+1)->X)=>@OrientedSimplexCurrent.value R h2 n m w).
Local Notation C := (fun m=>@current_space R h2 n Full hFull m).
Local Notation Compact := (fun m (T:C m)=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n Full hFull m T)).

(** Source for [oriented_simplex_current_tail_negative]:
    fixing the first vertex and negating its tail negates
    the original simplex, supporting Federer 4.1.11,
    p. 366. No associativity or permutation law is assumed. *)
Theorem oriented_simplex_current_tail_negative m (v w:'I_(m.+2)->X):
  w ord0=v ord0->F m (current_simplex_tail w)= -F m (current_simplex_tail v)->
  F m.+1 w= -F m.+1 v.
Proof.
move=>hHead hTail;cbn beta in hTail.
pose P:=@dirac_current R h2 n Full hFull (v ord0).
pose Pw:=@dirac_current R h2 n Full hFull (w ord0).
pose hP:=@current_compact_dirac_support R h2 n Full hFull (v ord0) Logic.I.
pose hPw:=@current_compact_dirac_support R h2 n Full hFull (w ord0) Logic.I.
pose T:=F m (current_simplex_tail v).
pose Tw:=F m (current_simplex_tail w).
pose hT:=@oriented_simplex_current_compact R h2 n m (current_simplex_tail v).
pose hTw:=@oriented_simplex_current_compact R h2 n m (current_simplex_tail w).
have hPoint:Pw = P:=congr1 (@dirac_current R h2 n Full hFull) hHead.
have hNegative:Compact m (-T).
  have h:=@current_compact_scaled_support R h2 n m Full hFull T (-1:R) hT.
  by rewrite scaleN1r in h.
have hJoin:=@current_join_current_congruence R h2 n 0%N m Pw P Tw (-T)
  hPw hP hTw hNegative hPoint hTail.
have hScale:=@current_join_second_scale R h2 n 0%N m P hP (-1:R) T hT.
have hRecV:=@oriented_simplex_current_successor R h2 n m v hP hT.
have hRecW:=@oriented_simplex_current_successor R h2 n m w hPw hTw.
rewrite current_degree_transport_identity in hRecV.
rewrite current_degree_transport_identity in hRecW.
have hScaled:Compact m ((-1:R)*:T) by rewrite scaleN1r.
have hScaleValue:=hScale hScaled.
have hNegativeInput:=@current_join_current_congruence R h2 n 0%N m P P
  ((-1:R)*:T) (-T) hP hP hScaled hNegative (erefl P) (ltac:(by rewrite scaleN1r)).
rewrite hNegativeInput scaleN1r in hScaleValue.
exact:(eq_trans hRecW (eq_trans hJoin
  (eq_trans hScaleValue (congr1 (fun U=>-U) (esym hRecV))))).
Qed.
End OrientedSimplexTailAlternation.
