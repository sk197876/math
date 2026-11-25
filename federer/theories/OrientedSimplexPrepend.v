(** Federer (1969), 4.1.11, pp. 365–366: the
    original point join prepends one vertex. Recover this
    convenient form solely from the opaque simplex laws
    and the existing point-join congruence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct Biorthogonal
  CurrentSpaces CurrentDirac CurrentDegreeTransportIdentity CurrentCompactElementaryPushforwards
  CurrentJoinSealed CurrentJoinCongruence OrientedSimplexCurrentUP
  OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section OrientedSimplexPrepend.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation F := (fun (m:nat) (v:'I_(m.+1)->X)=>@OrientedSimplexCurrent.value R h2 n m v).

(** Source for [oriented_simplex_tail_prepend]: the original
    tail of (u,v_0,...,v_m) is (v_0,...,v_m),
    supporting Federer 4.1.11, pp. 365–366. *)
Lemma oriented_simplex_tail_prepend m u (v:'I_(m.+1)->X):
  current_simplex_tail (ordinal_cons u v)=v.
Proof. apply:funext=>k;exact:ordinal_consS. Qed.

(** Source for [oriented_simplex_current_prepend]:
    [u,v_0,...,v_m] is delta_u join [v_0,...,v_m],
    the original recursion of Federer 4.1.11, p. 365,
    used for the prism decomposition on p. 366. *)
Theorem oriented_simplex_current_prepend m u (v:'I_(m.+1)->X):
  F m.+1 (ordinal_cons u v)=
    @CurrentJoin.value R h2 n 0%N m (@dirac_current R h2 n Full hFull u) (F m v)
      (@current_compact_dirac_support R h2 n Full hFull u Logic.I)
      (@oriented_simplex_current_compact R h2 n m v).
Proof.
pose w:=ordinal_cons u v.
pose P:=@dirac_current R h2 n Full hFull (w ord0).
pose Q:=@dirac_current R h2 n Full hFull u.
pose hP:=@current_compact_dirac_support R h2 n Full hFull (w ord0) Logic.I.
pose hQ:=@current_compact_dirac_support R h2 n Full hFull u Logic.I.
pose T:=F m (current_simplex_tail w).
pose hT:=@oriented_simplex_current_compact R h2 n m (current_simplex_tail w).
pose hV:=@oriented_simplex_current_compact R h2 n m v.
have hRec:=@oriented_simplex_current_successor R h2 n m w hP hT.
rewrite current_degree_transport_identity in hRec.
have hPoint:P=Q by rewrite /P /Q /w ordinal_cons0.
have hTail:T=F m v by rewrite /T /w oriented_simplex_tail_prepend.
have hJoin:=@current_join_current_congruence R h2 n 0%N m P Q T (F m v)
  hP hQ hT hV hPoint hTail.
exact:(eq_trans hRec hJoin).
Qed.
End OrientedSimplexPrepend.
