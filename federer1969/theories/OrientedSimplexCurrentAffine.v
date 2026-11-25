(** Federer (1969), 4.1.11, p. 366: every affine
    image of an ordered simplex is the simplex of the
    ordered vertex images. Follow the printed induction,
    using the preceding point-image and join naturality laws.
    Singular maps and independent ambient dimensions remain allowed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom AffineMaps RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanAffineSmooth
  CurrentSpaces CurrentDirac CurrentDegreeTransportIdentity CurrentCompactElementaryPushforwards
  CurrentCompactPushforwardAlgebra CurrentCartesianMapPullback CurrentJoinSealed CurrentJoinLaws
  CurrentJoinCongruence CurrentJoinAffineSourcePushforward CurrentJoinAffineNaturality
  OrientedSimplexCurrentUP OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section OrientedSimplexCurrentAffine.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation FullM := (fun _:X=>True).
Local Notation FullN := (fun _:Y=>True).
Local Notation hFullM := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R m)) x).
Local Notation hFullN := (fun (y:Y) (_:True)=>@norm_full_domain_interior R Y
  (inner_norm (@euclidean_inner_productP R n)) y).
Local Notation FM := (fun (d:nat) (w:'I_(d.+1)->X)=>@OrientedSimplexCurrent.value R h2 m d w).
Local Notation FN := (fun (d:nat) (w:'I_(d.+1)->Y)=>@OrientedSimplexCurrent.value R h2 n d w).
Local Notation CM := (fun d=>@current_space R h2 m FullM hFullM d).
Local Notation CompactM := (fun d (T:CM d)=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m FullM hFullM d T)).
Variable A:X->Y.
Hypothesis hA:is_affine_map A.
Local Notation AImage := (fun (x:X) (_:True)=>Logic.I).
Local Notation AGlobal := (@euclidean_affine_map_smooth R m n FullM hFullM A hA).
Local Notation AClass := (@current_cartesian_factor_open_class R m n FullM hFullM A AGlobal).
Local Notation Push := (fun d (T:CM d) (hT:CompactM d T)=>@current_join_affine_current R h2 m n A hA d T hT).

(** Source for [oriented_simplex_current_affine]: the
    original A#[u_0,...,u_d]=[A(u_0),...,A(u_d)],
    Federer 4.1.11, p. 366. A is any affine map
    between independent Euclidean spaces; neither source
    simplex nor target simplex is assumed nondegenerate. *)
Theorem oriented_simplex_current_affine d (v:'I_(d.+1)->X)
    (hCompact:CompactM d (FM d v)):
  Push d (FM d v) hCompact=FN d (fun k=>A (v k)).
Proof.
elim:d v hCompact=>[|d ih] v hCompact;cbn beta.
- pose P:=@dirac_current R h2 m FullM hFullM (v ord0).
  pose hP:=@current_compact_dirac_support R h2 m FullM hFullM (v ord0) Logic.I.
  have hInput:=@current_compact_map_pushforward_congruence R h2 m n
    FullM FullN hFullM hFullN A AImage AClass 0%N (FM 0%N v) P hCompact hP
    (@oriented_simplex_current_point R h2 m v).
  have hPoint:=@current_compact_map_dirac_image R h2 m n FullM FullN hFullM hFullN
    A AImage AClass (v ord0) Logic.I hP.
  exact:(eq_trans hInput (eq_trans hPoint (esym (@oriented_simplex_current_point R h2 n (fun k=>A (v k)))))).
- pose P:=@dirac_current R h2 m FullM hFullM (v ord0).
  pose hP:=@current_compact_dirac_support R h2 m FullM hFullM (v ord0) Logic.I.
  pose T:=FM d (current_simplex_tail v).
  pose hT:=@oriented_simplex_current_compact R h2 m d (current_simplex_tail v).
  pose J:=@CurrentJoin.value R h2 m 0%N d P T hP hT.
  pose hJ:=@current_join_compact R h2 m 0%N d P T hP hT.
  have hSource:=@oriented_simplex_current_successor R h2 m d v hP hT.
  rewrite current_degree_transport_identity in hSource.
  have hInput:=@current_compact_map_pushforward_congruence R h2 m n
    FullM FullN hFullM hFullN A AImage AClass d.+1 (FM d.+1 v) J hCompact hJ hSource.
  have hNatural:=@current_join_affine_natural R h2 m n A hA 0%N d P T hP hT.
  pose AP:=Push 0%N P hP.
  pose AT:=Push d T hT.
  pose hAP:=@current_join_affine_current_compact R h2 m n A hA 0%N P hP.
  pose hAT:=@current_join_affine_current_compact R h2 m n A hA d T hT.
  pose Q:=@dirac_current R h2 n FullN hFullN (A (v ord0)).
  pose hQ:=@current_compact_dirac_support R h2 n FullN hFullN (A (v ord0)) Logic.I.
  pose U:=FN d (fun k=>A (v (lift ord0 k))).
  pose hU:=@oriented_simplex_current_compact R h2 n d (fun k=>A (v (lift ord0 k))).
  have hPoint:AP=Q:=@current_compact_map_dirac_image R h2 m n FullM FullN hFullM hFullN
    A AImage AClass (v ord0) Logic.I hP.
  have hTail:AT=U:=ih (current_simplex_tail v) hT.
  have hJoin:=@current_join_current_congruence R h2 n 0%N d AP Q AT U hAP hQ hAT hU hPoint hTail.
  have hTarget:=@oriented_simplex_current_successor R h2 n d (fun k=>A (v k)) hQ hU.
  rewrite current_degree_transport_identity in hTarget.
  exact:(eq_trans hInput (eq_trans hNatural (eq_trans hJoin (esym hTarget)))).
Qed.
End OrientedSimplexCurrentAffine.
