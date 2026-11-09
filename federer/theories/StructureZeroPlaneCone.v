(** Federer (1969), 3.3.4, p. 288: the zero-plane
    endpoint of the cone alternatives. Prove the actual
    distance law and empty small-aperture cones before using
    any averaging argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct InnerMetric InnerNorm MetricSetDistanceUP
  StructureCone StructureExtremePlanes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_zero_plane_distance]: supporting
    zero-dimensional case of Federer 3.3.4, p. 288:
    distance from x to the actual zero plane is its
    original Euclidean norm. Only the infimum laws are used. *)
Lemma structure_zero_plane_distance (R:realType) n (V:G (R_n R n) 0):
  is_metric_set_distance
    [set x:inner_metric_space (@euclidean_inner_productP R n)|grassmann_val V x]
    (inner_norm (@euclidean_inner_productP R n)).
Proof.
constructor=>x.
- move=>y hy; have ->:y=0:=structure_zero_plane_member hy.
  by rewrite inner_metric_distanceE subr0.
- move=>b hLower; have h0:grassmann_val V 0:=subspace_zero _.
  have h:=hLower 0 h0; by rewrite inner_metric_distanceE subr0 in h.
Qed.

(** Source for [structure_zero_plane_cone_empty]: in the
    zero-plane endpoint of Federer 3.3.4, p. 288,
    every original cone with 0<s<=1 is empty,
    including cones with infinite radius. *)
Lemma structure_zero_plane_cone_empty (R:realType) n (V:G (R_n R n) 0)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (r: \bar R) (s:R):
  0<s ->s<=1 ->structure_cone V a r s=set0.
Proof.
move=>hs hs1; apply/seteqP; split=>x hx; last by [].
have [hAngle _]:=((@structure_cone_specification R n 0 V a r s)
  _ (structure_zero_plane_distance V) x).1 hx.
have hInv:1<=s^-1 by rewrite (invf_ge1 hs).
have hNorm:=inner_norm_nonnegative (@euclidean_inner_productP R n) (x-a).
have hBound:inner_norm (@euclidean_inner_productP R n) (x-a)<=
    s^-1*inner_norm (@euclidean_inner_productP R n) (x-a).
  rewrite -[X in X<=_]mul1r; exact:(ler_pM ler01 hNorm hInv (lexx _)).
by move:(lt_le_trans hAngle hBound); rewrite ltxx.
Qed.
