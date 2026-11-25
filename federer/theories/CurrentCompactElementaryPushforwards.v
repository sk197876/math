(** Federer (1969), 4.1.11, p. 365: point images and
    boundary commutation for the compact maps in the reversing
    and affine identities. These supporting laws reuse the
    complete preceding proper-pushforward and Dirac results. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDirac DiracCurrentBounds CurrentSupportGeometry SmoothCompactSet
  CurrentProperSupport CurrentCompactMapProper CurrentPushforwardSealed
  CurrentPushforwardCongruence CurrentPushforwardDirac CurrentPushforwardBoundary
  CurrentBoundary CurrentCompactBoundarySmooth CurrentCompactPushforwardAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_compact_dirac_support]: the original
    Dirac current is compactly supported at its point, supporting
    the point and reversing identities in Federer 4.1.11,
    p. 365. Reuse the previously proved exact support. *)
Theorem current_compact_dirac_support (R:realType) (h2:(1+1:R)!=0)
    m (U:set (R_n R m))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) U x) (a:R_n R m):
  U a->@compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m)))
    (@current_support R h2 m U hU 0%N (@dirac_current R h2 m U hU a)).
Proof.
move=>ha;rewrite (@dirac_current_support R h2 m U hU a ha).
exact:compact_set1.
Qed.

Section CompactMaps.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variables (U:set (R_n R m)) (V:set (R_n R n)).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) U x.
Hypothesis hV:forall y,V y->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) V y.
Variable f:R_n R m->R_n R n.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hf:norm_class_all_orders
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U f.
Local Notation C := (fun k=>@current_space R h2 m U hU k).
Local Notation Compact := (fun k (T:C k)=>@compact (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m U hU k T)).
Local Notation Proper := (fun k (T:C k) (hT:Compact k T)=>
  @current_compact_map_proper R h2 m n k U V hU T f hImage
    (norm_class_continuous (hf 0%N)) hT).
Local Notation P := (fun k (T:C k) (hT:Compact k T)=>
  @current_compact_map_pushforward R h2 m n U V hU hV f hImage hf k T hT).

(** Source for [current_compact_map_dirac_image]: the original
    compact image of delta_a is delta_(f(a)), supporting the
    point and affine formulas of Federer 4.1.11, p. 365. The
    preceding Dirac pushforward theorem supplies the action. *)
Theorem current_compact_map_dirac_image (a:R_n R m) (ha:U a)
    (hPoint:Compact 0%N (@dirac_current R h2 m U hU a)):
  P 0%N (@dirac_current R h2 m U hU a) hPoint=@dirac_current R h2 n V hV (f a).
Proof.
pose delta:=@dirac_current R h2 m U hU a.
have hCompare:=@current_pushforward_current_congruence R h2 m n 0%N U V hU hV
  f hImage hf delta delta (Proper 0%N delta hPoint)
  (@current_point_support_proper R h2 m n U V hU a ha f hImage) (erefl delta).
exact:(eq_trans hCompare (@current_pushforward_dirac R h2 m n U V hU hV
  a ha f hImage hf)).
Qed.

(** Source for [current_compact_map_boundary_image]: the
    original compact image commutes with the actual positive-
    degree boundary, supporting the reversing and simplex
    identities in Federer 4.1.11, pp. 365–366. Every compactness
    witness of the boundary is permitted. *)
Theorem current_compact_map_boundary_image k (T:C k.+1) (hT:Compact k.+1 T)
    (hBoundary:Compact k (@current_boundary R h2 m k U hU T)):
  @current_boundary R h2 n k V hV (P k.+1 T hT)=
  P k (@current_boundary R h2 m k U hU T) hBoundary.
Proof.
pose B:=@current_boundary R h2 m k U hU T.
have h:=@current_pushforward_boundary R h2 m n k U V hU hV T f hImage hf
  (Proper k.+1 T hT).
have hCompare:=@current_pushforward_current_congruence R h2 m n k U V hU hV
  f hImage hf B B
  (@current_pushforward_boundary_proper R h2 m n k U V hU T f hImage
    (Proper k.+1 T hT)) (Proper k B hBoundary) (erefl B).
exact:(eq_trans h hCompare).
Qed.
End CompactMaps.
