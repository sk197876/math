(** Federer (1969), 4.1.16, p. 374: the compact index
    is precisely the existing convex hull of the actual
    support of the original flat current. Compactness is
    proved from an arbitrary existing flat index. No point
    is adjoined when the support is empty. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  InnerConvex ConvexHull SmoothCompactSet CurrentSpaces CurrentSupportGeometry
  CurrentSupportExtensionality FlatCurrentsUP FlatCurrentFinite
  EuclideanCompactConvexHullAll.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section EuclideanFlatConvexHullIndex.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hN).
Local Notation U := (fun _:X=>True).
Variable hU : forall x,U x->norm_domain_interior N U x.
Variable T : @current_space R h2 n U hU m.
Hypothesis hFlat : @is_flat_current R h2 n m U hU T.
Local Notation support := (@current_support R h2 n U hU m T).
Local Notation C := (@convex_hull R X support).

(** Source for [euclidean_flat_support_compact]: T in
    F_m(R^n) has compact support, by 4.1.12,
    p. 368, used in 4.1.16, p. 374. The defining
    compact index is eliminated inside the proof. *)
Lemma euclidean_flat_support_compact : @compact XT support.
Proof.
have [K hK] := hFlat.
apply: (@current_support_compact_bound R h2 n m U hU K T).
exact: (@flat_current_supported_support R h2 n m U hU K T hK).
Qed.

(** Source for [euclidean_flat_support_convex_hull_compact]:
    the original C is compact by the finite-dimensional
    compact-hull theorem 2.10.21, p. 184, supporting
    4.1.16, p. 374. This includes empty support and n=0. *)
Theorem euclidean_flat_support_convex_hull_compact : @compact XT C.
Proof.
exact: (@euclidean_own_norm_compact_convex_hull_all R n support
  euclidean_flat_support_compact).
Qed.

(** Source for [current_flat_convex_hull_index]: exactly the
    convex hull C of spt T, Federer 4.1.16, p. 374,
    as a compact subset of the original full domain.
    The carrier is an abbreviation of the already opaque
    hull, and its compactness is a proved law. *)
Definition current_flat_convex_hull_index : smooth_compact_set hN U :=
  @Build_smooth_compact_set R X N hN U C
    (fun _ _=>Logic.I) euclidean_flat_support_convex_hull_compact.

(** Source for [current_flat_convex_hull_index_carrier]: the
    compact carrier is precisely the printed hull,
    supporting Federer 4.1.16, p. 374. *)
Lemma current_flat_convex_hull_index_carrier :
  smooth_compact_carrier current_flat_convex_hull_index=C.
Proof. by []. Qed.

(** Source for [current_flat_convex_hull_index_contains_support]:
    C contains spt T, by the original hull law,
    supporting Federer 4.1.16, p. 374. *)
Lemma current_flat_convex_hull_index_contains_support :
  support `<=` smooth_compact_carrier current_flat_convex_hull_index.
Proof. exact: (@convex_hull_includes R X support). Qed.

(** Source for [current_flat_convex_hull_index_convex]: the
    exact carrier C is convex, supporting the nearest
    retraction used in Federer 4.1.16, p. 374. *)
Lemma current_flat_convex_hull_index_convex :
  is_inner_convex (smooth_compact_carrier current_flat_convex_hull_index).
Proof. exact: (@convex_hull_convex R X support). Qed.

(** Source for [current_flat_convex_hull_index_empty]: the
    zero-current branch retains the empty hull, supporting
    Federer 4.1.16, p. 374. No nonempty hull is imposed. *)
Theorem current_flat_convex_hull_index_empty :
  support `<=` set0 ->
  T=0 /\ smooth_compact_carrier current_flat_convex_hull_index=set0.
Proof.
move=> hEmpty; split.
- exact: (@current_empty_support_iff_zero R h2 n m U hU T).1 hEmpty.
- have hSupport : support=set0.
    apply/seteqP; split; first exact: hEmpty.
    by move=> x [].
  by rewrite current_flat_convex_hull_index_carrier hSupport convex_hull_empty.
Qed.
End EuclideanFlatConvexHullIndex.
