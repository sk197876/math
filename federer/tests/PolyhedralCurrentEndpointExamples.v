(** Actual-current endpoint regressions for Federer (1969),
    4.1.22, p. 379: the nonzero zero-simplex in R^0
    is integral polyhedral in its singleton index; its real
    half multiple is in the original real space. Exercise the
    public original predicates and opaque carrier image laws,
    together with additive inverses, both compact-union
    carrier images and the empty-index obstruction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingZero CurrentSpaces CurrentDirac CurrentBoundedPointTest
  ModuleQuotient SmoothCompactSet ConvexHull InnerConvex
  AdditiveSubgroupRepresentationUP LinearSubspaceRepresentationUP
  PolyhedralCurrents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PolyhedralCurrentEndpointExamples.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 0%N)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation C := (@current_space R h2 0%N Full hFull 0%N).
Local Notation P := (@dirac_current R h2 0%N Full hFull (0:X)).
Local Notation K := (@smooth_compact_singleton R X NX hNX Full (0:X) Logic.I).
Local Notation Integral := (@integral_polyhedral_current_class R h2 0%N 0%N Full hFull K).
Local Notation Real := (@polyhedral_current_subspace R h2 0%N 0%N Full hFull K).

(** Source for [polyhedral_zero_dimensional_point_nonzero]:
    the original zero-simplex is a genuine nonzero actual
    current, checking the retained m=n=0 endpoint of the
    definitions in 4.1.22, p. 379. *)
Example polyhedral_zero_dimensional_point_nonzero:P<>0.
Proof.
have[gamma [hSupport [hRange hOne]]]:=
  @current_bounded_point_test_exists R h2 0%N (0:X) 1 ltr01.
move=>hZero.
have hAction:=congr1 (fun T:C=>@current_value R h2 0%N Full hFull 0%N T gamma) hZero.
rewrite dirac_current_evaluation hOne zero_formK
  (linear0 (@current_value R h2 0%N Full hFull 0%N)) hom_zeroE in hAction.
have hNonzero:(1:R)!=0:=@oner_neq0 R.
by rewrite hAction eqxx in hNonzero.
Qed.

(** Source for [polyhedral_zero_dimensional_point_integral]:
    the original nonzero point current belongs to the
    actual fixed-singleton integral class in R^0,
    checking 4.1.22, p. 379. *)
Example polyhedral_zero_dimensional_point_integral:Integral P.
Proof.
pose v:'I_1->X:=fun _=>0.
have hHull:@polyhedral_simplex_vertex_hull R 0%N 0%N v
    `<=` smooth_compact_carrier K.
  apply:convex_hull_least.
  - by move=>x [i <-].
  - move=>x y -> -> t _ _;by rewrite !scaler0 addr0.
have h:=@integral_polyhedral_current_generator R h2 0%N 0%N Full hFull K v hHull.
by rewrite open_oriented_simplex_point in h.
Qed.

(** Source for [polyhedral_zero_dimensional_half_point_real]:
    the original real span admits the real coefficient 1/2
    applied to that actual point, checking the distinction of
    the two definitions in 4.1.22, p. 379. *)
Example polyhedral_zero_dimensional_half_point_real:Real ((1/2:R)*:P).
Proof.
apply:(@subspace_scale R C Real (1/2:R) P).
exact:integral_polyhedral_current_is_polyhedral polyhedral_zero_dimensional_point_integral.
Qed.

(** Source for [polyhedral_zero_dimensional_integral_carrier]:
    the original nonzero actual point is represented by
    the opaque integral carrier, checking its exact image
    in 4.1.22, p. 379. *)
Example polyhedral_zero_dimensional_integral_carrier:
  exists z:@integral_polyhedral_current_space R h2 0%N 0%N Full hFull K,
    @integral_polyhedral_current_inclusion R h2 0%N 0%N Full hFull K z= P.
Proof.
exact:(additive_subgroup_representation_full
  (@integral_polyhedral_current_space_laws R h2 0%N 0%N Full hFull K)
  polyhedral_zero_dimensional_point_integral).
Qed.

(** Source for [polyhedral_zero_dimensional_real_carrier]:
    the original actual half point is represented by the
    opaque real carrier, checking its exact linear image
    in 4.1.22, p. 379. *)
Example polyhedral_zero_dimensional_real_carrier:
  exists z:@polyhedral_current_space R h2 0%N 0%N Full hFull K,
    @polyhedral_current_inclusion R h2 0%N 0%N Full hFull K z=(1/2:R)*:P.
Proof.
exact:(subspace_representation_full
  (@polyhedral_current_space_laws R h2 0%N 0%N Full hFull K)
  polyhedral_zero_dimensional_half_point_real).
Qed.

(** Source for [polyhedral_zero_dimensional_empty_index_obstruction]:
    the same nonzero original point belongs to neither
    empty-index class, checking that the full vertex-hull
    condition is retained in 4.1.22, p. 379. *)
Example polyhedral_zero_dimensional_empty_index_obstruction:
  ~@integral_polyhedral_current_class R h2 0%N 0%N Full hFull
    (@smooth_compact_empty R X NX hNX Full) P /\
  ~@polyhedral_current_subspace R h2 0%N 0%N Full hFull
    (@smooth_compact_empty R X NX hNX Full) P.
Proof.
split=>hPoint;apply:polyhedral_zero_dimensional_point_nonzero.
- exact:(@integral_polyhedral_current_empty_index R h2 0%N 0%N Full hFull P).1 hPoint.
- exact:(@polyhedral_current_empty_index R h2 0%N 0%N Full hFull P).1 hPoint.
Qed.

(** Source for [polyhedral_negative_zero_dimensional_point_integral]:
    the original additive subgroup includes the nonzero negative
    point current in R^0, checking the meaning of integral
    generation in 4.1.22, p. 379. No orientation convention
    for a later convex-cell definition is assumed here. *)
Example polyhedral_negative_zero_dimensional_point_integral:
  Integral (-P) /\(-P<>0).
Proof.
split.
- exact:(@integral_polyhedral_current_negate R h2 0%N 0%N Full hFull K P
    polyhedral_zero_dimensional_point_integral).
- move=>hZero;apply:polyhedral_zero_dimensional_point_nonzero.
  have hOpposite:=congr1 (fun T:C=>-T) hZero.
  by rewrite opprK oppr0 in hOpposite.
Qed.

(** Source for [polyhedral_negative_point_union_carrier]: the
    original integral compact union has the negative actual
    point in the image of its opaque abelian carrier,
    checking the union assertion in 4.1.22, p. 379. *)
Example polyhedral_negative_point_union_carrier:
  exists z:@integral_polyhedral_current_union_space R h2 0%N 0%N Full hFull,
    @integral_polyhedral_current_union_inclusion R h2 0%N 0%N Full hFull z= -P.
Proof.
apply:(additive_subgroup_representation_full
  (@integral_polyhedral_current_union_space_laws R h2 0%N 0%N Full hFull)).
exists K;exact:polyhedral_negative_zero_dimensional_point_integral.1.
Qed.

(** Source for [polyhedral_half_point_real_union_carrier]: the
    original real compact union has the actual half point
    in the image of its opaque linear carrier, checking
    the last assertion of 4.1.22, p. 379. *)
Example polyhedral_half_point_real_union_carrier:
  exists z:@polyhedral_current_union_space R h2 0%N 0%N Full hFull,
    @polyhedral_current_union_inclusion R h2 0%N 0%N Full hFull z=(1/2:R)*:P.
Proof.
apply:(subspace_representation_full
  (@polyhedral_current_union_space_laws R h2 0%N 0%N Full hFull)).
exists K;exact:polyhedral_zero_dimensional_half_point_real.
Qed.
End PolyhedralCurrentEndpointExamples.
