(** Federer (1969), 4.1.12, p. 368: the
    union over all compact K is a vector
    space. The original locally flat currents form
    a vector space as well. Use the directed
    compact indices and actual linear scalar contraction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import Hom Bilinear ModuleQuotient RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  SmoothCompactSet SmoothTestSpaces CurrentContraction CurrentSupportGeometry
  NormalCurrentsUP NormalCurrentLinear FlatCurrentsUP FlatCurrentFinite
  FlatCurrentClosure CurrentFlatCompactMonotone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatCurrentUnion.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation flat := (@is_flat_current R h2 n m U hU).
Local Notation localflat := (@is_locally_flat_current R h2 n m U hU).
Local Notation ScalarTest := (@current_test_space R h2 n U hU 0%N).
Local Notation hScalar := (@current_smooth_space_laws R h2 n U hU 0%N).
Local Notation contract gamma := (@current_contraction R h2 n 0%N m U hU
  (smooth_test_inclusion hScalar gamma)).

(** Source for [flat_current_zero]: the zero
    current belongs to the original flat space,
    Federer 4.1.12, p. 368, even for
    empty U. The empty compact index suffices. *)
Lemma flat_current_zero:flat (0:C).
Proof.
pose K:=@smooth_compact_empty R X NX hNX U.
exists K;apply:(@supported_normal_current_is_flat R h2 n m U hU K (0:C)).
split;first exact:normal_current_zero.
exact:current_support_zero_subset.
Qed.

(** Source for [flat_current_linear_combination]: the
    original union F_m(U) is closed under real
    linear combinations, Federer 4.1.12, p. 368.
    The union of the two compact indices is
    a common index; no exhaustion is chosen. *)
Theorem flat_current_linear_combination c (S T:C):
  flat S->flat T->flat (c*:S+T).
Proof.
move=>[K hS] [L hT].
pose M:=smooth_compact_union K L.
have hKM:smooth_compact_carrier K `<=` smooth_compact_carrier M by move=>x hx;left.
have hLM:smooth_compact_carrier L `<=` smooth_compact_carrier M by move=>x hx;right.
have hS':@is_flat_current_supported_in R h2 n m U hU M S:=
  @flat_current_compact_monotone R h2 n m U hU K M hKM S hS.
have hT':@is_flat_current_supported_in R h2 n m U hU M T:=
  @flat_current_compact_monotone R h2 n m U hU L M hLM T hT.
pose A:=@flat_current_subspace R h2 n m U hU M.
exists M.
exact:(@subspace_add R C A (c*:S) T (@subspace_scale R C A c S hS') hT').
Qed.

(** Source for [flat_current_union_subspace]: the
    independently specified original union F_m(U)
    has the vector-subspace laws, Federer 4.1.12,
    p. 368. *)
Definition flat_current_union_subspace:subspace C.
Proof.
refine (@Subspace R C flat flat_current_zero _ _).
- move=>S T hS hT;have h:=flat_current_linear_combination 1 hS hT.
  by rewrite scale1r in h.
- move=>c S hS;have h:=flat_current_linear_combination c hS flat_current_zero.
  by rewrite addr0 in h.
Defined.

(** Source for [locally_flat_current_linear_combination]:
    the original locally flat class is closed
    under real linear combinations, supporting Federer
    4.1.12, p. 368. Every compact scalar
    test uses its actual linear contraction. *)
Theorem locally_flat_current_linear_combination c (S T:C):
  localflat S->localflat T->localflat (c*:S+T).
Proof.
move=>hS hT gamma.
rewrite (linearP (contract gamma)).
exact:(flat_current_linear_combination c (hS gamma) (hT gamma)).
Qed.
End FlatCurrentUnion.
