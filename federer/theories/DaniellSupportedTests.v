(** Federer (1969), 2.5.20, p. 114: countably many uniformly dense supported
    tests determine whether a Daniell integral vanishes on an open set.
    Uniform boundedness from 2.5.19, p. 113, extends vanishing from the
    chosen tests to all functions supported there. Source context:
    CompactFunctionSupportedTests.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import CompactSupportFunctionUP CompactSupportDaniellSupport
  CompactFunctionSupportedTests DaniellIntegralUP DaniellSpaceCompactSpace
  DaniellSpaceCompactness CompactUniformNorm VectorFunctionLattice VectorDaniellDualExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [daniell_dense_supported_tests_vanish]:
    supporting uniform-density inference for the support
    assertion in Federer 2.5.20, p. 114. The
    functional is a genuine Daniell integral, whose uniform
    bound follows from compactness. *)
Theorem daniell_dense_supported_tests_vanish (R : realType) (Y : topologicalType)
    (A : (Y -> R) -> R) (U : set Y) (D : set (Y -> R)) :
  compact (@setT Y) ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) A ->
  is_countable_supported_test_family U D -> (forall g, D g -> A g=0) ->
  forall f, compactly_supported_continuous_functions f -> real_function_support f `<=` U -> A f=0.
Proof.
move=> hY hA hD hz f hf hs.
have [C [hC hb]] := @daniell_sup_norm_bounded R Y hY A hA.
have hL := @compact_support_vector_lattice R Y.
have hlin := daniell_compact_support_linear hA.
apply: real_small_zero=> e he.
have hC1 : 0<C+1 by lra.
pose d := e/(C+1).
have hd : 0<d by rewrite /d divr_gt0.
have [g [hg hnear]] := supported_tests_approximate hD hf hs hd.
have hgK := (supported_tests_member hD hg).1.
have hdiff := vector_function_lattice_difference hL hf hgK.
have h := hb (fun y => f y-g y) hdiff d (ltW hd) (fun y => ltW (hnear y)).
rewrite (vector_lattice_additive_difference hL hlin.1 hf hgK) (hz g hg) subr0 in h.
apply: le_lt_trans h _.
have hCd : C*d<(C+1)*d by rewrite ltr_pM2r // ltrDl.
by rewrite [(C+1)*d]mulrC /d divfK ?gt_eqF // in hCd.
Qed.

(** Source for [daniell_supported_tests_exclude_open_set]:
    the support avoids an open set once the countable
    supported tests vanish, supporting the fibre inclusion
    of Federer 2.5.20, p. 114, with the support
    definition of 2.5.14, p. 108. *)
Theorem daniell_supported_tests_exclude_open_set (R : realType) (Y : topologicalType)
    (A : (Y -> R) -> R) (U : set Y) (D : set (Y -> R)) :
  compact (@setT Y) -> open U ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) A ->
  is_countable_supported_test_family U D -> (forall g, D g -> A g=0) ->
  forall y, U y -> ~ compact_support_daniell_support A y.
Proof.
move=> hY hU hA hD hz y hy hsupport; apply: hsupport.
exists U; last exact hy.
split=> //; exact: daniell_dense_supported_tests_vanish hY hA hD hz.
Qed.
