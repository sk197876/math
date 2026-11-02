(** Federer (1969), 2.5.12, printed p. 106, final paragraph: the pairing is
    bounded by the product of the primal and dual norms. The proof
    normalises a nonzero vector in the defining sphere of nu*, handling the
    zero vector separately. This is a consequence of the norm definition on
    pp. 102–103, independent of the construction of the representing
    density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric VectorDaniellHypotheses
  VectorDaniellDualExtension VectorDaniellRationalSpan VectorDaniellWeakMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DualNorm.
Variable R : realType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.

(** Source for [dual_norm_evaluation_bound]: the norm product
    bound used in the last paragraph of Federer 2.5.12, p. 106.
    The functional need not belong to the unit ball. *)
Lemma dual_norm_evaluation_bound (alpha : E -> R) (v : E) : dual_space hN alpha ->
  `|alpha v| <= dual_norm N alpha * N v.
Proof.
move=> ha.
have [C [hC hCb]] := dual_space_bounded ha.
have [->|hv] := eqVneq v 0.
  by rewrite (dual_space_zero ha) normr0 (real_seminorm_zero hN.1) mulr0.
have hNv : 0 < N v by rewrite (real_norm_positive hN.1 hN.2).
pose u := (N v)^-1 *: v.
have hNu : N u = 1 by rewrite (real_seminorm_scale hN.1) gtr0_norm ?invr_gt0 // mulVf // gt_eqF.
have hNu' : N (- u) = 1 by rewrite (real_seminorm_negate hN.1).
have hsup : has_sup [set alpha y | y in [set y | N y = 1]].
  split; first by exists (alpha u); exists u.
  exists C => _ [y hy <-]; apply: le_trans (ler_norm _) _.
  by have := hCb y; rewrite hy mulr1.
have h1 : alpha u <= dual_norm N alpha := sup_upper_bound hsup (imageP alpha hNu).
have h2 : alpha (- u) <= dual_norm N alpha := sup_upper_bound hsup (imageP alpha hNu').
rewrite -scaleN1r (dual_space_scale _ _ ha) mulN1r in h2.
have hu : alpha u = (N v)^-1 * alpha v by rewrite (dual_space_scale _ _ ha).
have hau : `|alpha u| <= dual_norm N alpha by rewrite ler_norml; apply/andP; split; lra.
rewrite hu normrM gtr0_norm ?invr_gt0 // in hau.
have hi : 0 < (N v)^-1 by rewrite invr_gt0.
have hh := ler_wpM2l (ltW hNv) hau.
rewrite mulrA mulfV ?gt_eqF // mul1r in hh.
by rewrite mulrC in hh.
Qed.

(** Source for [dual_unit_norm_nonnegative]: nonnegativity of
    the dual norm, supporting the final comparison in Federer
    2.5.12, p. 106. The dense open-unit-ball formula on p. 105
    contains the value at zero, also in the zero-dimensional case. *)
Lemma dual_unit_norm_nonnegative (D : set E)
    (hD : is_rational_dense_subspace hN D) (alpha : E -> R) :
  dual_unit_ball hN alpha -> 0 <= dual_norm N alpha.
Proof.
move=> ha.
rewrite (@dual_norm_dense_sup R E N hN D hD alpha ha).
have hz := @dense_unit_values_zero R E N hN D hD alpha.
have hs := @dense_unit_values_has_sup R E N hN D hD alpha ha.
have hh := sup_upper_bound hs hz.
by rewrite (dual_space_zero ha.1) in hh.
Qed.
End DualNorm.
