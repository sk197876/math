(** Federer (1969), 1.10.5, p. 48: supporting finite-dimensional norm
    comparison for mass positivity and compactness. The zero-dimensional
    case is handled separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import LinearBasis RealNormUP InnerProductUP InnerNorm
  InnerNormalization InnerMetric InnerNormedTopology InnerBoundedness
  InnerFiniteCompactness ConstrainedUnitSphere CompactMaximum FiniteNormContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LowerBound.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation M := (inner_metric_space hB).

(** Source for [finite_norm_inner_lower_bound]: Federer 1.10.5,
    p. 48, supporting finite-dimensional norm comparison. A positive
    constant bounds the auxiliary Euclidean length by a multiple of the
    given norm. The constant need not be optimal and no choice of a
    norm-defining basis is exposed in the conclusion. *)
Theorem finite_norm_inner_lower_bound : exists C : R,
  0 < C /\ forall x, inner_norm hB x <= C * N x.
Proof.
have [hn|hz] := pselect (exists u : V, u!=0).
- have [u hu] := hn.
  pose S : set M := [set x | inner_norm hB x = 1].
  have hne : S !=set0.
    exists (inner_normalize hB u); exact: inner_normalize_norm hu.
  have hcompact : compact S.
    apply: (@inner_finite_basis_boundedly_compact R V B hB n e he).
    + exact: inner_unit_sphere_closed.
    + exists 1=> x hx; by rewrite hx.
  have hc := @finite_seminorm_inner_continuous R V B hB N (proj1 hN) n e he.
  have hneg : continuous (fun x : M => (-N x : R^o)).
    move=> x; apply: continuousN; exact: hc.
  have [z [hzs hzmin]] := @continuous_compact_maximum R (Topological.clone M _) S
    (fun x : M => (-N x:R^o)) hne hcompact hneg.
  have hz0 : z!=0.
    apply/negP=> /eqP hzero.
    have hzz : inner_norm hB z=0 by rewrite hzero inner_norm0.
    have hh : (0:R) = 1 := eq_trans (esym hzz) hzs.
    by move/eqP: hh; rewrite eq_sym oner_eq0.
  have hp : 0<N z by rewrite (real_norm_positive (proj1 hN) (proj2 hN)).
  exists (N z)^-1; split; first by rewrite invr_gt0.
  move=> x; case: (eqVneq x 0)=> [->|hx].
  + by rewrite inner_norm0 (real_seminorm_zero (proj1 hN)) mulr0.
  have hux : S (inner_normalize hB x) by exact: inner_normalize_norm hx.
  have hmin := hzmin _ hux; rewrite lerN2 in hmin.
  rewrite /inner_normalize (real_seminorm_scale (proj1 hN)) normfV
    (ger0_norm (inner_norm_nonnegative hB x)) in hmin.
  rewrite (@ler_pdivlMl R (N z) (inner_norm hB x) (N x) hp).
  have hi : 0 < inner_norm hB x by rewrite inner_norm_gt0.
  rewrite (@ler_pdivlMl R (inner_norm hB x) (N z) (N x) hi) in hmin.
  by rewrite mulrC in hmin.
- exists 1; split; first exact: ltr01.
  move=> x; have hx : x=0.
    case: (eqVneq x 0)=> // hx.
    exfalso; apply: hz; by exists x.
  by rewrite hx inner_norm0 (real_seminorm_zero (proj1 hN)) mulr0.
Qed.
End LowerBound.
