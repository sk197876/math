(** Federer (1969), 2.2.15, p. 71, target sufficiency: reciprocal error
    implies pointwise convergence of the abstract countable approximants. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import PointwiseLimit CountableBorelApproximationUP ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [countable_borel_approximations_converge]: supporting
    limiting step for Federer 2.2.15, p. 71.
    The source need not be separable or complete; the bound
    comes directly from the abstract approximation laws. *)
Lemma countable_borel_approximations_converge (R : realType) (X : topologicalType)
    (Y : metricType R) (f : X -> Y) (y : nat -> Y) (q : nat -> X -> nat) :
  is_countable_borel_approximation f y q ->
  is_pointwise_limit (fun k => y \o q k) f.
Proof.
move=> h x V hV.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP (f x) V) hV.
have [N hN] := positive_reciprocal_nat_small he.
exists N; first exact Logic.I.
move=> n hn; apply: hb.
have hd := countable_approximation_error h n x.
have hmon : (((n.+1)%:R : R)^-1) <= (((N.+1)%:R : R)^-1).
  have hnpos : (0 : R) < n.+1%:R by rewrite ltr0n.
  have hNpos : (0 : R) < N.+1%:R by rewrite ltr0n.
  by rewrite (@lef_pV2 R _ _ hnpos hNpos) ler_nat.
exact: lt_trans hd (le_lt_trans hmon hN).
Qed.
