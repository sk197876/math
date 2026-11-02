(** Federer (1969), 2.2.15, p. 71: the cellwise approximants h_i converge
    pointwise to f. The defining cell gives an error less than 1/i,
    independently of its integer label. These estimates use only the
    abstract laws. *)
From mathcomp Require Import all_boot all_order all_algebra ssrint boolp
  classical_sets reals topology.
From Federer Require Import RealMetricBackground RealIntegerCells RealQuantisationUP
  PointwiseLimit ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_quantisation_error]: supporting quantitative
    estimate for h_i(x) tending to f(x) in Federer 2.2.15,
    p. 71. The lower endpoint lies at most 1/i
    below f(x), with strict upper error and no boundedness
    assumption on f. *)
Lemma real_quantisation_error (R : realType) (X : Type) (f q : X -> R) k :
  is_real_quantisation f q k -> forall x,
  0 <= f x - q x /\ f x - q x < ((k.+1)%:R)^-1.
Proof.
move=> hq x; have [j [[hl hu] hval]] := hq x.
rewrite hval; split; first by rewrite subr_ge0.
rewrite intrD mulrDl /= mul1r in hu.
by rewrite ltrBlDl.
Qed.

(** Source for [real_quantisations_pointwise_limit]: direct
    pointwise convergence of h_i to f in Federer 2.2.15,
    p. 71. The reciprocal error tends to zero by
    Archimedean real arithmetic; the approximants may be any
    witnesses satisfying the abstract integer-cell laws. *)
Theorem real_quantisations_pointwise_limit (R : realType) (X : Type)
    (f : X -> real_line_metric R) (q : nat -> X -> real_line_metric R) :
  (forall k, is_real_quantisation f (q k) k) -> is_pointwise_limit q f.
Proof.
move=> hq x V hV.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP (f x) V) hV.
have [N hN] := positive_reciprocal_nat_small he.
exists N; first exact Logic.I.
move=> n hn; apply: hb.
have [hl hu] := real_quantisation_error (hq n) x.
change (mdist (f x) (q n x) < e).
rewrite real_line_metric_distanceE ger0_norm //.
have hmon : (((n.+1)%:R : R)^-1) <= (((N.+1)%:R : R)^-1).
  have hnpos : (0 : R) < n.+1%:R by rewrite ltr0n.
  have hNpos : (0 : R) < N.+1%:R by rewrite ltr0n.
  by rewrite (@lef_pV2 R _ _ hnpos hNpos) ler_nat.
exact: lt_trans hu (le_lt_trans hmon hN).
Qed.
