(** Federer (1969), 3.1.2, p. 212: missing domain has density zero and
    arbitrarily small relative remainders hold outside density-zero sets.
    These consequences use the exact approximate-limit definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric InnerNorm RealNormUP RealMetricBackground EuclideanLebesgueDimensions
  CenteredBallRelations PartialFunctionUP MeasureApproximateLimitUP MeasureSetDensity
  LocalZeroDensity EuclideanApproximateContext ApproximateDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Remainders.
Variable R : realType.
Variable n : nat.
Variable Y : lmodType R.
Variable NY : Y -> R.
Hypothesis hNY : is_real_norm NY.
Variable A : R_n R n -> Prop.
Variable f : R_n R n -> Y.
Variable a : R_n R n.
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation V := (@centered_closed_ball_relation R [the metricType R of E]).

(** Source for [approximate_remainder_quotient_graph]: exact interpretation
    of the quotient in Federer 3.1.2, p. 212. Neither an absent function
    value nor the zero denominator acquires a default value. *)
Lemma approximate_remainder_quotient_graph (L : Hom (R_n R n) Y) x q :
  partial_function_graph (approximate_remainder_quotient NY A f a L) x q <->
  A x /\ x != a /\ q=NY (f x-f a-L (x-a))/NX (x-a).
Proof.
split.
- move=> [[hx hn] <-]; by split=> //; split.
- move=> [hx [hn ->]]; by split; [split|].
Qed.

(** Source for [approximate_differential_missing_domain]: the assertion
    that the complement of A has density zero at a, Federer 3.1.2,
    p. 212, immediately following the definition. *)
Theorem approximate_differential_missing_domain (L : Hom (R_n R n) Y) :
  has_approximate_differential NY A f a L ->
  partial_function_graph (measure_set_density mu V (~` A)) a 0%E.
Proof.
move=> [_ hl].
have hd := approximate_limit_domain_density hl.
apply: (@local_zero_density_mono R [the metricType R of E] mu V (~` A)
  (~` partial_function_domain (approximate_remainder_quotient NY A f a L))
  setT a (euclidean_approximate_context R n) openT I _ hd).
move=> x _ hn [q hq]; apply: hn.
have hh := (approximate_remainder_quotient_graph L x q).1 hq.
exact: hh.1.
Qed.

(** Source for [approximate_remainder_good_points]: the complement of
    the exceptional set used in Federer 3.1.2, p. 212. A good point
    belongs to the punctured actual domain and its first-order error
    is smaller than e times its distance from a. *)
Definition approximate_remainder_good_points (L : Hom (R_n R n) Y) (e : R) : set E :=
  [set x | A x /\ x != a /\ NY (f x-f a-L (x-a)) < e*NX (x-a)].

(** Source for [approximate_remainder_good_preimage]: supporting
    equivalence between the neighborhood inverse image in 2.9.12 and
    the small-remainder set used in 3.1.2, p. 212. Nonnegativity of
    the quotient removes the absolute value around its scalar value. *)
Lemma approximate_remainder_good_preimage (L : Hom (R_n R n) Y) (e : R) :
  partial_function_preimage (approximate_remainder_quotient NY A f a L)
    [set q : real_line_metric R | mdist (0 : real_line_metric R) q<e] = approximate_remainder_good_points L e.
Proof.
apply/seteqP; split=> x.
- move=> [q [hq hqe]].
  change (is_true (`|0-q|<e)) in hqe.
  rewrite sub0r normrN in hqe.
  have [hx [hn hqval]] := (approximate_remainder_quotient_graph L x q).1 hq.
  rewrite hqval in hqe.
  have hpos : 0<NX (x-a) by rewrite inner_norm_gt0 subr_eq0.
  have hqpos : 0<=NY (f x-f a-L (x-a))/NX (x-a).
    exact: divr_ge0 (real_seminorm_nonnegative hNY.1 _) (ltW hpos).
  split=> //; split=> //.
  move: hqe; rewrite ger0_norm //.
  by rewrite ltr_pdivrMr.
- move=> [hx [hn he]].
  have hpos : 0<NX (x-a) by rewrite inner_norm_gt0 subr_eq0.
  exists (NY (f x-f a-L (x-a))/NX (x-a)); split.
  + apply: (approximate_remainder_quotient_graph L x _).2; by split=> //; split.
  change (is_true (`|0-NY (f x-f a-L (x-a))/NX (x-a)|<e)).
  rewrite sub0r normrN ger0_norm; last first.
    exact: divr_ge0 (real_seminorm_nonnegative hNY.1 _) (ltW hpos).
  by rewrite ltr_pdivrMr.
Qed.

(** Source for [approximate_remainder_exceptional_density]: the small
    exceptional sets in the uniqueness argument of Federer 3.1.2,
    p. 212. Their density is zero for every positive error threshold. *)
Theorem approximate_remainder_exceptional_density (L : Hom (R_n R n) Y) e :
  has_approximate_differential NY A f a L -> 0<e ->
  partial_function_graph (measure_set_density mu V
    (~` approximate_remainder_good_points L e)) a 0%E.
Proof.
move=> [_ hl] he.
have hn : nbhs (0 : real_line_metric R) [set q | mdist (0 : real_line_metric R) q<e].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (0 : real_line_metric R) _)).
  by exists e.
have hd := hl _ hn.
by rewrite approximate_remainder_good_preimage in hd.
Qed.
End Remainders.
