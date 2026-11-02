(** Federer (1969), 2.5.5, p. 97, final sentence: define h(x)=liminf k_n(x)
    for every x. The pointwise bounds 0 <= k_n <= f make this lower limit
    finite everywhere, including outside both conull convergence loci. The
    existing sealed extended lower limit proves existence; later arguments
    use only its order laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialFunctionLimitUP
  ExtendedRealBoundsUP ExtendedLowerLimitUP ExtendedLowerLimit ExtendedRealOrderLimit RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_real_function_lower_limit_exists]: existence and
    finiteness of the h defined at the end of Federer 2.5.5, p. 97 This
    includes points exceptional for either measure, and does not assert h
    belongs to the original lattice. *)
Theorem bounded_real_function_lower_limit_exists (R : realType) (X : Type)
    (k : nat -> X -> R) (f : X -> R) :
  (forall n x, (0 <= k n x <= f x)%R) -> exists h : X -> R,
    (forall x, (0 <= h x <= f x)%R) /\
    forall x, is_extended_lower_limit (fun n => (k n x)%:E) (h x)%:E.
Proof.
move=> hb; pose s x := extended_lower_limit (fun n => (k n x)%:E).
have hlow x : 0 <= s x.
  apply: (extended_lower_limit_eventual_bound (extended_lower_limit_laws _)).
  exists 0%N=> n _; rewrite lee_fin; exact: (andP (hb n x)).1.
have hupp x : s x <= (f x)%:E.
  apply: (extended_real_supremum_least (extended_lower_limit_laws _))=> b [N hN].
  apply: le_trans (hN N (leqnn N)) _; rewrite lee_fin; exact: (andP (hb N x)).2.
have hfin x : s x \is a fin_num.
  rewrite fin_numElt; apply/andP; split.
  - exact: lt_le_trans (ltNyr (0%R : R)) (hlow x).
  - exact: le_lt_trans (hupp x) (ltry (f x)).
exists (fun x => fine (s x)); split.
- move=> x; apply/andP; split.
  + have hh := hlow x; by move: hh; rewrite -(fineK (hfin x)) lee_fin.
  + have hh := hupp x; by move: hh; rewrite -(fineK (hfin x)) lee_fin.
- move=> x; rewrite fineK //; exact: extended_lower_limit_laws.
Qed.

(** Source for [scalar_norm_sequence_order_limit]: scalar topology adapter
    for identifying the lower limit with each almost-everywhere limit in
    Federer 2.5.5, p. 97 The absolute-difference metric gives exactly the
    finite order-interval convergence used by the lower-limit laws. *)
Lemma scalar_norm_sequence_order_limit (R : realType)
    (u : nat -> real_norm_metric_space (scalar_absolute_value_norm R))
    (z : real_norm_metric_space (scalar_absolute_value_norm R)) :
  u @ \oo --> z -> extended_order_limit (fun n => (u n)%:E) z%:E.
Proof.
move=> hl; apply: real_error_extended_order_limit=> e he.
have hn : nbhs z [set y | (mdist z y < e)%R].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP z _)); by exists e.
have [K _ hK] := hl _ hn; exists K=> n hnK.
rewrite distrC; exact: hK n hnK.
Qed.

(** Source for [total_scalar_limit_locus_order_limit]: supporting graph
    identification of the two limits in Federer 2.5.5, p. 97 The selected
    sequence and prescribed limits are total real functions. *)
Lemma total_scalar_limit_locus_order_limit (R : realType) (X : Type)
    (k : nat -> X -> R) (f : X -> R) x :
  partial_function_limit_locus
    (fun n => partial_function_total (k n : X -> real_norm_metric_space (scalar_absolute_value_norm R)))
    (partial_function_total (f : X -> real_norm_metric_space (scalar_absolute_value_norm R))) x ->
  extended_order_limit (fun n => (k n x)%:E) (f x)%:E.
Proof.
move=> [u [z [hu [hz hl]]]].
have he : u=(fun n => k n x) by apply: funext=> n; exact: esym (hu n).
have hz' : f x=z := hz.
rewrite he -hz' in hl; exact: scalar_norm_sequence_order_limit hl.
Qed.
