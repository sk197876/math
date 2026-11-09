(** Federer (1969), 3.4.2(7), pp. 312–314: empty compact
    pieces supply harmless gaps in countable covers. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannSubspaces GrassmannAbbreviations
  RealNormUP ExtendedSupremumUP CriticalManifoldFamilyUP CriticalFlatPiecesUP
  CriticalOscillationUP CriticalOscillation CriticalDiscreteOscillation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_eta_empty_centres]: the empty-compact-set
    case of the oscillations in 3.4.2(4), pp. 310–311. Only
    the adjoined zero remains in the original quotient family. *)
Lemma critical_eta_empty_centres (R:realType) m (Y:lmodType R)
    (NY:Y->R) (Z:subspace (R_n R m)) S (f:R_n R m->Y) lambda delta:
  critical_eta NY Z S set0 f lambda delta=0%E.
Proof.
apply/eqP;rewrite eq_le;apply/andP;split;last exact:critical_eta_nonnegative.
apply:(extended_supremum_least (critical_eta_laws NY Z S set0 f lambda delta)).
move=>q [->|[x [c [_ [hc _]]]]];first exact:lexx.
exact:False_ind _ hc.
Qed.

(** Source for [critical_empty_flat_piece]: supporting empty
    gaps and the empty-cover case of 3.4.2(7), pp. 312–314.
    The original manifold with an empty compact subset belongs
    to Ψ for every function class and original zero set. *)
Lemma critical_empty_flat_piece (R:realType) m d
    (Z:G (R_n R m) d) mu (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    S C k:
  critical_manifold_family Z mu 1 S ->
  is_critical_flat_piece hNY Z mu S C k S set0.
Proof.
move=>hFamily;split;first by exists mu;split;first exact:leqnn.
split;first by move=>x.
split;first exact:compact0.
split;first by move=>x [].
move=>f hf;apply:(@eventually_zero_positive_cutoff_limit R
  (fun delta=>critical_eta NY (grassmann_val Z) S set0 f k%:R delta) 1 ltr01).
by move=>delta hdelta hSmall;rewrite critical_eta_empty_centres.
Qed.
