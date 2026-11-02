(** Federer (1969), 2.2.5, p. 62, the supremum and infimum formulas in the
    definition. These formulas and their strict-approximation consequences
    are derived from the abstract order laws. Source context:
    RadonMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealBounds MeasureUP MeasureBasic RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_inner_formula]: Federer 2.2.5,
    p. 62, the measure of an open V is the supremum of measures
    of compact subsets of V. Direct recovery of the printed formula. *)
Lemma radon_inner_formula (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_radon_measure mu) V : open V ->
  mu V = extended_real_sup [set t | exists K, compact K /\ K `<=` V /\ t = mu K].
Proof.
move=> hV; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@radon_inner_least R T mu hr V hV)=> K hK hKV.
  apply: extended_real_sup_upper; exists K; by split=> //; split.
- apply: extended_real_sup_least=> t [K [hK [hKV ->]]].
  exact: (@measure_mono R _ mu hm K V hKV).
Qed.

(** Source for [radon_outer_formula]: Federer 2.2.5,
    p. 62, the measure of every A is the infimum of measures
    of open supersets of A. Direct recovery of the printed formula. *)
Lemma radon_outer_formula (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_radon_measure mu) A :
  mu A = extended_real_inf [set t | exists V, open V /\ A `<=` V /\ t = mu V].
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: extended_real_inf_greatest=> t [V [hV [hAV ->]]].
  exact: (@measure_mono R _ mu hm A V hAV).
- apply: (radon_outer_greatest hr)=> V hV hAV.
  apply: extended_real_inf_lower; exists V; by split=> //; split.
Qed.

(** Source for [radon_inner_strict_approximation]: Federer
    2.2.5, pp. 62-63, supporting choice of compact sets with
    measure arbitrarily close to that of an open set from below,
    used in the compact approximation proof on p. 63. *)
Lemma radon_inner_strict_approximation (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hr : is_radon_measure mu) V c :
  open V -> c < mu V -> exists K, compact K /\ K `<=` V /\ c < mu K.
Proof.
move=> hV hc; case: (pselect (exists K, compact K /\ K `<=` V /\ c < mu K))=> h; first exact h.
exfalso; have hub : mu V <= c.
  apply: (@radon_inner_least R T mu hr V hV)=> K hK hKV.
  rewrite leNgt; apply/negP=> hk; apply: h; exists K; by split=> //; split.
by move: hc; rewrite ltNge hub.
Qed.

(** Source for [radon_outer_strict_approximation]: Federer
    2.2.5, pp. 62-63, supporting choice of open supersets
    with measure below any strict upper bound on the original measure. *)
Lemma radon_outer_strict_approximation (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hr : is_radon_measure mu) A c :
  mu A < c -> exists V, open V /\ A `<=` V /\ mu V < c.
Proof.
move=> hc; case: (pselect (exists V, open V /\ A `<=` V /\ mu V < c))=> h; first exact h.
exfalso; have hlb : c <= mu A.
  apply: (radon_outer_greatest hr)=> V hV hAV.
  rewrite leNgt; apply/negP=> hv; apply: h; exists V; by split=> //; split.
by move: hc; rewrite ltNge hlb.
Qed.
