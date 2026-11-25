(** Federer (1969), 2.4.17, p. 90: interval structure permits approaching
    infinity through finite exponents. This supporting density argument
    excludes the separate singleton infinity case by assuming a finite
    member. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedExponentInterval FiniteExponentPart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_interval_finite_part_dense]: supporting density of
    P intersect R in P when it is nonempty, Federer 2.4.17, p. 90 Exponents
    below one are excluded as in Federer's norm domain from 2.4.12, p. 86. *)
Lemma extended_interval_finite_part_dense (R : realType) (P : set (\bar R)) (s : R) :
  is_extended_real_interval P -> (forall p, P p -> 1 <= p) -> P s%:E ->
  (P : set (extended_real_line R)) `<=` closure (finite_exponent_part P).
Proof.
move=> hP hdom hs p hp; case: p hp=> [p| |] hp.
- apply: subset_closure; split=> //; by [].
- move=> B hB; rewrite itv_nbhsE in hB; have [it [hoi hxi] hiB] := hB.
  case: it hoi hxi hiB=> [[[] a|[]]] [[] b|[]] //= _ hxi hiB;
    rewrite interval.in_itv /= ?andbT in hxi.
  + have /andP[_ hh] := hxi; by move: hh; rewrite ltNge leey.
  + have [r [har hrinf]] := @extended_rationals_order_dense R a +oo hxi.
    pose t := Order.max s (ratr r : R).
    have hst : (s <= t)%R by rewrite /t le_max lexx.
    have hrt : (ratr r <= t :> R)%R by rewrite /t le_max lexx orbT.
    exists t%:E; split.
    * split; last by [].
      exact: hP s%:E +oo t%:E hs hp hst (leey _).
    * apply: hiB; rewrite /= interval.in_itv /= andbT; apply: (lt_le_trans har); by rewrite lee_fin.
  + by move: hxi; rewrite ltNge leey.
  + exists s%:E; split; first by split.
    apply: hiB; by rewrite /= interval.in_itv.
- have hh := hdom -oo hp; by move: hh; rewrite leNgt ltNyr.
Qed.

(** Source for [extended_interval_finite_part_closure]: Supporting Federer
    2.4.17, p. 90. *)
Lemma extended_interval_finite_part_closure (R : realType) (P : set (\bar R)) (s : R) :
  is_extended_real_interval P -> (forall p, P p -> 1 <= p) -> P s%:E ->
  closure (finite_exponent_part P)=closure (P : set (extended_real_line R)).
Proof.
move=> hP hd hs; apply/seteqP; split.
- apply: closureS=> p hp; exact hp.1.
- move=> p hp; apply: closed_closure.
  apply: (@closureS (extended_real_line R) P (closure (finite_exponent_part P))) hp.
  exact: (@extended_interval_finite_part_dense R P s hP hd hs).
Qed.
