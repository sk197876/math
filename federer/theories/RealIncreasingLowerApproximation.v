(** General order background for Federer (1969), 2.10.9, p. 175: replace any
    convergent real exponent sequence bounded below by one by a
    nondecreasing lower sequence with the same extended-real limit. Take
    infima of tails using the sealed completeness laws of 2.1.1, p. 51. This
    is supporting infrastructure, not a separately printed exponent theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import ExtendedRealBounds ExtendedRealOrderTopology ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_increasing_lower_approximation]: supporting
    tail-infimum argument for the full left limit in Federer
    2.10.9, p. 175. The resulting sequence is real-valued
    because each tail has lower bound one and contains its
    finite first term. The common limit can be infinity. *)
Theorem real_increasing_lower_approximation (R : realType) (p : nat -> R) (t : \bar R) :
  (forall n, (1<=p n)%R) -> extended_order_limit (fun n => (p n)%:E) t ->
  exists r : nat -> R, (forall n, (1<=r n)%R /\ (r n<=p n)%R) /\
    (forall n k, (n<=k)%N -> (r n<=r k)%R) /\
    extended_order_limit (fun n => (r n)%:E) t.
Proof.
move=> hp hl.
pose T n := [set a : \bar R | exists k, (n<=k)%N /\ a=(p k)%:E].
pose v n := extended_real_inf (T n).
have hlow n : 1<=v n.
  apply: extended_real_inf_greatest=> a [k [_ ->]]; exact: hp k.
have hupp n : v n<=(p n)%:E.
  apply: extended_real_inf_lower; exists n; by split.
have hv0 n : 0<=v n := le_trans lee01 (hlow n).
have hfinite n : v n \is a fin_num.
  rewrite (ge0_fin_numE (hv0 n)); exact: le_lt_trans (hupp n) (ltry (p n)).
pose r n := fine (v n).
have he n : (r n)%:E=v n by rewrite /r fineK.
exists r; split.
- move=> n; split; [move: (hlow n)|move: (hupp n)]; by rewrite -he lee_fin.
split.
- move=> n k hnk; rewrite -lee_fin !he; apply: extended_real_inf_greatest=> a [j [hkj ->]].
  apply: extended_real_inf_lower; exists j; split=> //; exact: leq_trans hnk hkj.
- split.
  + move=> a ha; have [q [haq hqt]] := @extended_rationals_order_dense R a t ha.
    have [N hN] := hl.1 (ratr q : R)%:E hqt; exists N=> n hn.
    apply: lt_le_trans haq _; rewrite he; apply: extended_real_inf_greatest=> b [k [hnk ->]].
    exact: ltW (hN k (leq_trans hn hnk)).
  + move=> b hb; have [N hN] := hl.2 b hb; exists N=> n hn.
    rewrite he; exact: le_lt_trans (hupp n) (hN n hn).
Qed.
