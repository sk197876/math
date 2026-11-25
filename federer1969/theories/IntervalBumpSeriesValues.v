(** Federer (1969), 3.2.33, p. 270: the printed
    scalar series is nonnegative, bounded and positive exactly
    on the union of its interval supports. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import RealNormUP RealOpenIntervals PositiveUnitIntervalBumpUP DenseSmallIntervalFamilyUP
  RescaledIntervalBumpValues ScalarSequenceLimitLowerBound NormSequenceClosedBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [interval_bump_series_values]: supporting the
    equalities {psi>0}= V and {g'= 0}= T minus V in
    Federer 3.2.33, p. 270. A positive summand stays
    below every later partial sum and hence below the limit.
    Off the union every summand is zero. The half-length
    geometric majorant proves a unit bound, with no positivity
    or finite bound for the limit assumed. *)
Theorem interval_bump_series_values (R:realType) (a b:nat->R) (phi psi:R->R):
  is_positive_unit_interval_bump phi ->is_dense_small_interval_family a b ->
  (forall e:R,0<e ->exists N:nat,forall M,(N<=M)%N ->forall t,
    `|(\sum_(j<M) (b j-a j)^+j.+1*phi ((t-a j)/(b j-a j)))-psi t|<e) ->
  (forall t,0<=psi t<= 1) /\forall t,
    (0<psi t <->(\bigcup_j real_open_interval (a j) (b j)) t).
Proof.
move=>hPhi hFamily hLimit.
pose d j:R:=b j-a j.
pose Q j t:R:=d j^+j.+1*phi ((t-a j)/d j).
pose P N t:R:=\sum_(j<N) Q j t.
pose q:R:= 1/2.
have hq0:0<q by rewrite /q divr_gt0 // ltr0n.
have hD j:0<d j<=q.
  apply/andP; split; first by rewrite /d subr_gt0; exact:(dense_small_interval_endpoints hFamily j).2.1.
  exact:(dense_small_interval_length hFamily j).
have hValues j t:=@rescaled_interval_bump_values R phi j (a j) (b j) t hPhi
  (dense_small_interval_endpoints hFamily j).2.1.
have hQNonnegative j t:0<=Q j t:=(andP (hValues j t).1).1.
have hQBound j t:Q j t<=q^+j.+1.
  apply:le_trans (andP (hValues j t).1).2 _.
  exact:(lerXn2r j.+1 (ltW (andP (hD j)).1) (ltW hq0) (andP (hD j)).2).
have hPNonnegative N t:0<=P N t by apply:sumr_ge0=>j _; exact:hQNonnegative.
have hPBound N t:P N t<= 1-q^+N.
  elim:N=>[|N ih]; first by rewrite /P big_ord0 expr0 subrr.
  rewrite /P big_ord_recr /= .
  have hRaw:=lerD ih (hQBound N t).
  have hStep:1-q^+N+q^+N.+1= 1-q^+N.+1 by rewrite exprS /q; field.
  by rewrite hStep in hRaw.
have hPointwise t:forall e:R,0<e ->exists N:nat,forall M,(N<=M)%N ->`|P M t-psi t|<e.
  move=>e he; have [N hN]:=hLimit e he; exists N=>M hM; exact:(hN M hM t).
have hPsiNonnegative t:0<=psi t.
  exact:(@scalar_sequence_limit_lower_bound R (fun N=>P N t) (psi t) 0 0%N
    (hPointwise t) (fun N _=>hPNonnegative N t)).
have hPsiUnit t:psi t<= 1.
  have hBound: `|psi t|<= 1.
    apply:(@norm_sequence_limit_closed_bound R R^o (fun t=>`|t|)
      (scalar_absolute_value_norm R).1 (fun N=>P N t) (psi t) 1 0%N (hPointwise t)).
    move=>N _; rewrite (ger0_norm (hPNonnegative N t)).
    have hPower:0<=q^+N:=exprn_ge0 _ (ltW hq0).
    have hB:=hPBound N t; lra.
  exact:(le_trans (ler_norm (psi t)) hBound).
split; first by move=>t; apply/andP; split; [exact:hPsiNonnegative|exact:hPsiUnit].
move=>t; split.
- move=>hPositive; apply:contrapT=>hNot.
  have hEach j:Q j t= 0.
    apply/eqP; rewrite eq_le (hQNonnegative j t) andbT leNgt; apply/negP=>hp.
    apply:hNot; exists j=>//; exact:(hValues j t).2.1 hp.
  have hOpp:psi t<= 0.
    have hAbs:`|psi t|<= 0.
      apply:(@norm_sequence_limit_closed_bound R R^o (fun t=>`|t|)
        (scalar_absolute_value_norm R).1 (fun N=>P N t) (psi t) 0 0%N (hPointwise t)).
      move=>N _.
      have hPN:P N t= 0 by rewrite /P; apply:big1=>j _; exact:hEach.
      by rewrite hPN normr0.
    exact:(le_trans (ler_norm (psi t)) hAbs).
  by have:=lt_le_trans hPositive hOpp; rewrite ltxx.
- move=>[j _ hj].
  have hPositive:0<Q j t:=(hValues j t).2.2 hj.
  have hTerm N (hN:(j.+1<=N)%N):Q j t<=P N t.
    have hjN:(j<N)%N:=hN.
    rewrite /P (bigD1 (Ordinal hjN)) //= lerDl.
    apply:sumr_ge0=>k _; exact:hQNonnegative.
  have hLower:=@scalar_sequence_limit_lower_bound R (fun N=>P N t) (psi t)
    (Q j t) j.+1 (hPointwise t) hTerm.
  exact:(lt_le_trans hPositive hLower).
Qed.
