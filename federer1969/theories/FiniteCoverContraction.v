(** Measurable splitting and the contraction factor in Federer (1969),
    2.8.15, p. 150. Of N measurable covering unions, one leaves at most
    (1-1/N) of a finite-measure target. The target itself need not be
    measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic FiniteCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_cover_loss_factor]: sigma=2 zeta/(2 zeta+1)
    in Federer 2.8.15, p. 150, written as 1-1/N for N
    color classes. The equivalence for N=m+1 is proved below. *)
Definition finite_cover_loss_factor (R : realType) (N : nat) : R := 1-(N%:R)^-1.

(** Source for [finite_cover_loss_factor_succ]: the equality
    1-1/(m+1)=m/(m+1), supporting the printed sigma in Federer 2.8.15, p.
    150 *)
Lemma finite_cover_loss_factor_succ (R : realType) (m : nat) :
  finite_cover_loss_factor R m.+1 = m%:R/m.+1%:R.
Proof.
have hm : (m%:R : R) = m.+1%:R-1 by rewrite -addn1 natrD addrK.
rewrite /finite_cover_loss_factor [in RHS]hm mulrBl divff ?pnatr_eq0 //.
by rewrite mul1r.
Qed.

(** Source for [finite_cover_loss_factor_range]: 0<sigma<1
    for the positive zeta in Federer 2.8.15, p. 150.
    The supporting assertion holds whenever the number N of
    color classes exceeds one. *)
Lemma finite_cover_loss_factor_range (R : realType) (N : nat) :
  (1 < N)%N -> 0 < finite_cover_loss_factor R N < 1.
Proof.
move=> hN.
have hNr : (1 < N%:R :> R) by rewrite ltr1n.
have hNp : (0 < N%:R :> R) := lt_trans ltr01 hNr.
rewrite /finite_cover_loss_factor; apply/andP; split.
- by rewrite subr_gt0 invf_lt1.
- by rewrite ltrBlDl ltrDr invr_gt0.
Qed.

(** Source for [finite_measurable_cover_contraction]: the last estimate in
    Federer 2.8.15, p. 150. Finite covering subadditivity supplies an
    average-size intersection, and Caratheodory splitting by its measurable
    covering union bounds the remaining outer measure. No measurability of T
    is assumed. *)
Theorem finite_measurable_cover_contraction (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (T : set X)
    (N : nat) (U : 'I_N -> set X) :
  (0 < N)%N -> (mu T < +oo)%E ->
  (forall i, measure_measurable mu (U i)) ->
  T `<=` \bigcup_(i in @setT 'I_N) U i ->
  exists i, (mu (T `\` U i) <= (finite_cover_loss_factor R N)%:E * mu T)%E.
Proof.
move=> hN hT hU hcover.
have hNr : (0 < N%:R :> R) by rewrite ltr0n.
have hTf : mu T \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm T)).
have hsubfinite B : B `<=` T -> mu B \is a fin_num.
  move=> hBT; rewrite (ge0_fin_numE (measure_nonnegative hm B)).
  exact: le_lt_trans (@measure_mono R X mu hm B T hBT) hT.
have hIf i : mu (T `&` U i) \is a fin_num.
  apply: hsubfinite; by move=> x [hx _].
have hDf i : mu (T `\` U i) \is a fin_num.
  apply: hsubfinite; by move=> x [hx _].
pose t : R := fine (mu T).
pose p (i : 'I_N) : R := fine (mu (T `&` U i)).
have hval i : mu (T `&` U i) = (p i)%:E by rewrite /p fineK.
have hcov : T `<=` \bigcup_(i in @setT 'I_N) (T `&` U i).
  move=> x hx; have [i hi hxi] := hcover x hx.
  exists i=> //; by split.
have hsum := @measure_finite_indexed_cover R X [the finType of 'I_N] mu hm T
  (fun i => T `&` U i) hcov.
have hsume : (\sum_i mu (T `&` U i))%E = (\sum_i p i)%:E.
  rewrite -sumEFin; apply: eq_bigr=> i _; exact: hval.
rewrite hsume -(fineK hTf) lee_fin in hsum.
have [i hi] := @finite_real_cover_average_piece R N p t hN hsum.
have havg : t/N%:R <= p i by rewrite ler_pdivrMr // mulrC.
pose q : R := fine (mu (T `\` U i)).
have hsplit := hU i T.
rewrite -(fineK hTf) hval -(fineK (hDf i)) -EFinD in hsplit.
have hsplitR : t = p i+q := EFin_inj hsplit.
have hineq := lerD havg (lexx q); rewrite -hsplitR in hineq.
have hrest : q <= t-t/N%:R by rewrite lerBrDl.
have heq : t-t/N%:R = finite_cover_loss_factor R N*t.
  by rewrite /finite_cover_loss_factor mulrBl mul1r [(_^-1)*t]mulrC.
exists i; rewrite -(fineK (hDf i)) -(fineK hTf) -EFinM lee_fin -heq.
exact hrest.
Qed.
