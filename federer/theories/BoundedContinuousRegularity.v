(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureDerivationContext BoundedSupportContinuous
  BoundedContinuousOpenLevels DerivationOpenSupersets FunctionLatticeUP FunctionLatticeLevelFamilies
  FunctionLatticeRegularityUP SetSequenceDisjointification ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_measure_bounded_lattice_regular_pointed]:
    supporting regularity direction in the first observation of
    Federer 2.9.10, p. 157. On a nonempty metric space,
    intersect decreasing finite open approximants. They are F1 sets
    for the bounded-support continuous lattice, and reciprocal errors
    give an equal-mass F2 hull. No compactness is assumed. *)
Lemma derivation_measure_bounded_lattice_regular_pointed (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (a : X) :
  is_derivation_measure phi ->
  is_function_lattice_regular (@bounded_support_continuous_functions R X) phi.
Proof.
move=> hphi S; split; last by move=> [W [_ [_ [he hfin]]]]; rewrite he.
move=> hS; have hm := derivation_measure_law hphi.
have hSfin : phi S \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm S)).
have hex n : exists W, open W /\ S `<=` W /\ phi W<=phi S+((n.+1%:R : R)^-1)%:E.
  exact (@derivation_measure_open_superset R X phi S ((n.+1%:R : R)^-1) hphi
    ltac:(by rewrite invr_gt0 ltr0n)).
pose W n := projT1 (cid (hex n)).
have hW n : open (W n) /\ S `<=` W n /\ phi (W n)<=phi S+((n.+1%:R : R)^-1)%:E := projT2 (cid (hex n)).
pose V n := ~` set_sequence_prefix (fun n => ~` W n) n.+1.
have hV0 : V 0%N=W 0%N.
  by rewrite /V set_sequence_prefix_succ set_sequence_prefix_zero set0U setCK.
have hVs n : V n.+1=V n `&` W n.+1.
  by rewrite /V (@set_sequence_prefix_succ X (fun n => ~` W n) n.+1) setCU setCK.
have hVo n : open (V n).
  elim: n=> [|n IH]; first by rewrite hV0; exact: (hW 0%N).1.
  rewrite hVs; exact: openI IH (hW n.+1).1.
have hSV n : S `<=` V n.
  move=> x hx [k hk hnk]; exact: hnk ((hW k).2.1 x hx).
have hVW n : V n `<=` W n.
  move=> x hx; apply: contrapT=> hn; apply: hx; exists n=> //; exact: ltnSn.
have hVm n m : (n<=m)%N -> V m `<=` V n.
  move=> hnm x hx hn; apply: hx.
  exact (@set_sequence_prefix_mono X (fun n => ~` W n) n.+1 m.+1 hnm x hn).
pose B := \bigcap_n V n.
have hSB : S `<=` B by move=> x hx n _; exact: hSV n x hx.
have hBV n : B `<=` V n by move=> x hx; exact: hx n Logic.I.
have hmass : phi B<=phi S.
  rewrite -(fineK hSfin).
  apply: extended_real_reciprocal_upper_bound=> n.
  apply: le_trans (@measure_mono R X phi hm B (W n) (subset_trans (hBV n) (hVW n))) _.
  rewrite EFinD fineK //; exact: (hW n).2.2.
have heq : phi S=phi B.
  apply/eqP; rewrite eq_le hmass andbT; exact (@measure_mono R X phi hm S B hSB).
have hVfin : phi (V 0%N)< +oo.
  rewrite hV0; apply: le_lt_trans (hW 0%N).2.2 _.
  rewrite -(fineK hSfin) -EFinD; exact: ltry.
exists B; split=> //; split.
- exists V; split; first by move=> n; exact (@bounded_continuous_open_increasing_levels R X a (V n) (hVo n)).
  split=> //; split=> //.
- split=> //; by rewrite -heq.
Qed.
