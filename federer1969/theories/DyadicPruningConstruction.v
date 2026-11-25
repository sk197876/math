(** Federer (1969), 2.10.47, p. 205: private existence proof for the nested
    compact sets E_j. A dependent recursion records compactness, the current
    mass and the earlier cell budgets. These budgets imply equality of all
    earlier contents by step (2). Only the final abstract pruning laws are
    exposed by the sealing module. Source context:
    DyadicCompactPruningStep.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP DyadicCubeGrid DyadicPruningUP CompactContentPruning DyadicCompactPruningStep
  RefiningCoverContent RefiningContentIntervalStability MetricDiameter MetricRealPowerCost
  MetricRealPowerMeasureUP MetricRealPowerMeasureLaws MeasureUP MeasureBasic MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section Construction.
Variables (R : realType) (n : nat) (a : R_n R n).
Let X := inner_metric_space (@euclidean_inner_productP R n).
Variable Q : forall j, dyadic_cube_indices n j -> set X.
Arguments Q j _ _ : clear implicits.
Variables (c p : R) (gamma : nat -> set X -> \bar R) (mu : set X -> \bar R).
Variables (hQ : is_dyadic_cube_grid a Q)
  (hg : forall j, is_refining_cover_content (dyadic_cube_level Q) (metric_real_diameter_cost c p) j (gamma j))
  (hmu : is_metric_real_power_measure c p mu) (hn : (0<n)%N) (hc : (0<c)%R) (hp : (0<p)%R).
Variables (A : set X) (h : nat) (hA : compact A)
  (hroot : forall x, A x -> forall l, (a l<=x l<=a l+1)%R)
  (hlevels : forall (l : 'I_n) (t : R), mu (A `&` [set x | x l=t])=0).

(** Source for [dyadic_pruning_stage_laws]: private induction
    invariant for the construction in 2.10.47, p. 205.
    The cell budgets are the inequalities immediately before
    the final identity for gamma_i(E_j). *)
Definition dyadic_pruning_stage_laws j (E : set X) :=
  [ /\ compact E, E `<=` A, gamma (h+j)%N E=gamma h A &
    forall k, (k<j)%N -> forall s,
      gamma (h+k).+1 (E `&` Q (h+k)%N s)<=metric_real_diameter_cost c p (Q (h+k)%N s)].

(** Source for [dyadic_pruning_initial_stage]: E_h=A in
    2.10.47, p. 205; A already denotes the compact
    part contained in the initial cube. *)
Lemma dyadic_pruning_initial_stage : dyadic_pruning_stage_laws 0%N A.
Proof. split=> //; by rewrite addn0. Qed.

(** Source for [dyadic_pruning_next_stage]: private successor
    choice for 2.10.47, p. 205. The cellwise choices
    and their union are proved in DyadicCompactPruningStep;
    old budgets persist by monotonicity. *)
Lemma dyadic_pruning_next_stage j (E : set X) : dyadic_pruning_stage_laws j E ->
  exists K, dyadic_pruning_stage_laws j.+1 K /\ K `<=` E.
Proof.
move=> [hEc hEA hmass hbudget].
have hmm := metric_real_power_measure_law (ltW hc) hmu.
have hcost (S : set X) : 0<=metric_real_diameter_cost c p S :=
  @metric_real_power_cost_nonnegative R c p (extended_metric_diameter S) (ltW hc).
have hgm i := refining_cover_content_measure (hg i) (fun S _=>hcost S).
have hEr x (hx : E x) := @hroot x (hEA x hx).
have hEl (l : 'I_n) (t : R) : mu (E `&` [set x | x l=t])=0.
  apply: (@measure_null_subset R X mu hmm _ (A `&` [set x | x l=t])); last exact: hlevels.
  by move=> x [hx ht]; split; first exact: hEA.
have [K [hK hKE hlocal htotal]] := @dyadic_compact_pruning_step R n a Q c p (h+j)%N
  (gamma (h+j)%N) (gamma (h+j).+1) mu E hQ (hg _) (hg _) hmu hn hc hp hEc hEr hEl.
exists K; split; last exact hKE.
split=> //.
- by move=> x hx; apply: hEA; apply: hKE.
- by rewrite addnS htotal hmass.
- move=> k hkj; case: (eqVneq k j)=> [->|hneq] s.
  + rewrite hlocal.
    have hmon : gamma (h+j)%N (E `&` Q (h+j)%N s)<=gamma (h+j)%N (Q (h+j)%N s).
      apply: (@measure_mono R X _ (hgm (h+j)%N)); by move=> x hx; exact hx.2.
    apply: le_trans hmon _.
    apply: (refining_cover_content_generator (hg _)); last exact: hcost.
    exists (h+j)%N; split=> //; by exists s.
  + have hkj' : (k<j)%N by move: hkj; rewrite ltnS leq_eqVlt (negPf hneq).
    apply: le_trans _ (hbudget k hkj' s).
    apply: (@measure_mono R X _ (hgm (h+k).+1))=> x [hx hs].
    split=> //; exact: hKE.
Qed.

(** Source for [dyadic_pruning_state]: private state carrier
    of the recursion in 2.10.47, p. 205. The
    public interface exposes the invariant rather than this
    dependent witness representation. *)
Definition dyadic_pruning_state j := {E : set X | dyadic_pruning_stage_laws j E}.

(** Source for [dyadic_pruning_state_next]: proved selection
    of the next state in 2.10.47, p. 205. *)
Definition dyadic_pruning_state_next j (s : dyadic_pruning_state j) : dyadic_pruning_state j.+1 :=
  let w := cid (dyadic_pruning_next_stage (proj2_sig s)) in
  exist _ (projT1 w) (proj1 (projT2 w)).

(** Source for [dyadic_pruning_state_next_subset]: the
    inclusion E_(j+1) in E_j from 2.10.47, p. 205. *)
Lemma dyadic_pruning_state_next_subset j (s : dyadic_pruning_state j) :
  proj1_sig (dyadic_pruning_state_next s) `<=` proj1_sig s.
Proof. exact: (proj2 (projT2 (cid (dyadic_pruning_next_stage (proj2_sig s))))). Qed.

(** Source for [dyadic_pruning_state_sequence]: private
    recursive witness for 2.10.47, p. 205. *)
Fixpoint dyadic_pruning_state_sequence j : dyadic_pruning_state j :=
  match j with
  | 0%N => exist _ A dyadic_pruning_initial_stage
  | k.+1 => dyadic_pruning_state_next (dyadic_pruning_state_sequence k)
  end.

(** Source for [dyadic_compact_pruning_exists]: existence
    of the nested compact sequence and all equalities
    gamma_i(E_j)=gamma_h(E_h) in 2.10.47, p. 205.
    The statement uses the actual power-gauge contents;
    intermediate-value and cell-additivity premises have
    been discharged by their proved lemmas. *)
Theorem dyadic_compact_pruning_exists :
  exists E, is_dyadic_compact_pruning gamma h A E.
Proof.
pose E j := proj1_sig (dyadic_pruning_state_sequence j).
have hstate j : dyadic_pruning_stage_laws j (E j) := proj2_sig (dyadic_pruning_state_sequence j).
have hnext j : E j.+1 `<=` E j := @dyadic_pruning_state_next_subset j (dyadic_pruning_state_sequence j).
have hcost (S : set X) : 0<=metric_real_diameter_cost c p S :=
  @metric_real_power_cost_nonnegative R c p (extended_metric_diameter S) (ltW hc).
exists E; split; first reflexivity.
constructor.
- by move=> j; have [hcE _ _ _] := hstate j.
- move=> i j; elim: j=> [|j IH] hij x hx.
  + have -> : i=0%N by move: hij; rewrite leqn0=> /eqP.
    exact hx.
  + case: (eqVneq i j.+1)=> [->|hneq]; first exact hx.
    have hij' : (i<=j)%N by move: hij; rewrite leq_eqVlt (negPf hneq) /= ltnS.
    exact: IH hij' x (hnext j x hx).
- move=> i j hij; have [_ _ hmass hbudget] := hstate j.
  rewrite -hmass; apply: (@refining_content_shifted_interval_stability R X
    (dyadic_cube_level Q) (metric_real_diameter_cost c p) gamma h i j (E j) hg hcost hij).
  move=> k /andP [_ hkj] S [s _ <-].
  rewrite setIC; exact: hbudget k hkj s.
Qed.
End Construction.
