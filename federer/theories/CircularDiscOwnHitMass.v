(** Federer (1969), 3.3.19, pp. 303–304:
    an original level disc has its own radius as hit
    mass, and all finer hit masses decrease. These
    support the original inside-centre alternative. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscTreeUP CircularDiscLevelPieces CircularDiscHitMeasureUP CircularDiscHitMeasureLaws
  CircularDiscHitCount FiniteCellHitMeasureUP FiniteCellHitIndicesLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section Mass.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable psi:nat->set E->\bar R.
Hypothesis hPsi:is_circular_disc_hit_measures H psi.

(** Source for [circular_disc_own_hit_indices]: exactly
    one original level disc meets itself, supporting
    the inside-centre mass estimate in 3.3.19,
    p. 303. Actual separation proves uniqueness. *)
Lemma circular_disc_own_hit_indices j (z:E):z \in H j ->
  @circular_disc_hit_indices R H j (metric_closed_ball z (rho j))=[fset z].
Proof.
move=>hz;apply/fsetP=>w.
apply/idP/idP.
- move=>hw;have [hwH [x [hxW hxZ]]]:=
    (@finite_cell_hit_indices_membership E E (H j)
      (fun c=>metric_closed_ball c (rho j)) (metric_closed_ball z (rho j)) w).1 hw.
  have hEqual:=@circular_disc_level_point_unique R H hH j x w z hwH hz hxW hxZ.
  by rewrite hEqual in_fset1 eqxx.
- rewrite in_fset1=>/eqP ->.
  apply/finite_cell_hit_indices_membership;split=>//.
  exists z;split;change (is_true ((mdist z z<=rho j)%R));rewrite mdistxx.
  all:exact:(ltW (@factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho
    (@FactorialDiscScales.laws R) j)).
Qed.

(** Source for [circular_disc_own_hit_mass]: the
    actual psi_n(B)= rho_n for B in G_n,
    used in 3.3.19, p. 303. No
    measure normalization is an additional premise. *)
Theorem circular_disc_own_hit_mass j (z:E):z \in H j ->
  psi j (metric_closed_ball z (rho j))=(rho j)%:E.
Proof.
move=>hz;rewrite (hPsi j).
change ((#|` @circular_disc_hit_indices R H j (metric_closed_ball z (rho j))|%:R* rho j)%R%:E=(rho j)%:E).
by rewrite (circular_disc_own_hit_indices hz) cardfs1 mul1r.
Qed.

(** Source for [circular_disc_hit_later_decreases]:
    every later original hit mass is at most an
    earlier one on every original test set,
    3.3.19, pp. 303–304. This is
    finite induction on the proved one-step law. *)
Lemma circular_disc_hit_later_decreases j k (T:set E):(j<= k)%N ->
  psi k T<= psi j T.
Proof.
move=>hjk;have hK:k=(j+(k-j))%N by rewrite addnC subnK.
rewrite hK;elim:(k-j)%N=>[|m ih];first by rewrite addn0.
have hIndex:(j+m.+1=(j+m).+1)%N by rewrite addnS.
rewrite hIndex.
exact:(le_trans (@circular_disc_hit_refinement_decreases R H psi hPsi hH (j+m)%N T) ih).
Qed.
End Mass.
