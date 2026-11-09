(** Federer (1969), 3.3.19, pp. 303–304:
    original psi_n exist, are outer measures, decrease
    under refinement, and give the actual original A
    mass one. All these assertions are proved after
    the independent literal hit-count specification. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets
  constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscTreeUP CircularDiscTreeExactCount CircularDiscLimitUP
  CircularDiscHitCount CircularDiscHitMeasureUP FiniteCellHitMeasureUP
  FiniteCellHitMeasureExistence MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section Measures.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation N:=(@FactorialDiscScales.count R).
Local Notation hs:=(@FactorialDiscScales.laws R).
Variable H:nat->{fset E}.

(** Source for [circular_disc_hit_measures_exist]: actual
    existence of all original psi_n, 3.3.19,
    p. 303. Their local component witnesses remain
    inside this opaque proof; subsequent arguments use
    only the independent original value laws. *)
Theorem circular_disc_hit_measures_exist:
  exists psi:nat->set E->\bar R,is_circular_disc_hit_measures H psi /\
    forall j,is_measure (psi j).
Proof.
have hExists j:exists mu:set E->\bar R,
    is_finite_cell_hit_measure (H j) (fun z=>metric_closed_ball z (rho j)) (rho j) mu /\
    is_measure mu.
  exact:(@finite_cell_hit_measure_exists R E E (H j)
    (fun z=>metric_closed_ball z (rho j)) (rho j)
    (ltW (@factorial_disc_radius_positive R N rho hs j))).
have [psi hPsi]:=choice hExists.
exists psi;split=>j;[exact:(hPsi j).1|exact:(hPsi j).2].
Qed.

Variable psi:nat->set E->\bar R.
Hypothesis hPsi:is_circular_disc_hit_measures H psi.

(** Source for [circular_disc_hit_is_measure]: each
    original psi_n is an outer measure in Federer's
    sense, 3.3.19, p. 303. No false
    all-set additivity assertion is inferred. *)
Lemma circular_disc_hit_is_measure j:is_measure (psi j).
Proof.
exact:(@finite_cell_hit_measure_is_measure R E E (H j)
  (fun z=>metric_closed_ball z (rho j)) (rho j) (psi j)
  (ltW (@factorial_disc_radius_positive R N rho hs j)) (hPsi j)).
Qed.

Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_hit_limit_mass_one]:
    psi_n(A)=1 for the actual original A,
    3.3.19, pp. 303–304. Actual nonempty
    pieces, the exact disc count and the conserved
    sum of actual radii discharge the equality. *)
Theorem circular_disc_hit_limit_mass_one (A:set E):
  is_circular_disc_limit H A ->forall j,psi j A= 1.
Proof.
move=>hA j;rewrite (hPsi j).
change ((#|` @circular_disc_hit_indices R H j A|%:R* rho j)%R%:E= 1).
rewrite (@circular_disc_limit_hits_all_indices R H hH A hA j)
  (@circular_disc_tree_exact_count R H hH j)
  (@factorial_disc_count_radius R N rho hs j).
exact:erefl.
Qed.

(** Source for [circular_disc_hit_refinement_decreases]:
    literal psi_n>=psi_(n+1) for every original
    test set, 3.3.19, p. 303. The
    actual child-hit count and exact radius recursion
    prove it; no limiting measure is assumed. *)
Theorem circular_disc_hit_refinement_decreases j (T:set E):psi j.+1 T<=psi j T.
Proof.
rewrite (hPsi j.+1) (hPsi j) lee_fin.
change (is_true ((#|` @circular_disc_hit_indices R H j.+1 T|%:R* rho j.+1<=
    #|` @circular_disc_hit_indices R H j T|%:R* rho j)%R)).
have hCount:=@circular_disc_hit_count_refinement R H hH j T.
have hReal:((#|` @circular_disc_hit_indices R H j.+1 T|%:R:R)<=
    #|` @circular_disc_hit_indices R H j T|%:R*(j+4)%:R)%R.
  by rewrite -natrM ler_nat.
have hPositive:=@factorial_disc_radius_positive R N rho hs j.+1.
have hScaled:=ler_wpM2r (ltW hPositive) hReal.
have hNN:(((j+4)%:R:R)!= 0)%R by rewrite pnatr_eq0 addn_eq0 andbF.
have hBudget:((j+4)%:R* rho j.+1=rho j)%R.
  by rewrite (factorial_disc_radius_step hs) mulrC divfK.
have hIdentity:(#|` @circular_disc_hit_indices R H j T|%:R*(j+4)%:R* rho j.+1=
    #|` @circular_disc_hit_indices R H j T|%:R* rho j)%R by rewrite -mulrA hBudget.
by rewrite hIdentity in hScaled.
Qed.
End Measures.
