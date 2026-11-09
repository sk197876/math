(** Federer (1969), 3.3.19, p. 303: actual
    original level-disc hit counts, their normalization on
    the original limit set, and the refinement upper
    bound. Every geometric counting premise is discharged. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscTreeUP CircularDiscTreeTopology CircularDiscTreeCountUpper CircularDiscTreeExactCount
  CircularDiscRefinement CircularDiscLimitUP CircularDiscDescendants FiniteCellHitMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Hits.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_hit_indices]: actual
    original discs meeting the original test set,
    as in psi_n in 3.3.19, p. 303. *)
Definition circular_disc_hit_indices j (T:set E):{fset E}:=
  finite_cell_hit_indices (H j) (fun z=>metric_closed_ball z (rho j)) T.

(** Source for [circular_disc_limit_hits_all_indices]:
    A meets every original level disc, hence its
    actual hit family is exactly G_n, supporting
    psi_n(A)=1 in 3.3.19, pp. 303–304. *)
Lemma circular_disc_limit_hits_all_indices (A:set E):
  is_circular_disc_limit H A ->forall j,circular_disc_hit_indices j A=H j.
Proof.
move=>hA j;apply/fsetP=>z;rewrite /circular_disc_hit_indices /finite_cell_hit_indices in_fset /= !inE.
apply/idP/idP;first by move=>/andP[hz _].
move=>hz.
rewrite hz /=;apply/asboolP.
have [x [hxA hxBall]]:=@circular_disc_limit_meets_every_disc R H hH A hA j z hz.
by exists x;split.
Qed.

(** Source for [circular_disc_hit_refinement_subset]: every
    actual child hit has an actual parent hit,
    supporting psi_n>=psi_(n+1) in 3.3.19,
    p. 303. Actual closed child containment supplies
    the parent; no measurable or selected-parent premise. *)
Lemma circular_disc_hit_refinement_subset j (T:set E):
  (circular_disc_hit_indices j.+1 T `<=`
    circular_disc_refinement (circular_disc_hit_indices j T) (rho j) (j+4)%N)%fset.
Proof.
apply/fsubsetP=>z;rewrite /circular_disc_hit_indices /finite_cell_hit_indices in_fset /= !inE
  =>/andP[hz /asboolP[x [hxBall hxT]]].
rewrite (circular_disc_tree_step hH) in hz.
have [w [k [hw hZ]]]:=(@circular_disc_refinement_membership R (H j) (rho j) (j+4)%N z).1 hz.
apply/circular_disc_refinement_membership;exists w,k;split=>//.
rewrite /circular_disc_hit_indices /finite_cell_hit_indices in_fset /= !inE hw /=;apply/asboolP.
exists x;split=>//;apply:(@circular_disc_child_containment R j w k);by rewrite -hZ.
Qed.

(** Source for [circular_disc_hit_count_refinement]: at
    most n actual children hit per actual parent hit,
    supporting the monotone weighted counts in
    3.3.19, p. 303. The complete original
    test set remains arbitrary. *)
Theorem circular_disc_hit_count_refinement j (T:set E):
  (#|` circular_disc_hit_indices j.+1 T|<=
    #|` circular_disc_hit_indices j T|*(j+4))%N.
Proof.
exact:leq_trans (fsubset_leq_card (@circular_disc_hit_refinement_subset j T))
  (@circular_disc_refinement_count_upper R (circular_disc_hit_indices j T) (rho j) (j+4)%N).
Qed.
End Hits.
