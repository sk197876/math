(** Federer (1969), 3.3.19, p. 305: existence and
    elementary finite membership of the local exceptional-stage
    families. No selected global pruning is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets.
From Federer Require Import EuclideanInnerProduct InnerMetric FactorialDiscScalesSealed
  CircularDiscRefinement CircularDiscBadChildCount CircularDiscArcPruningUP PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Section Existence.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).

(** Source for [circular_disc_arc_pruned_step_membership]:
    actual finite parent, child and bad-index membership in
    the original recurrence for K_n, 3.3.19, p. 305. *)
Lemma circular_disc_arc_pruned_step_membership j (eta:partial_function E E)
    (F:{fset E}) (a b:R) (w:E):
  w \in @circular_disc_arc_pruned_step R j eta F a b <->
  exists z:E,exists k:'I_(j+4),z \in F /\
    k \in @circular_disc_bad_child_indices R j eta z a b /\
    w=circular_disc_child_center z (@FactorialDiscScales.radius R j) k.
Proof.
rewrite /circular_disc_arc_pruned_step;split.
- move=>/bigfcupP[z /andP[hz _] /imfsetP[k hk hw]].
  exists z,k;by split=>//;split.
- move=>[z [k [hz [hk ->]]]];apply/bigfcupP;exists z;first by rewrite hz.
  apply/imfsetP;by exists k.
Qed.

(** Source for [circular_disc_arc_pruning_exists]: every
    original starting level and arc have actual finite K_n
    families satisfying the independent printed recursion of
    3.3.19, p. 305. Finite recursion serves solely
    as an existence witness. *)
Theorem circular_disc_arc_pruning_exists (H:nat->{fset E})
    (eta:nat->partial_function E E) s (a b:R):
  exists K:nat->{fset E},is_circular_disc_arc_pruning H eta s a b K.
Proof.
pose K:=fix K (l:nat):{fset E}:=
  match l with
  | O=>H s
  | S k=>@circular_disc_arc_pruned_step R (s+k)%N (eta (s+k)%N) (K k) a b
  end.
exists K;constructor;by [].
Qed.
End Existence.
