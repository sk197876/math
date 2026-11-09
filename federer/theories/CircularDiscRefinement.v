(** Federer (1969), 3.3.19, p. 302: the original
    child centres and finite family refinement. The actual
    closed disc belonging to a centre is introduced separately. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  CircularTrigonometrySealed CircularUnitVectors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Section Refinement.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).

(** Source for [circular_disc_child_center]: literal centre
    z+(1-1/n) r exp(2 pi i k/n) from 3.3.19,
    p. 302. Zero-based cyclic indices give the same family. *)
Definition circular_disc_child_center (z:E) (r:R) n (k:'I_n):E:=
  z+((1-n%:R^-1)*r)*:circular_unit_vector
    (2*(@CircularTrigonometry.half_period R)*k%:R/n%:R).

(** Source for [circular_disc_refinement]: union of the
    actual children of every original parent, as in the
    recursion for G_n in 3.3.19, p. 302. *)
Definition circular_disc_refinement (H:{fset E}) (r:R) n:{fset E}:=
  (\bigcup_(z<-H) [fset circular_disc_child_center z r k | k:'I_n])%fset.

(** Source for [circular_disc_refinement_membership]: exact
    parent and child-index membership in G_n, supporting
    the original recursion of 3.3.19, p. 302. *)
Lemma circular_disc_refinement_membership H r n x:
  x \in circular_disc_refinement H r n <->
  exists z:E,exists k:'I_n,z \in H /\x=circular_disc_child_center z r k.
Proof.
rewrite /circular_disc_refinement;split.
- move=>/bigfcupP[z /andP[hz _] /imfsetP[k _ hx]].
  exists z,k;by split.
- move=>[z [k [hz ->]]];apply/bigfcupP;exists z;first by rewrite hz.
  apply/imfsetP;exists k=>//.
Qed.
End Refinement.
