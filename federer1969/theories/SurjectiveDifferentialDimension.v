(** Federer (1969), 3.2.9, p. 247: a
    full-target-rank differential requires n<=m. The
    dimension inequality is already part of the
    proved opaque epimorphism chart from 3.1.3(3). *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanEpimorphismChartSealed CoordinateInverseCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [surjective_euclidean_linear_dimension]:
    the dimension bound implicit in the kernel
    calculation of Federer 3.2.9, p. 247.
    It is a conclusion from actual surjectivity,
    not an additional hypothesis. *)
Lemma surjective_euclidean_linear_dimension (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)):
  (forall y,exists x,L x=y) -> (n<=m)%N.
Proof.
move=>hSurj.
exact (projT1 (@EuclideanEpimorphismChart.value R m n (hom_as_linear L) hSurj)).
Qed.

(** Source for [surjective_differential_locus_above_dimension_empty]:
    empty-locus boundary of Federer 3.2.9, p. 247.
    An actual differential cannot be onto a
    strictly larger Euclidean target. *)
Lemma surjective_differential_locus_above_dimension_empty (R:realType) m n
    (f:R_n R m->R_n R n):
  (m<n)%N -> surjective_differential_locus f=set0.
Proof.
move=>hmn; apply/seteqP; split; last by move=>x [].
move=>x [L [hL hSurj]].
have hDim:=surjective_euclidean_linear_dimension hSurj.
have hh:=leq_ltn_trans hDim hmn; by rewrite ltnn in hh.
Qed.
