(** Federer (1969), 3.2.41, printed p. 277: the base
    case of finite-family induction is the already proved
    Brunn--Minkowski inequality for the two actual boxes. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  FiniteDisjointOpenBoxFamilyUP FiniteSingletonFamilyUnion EuclideanBoxBrunnMinkowski
  EuclideanVolumeRootSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_singleton_open_box_root_sum]: supporting
    genuine singleton-family base in Federer 3.2.41, p. 277.
    The unions are exactly their original members; all box
    geometry and volume comparison have already been proved. *)
Lemma finite_singleton_open_box_root_sum (R:realType) n (I J:finType)
    (a b:I->R_n R n) (c d:J->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (H:J->set (inner_metric_space (@euclidean_inner_productP R n))) (i0:I) (j0:J):
  (0<n)%N ->(#|I|<=1)%N ->(#|J|<=1)%N ->
  is_finite_disjoint_open_box_family a b G ->
  is_finite_disjoint_open_box_family c d H ->
  euclidean_volume_root_sum_bound (\bigcup_i G i) (\bigcup_j H j).
Proof.
move=> hn hI hJ hG hH.
rewrite (@finite_singleton_index_family_union I _ G i0 hI)
  (@finite_singleton_index_family_union J _ H j0 hJ).
exact:(@euclidean_box_brunn_minkowski R n (a i0) (b i0) (c j0) (d j0)
  (G i0) (H j0) hn (finite_disjoint_open_box_law hG i0) (finite_disjoint_open_box_law hH j0)).
Qed.
