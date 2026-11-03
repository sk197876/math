(** Federer (1969), 3.2.41, printed p. 277, finite-family
    proof: strong induction on card(G)+card(H) proves the actual
    Brunn--Minkowski inequality for every nonempty pair of finite
    disjoint proper open-box unions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  FiniteDisjointOpenBoxFamilyUP FiniteOpenBoxInductionUP FiniteOpenBoxInductionStep
  FiniteOpenBoxSingletonBrunnMinkowski EuclideanVolumeRootSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope nat_scope.

(** Source for [finite_open_box_brunn_minkowski]: direct full
    elementary finite-family case in Federer 3.2.41, p. 277.
    The cut step is invoked only with proved strict cardinal
    descent. Symmetry handles a singleton first family; two
    singleton families reduce to the actual box theorem.
    No induction, cut, volume or finite-family inequality is assumed. *)
Theorem finite_open_box_brunn_minkowski (R:realType) n:
  0<n ->forall (I J:finType) (a b:I->R_n R n) (c d:J->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (H:J->set (inner_metric_space (@euclidean_inner_productP R n))),
    is_finite_disjoint_open_box_family a b G ->
    is_finite_disjoint_open_box_family c d H ->
    (\bigcup_i G i) !=set0 ->(\bigcup_j H j) !=set0 ->
    euclidean_volume_root_sum_bound (\bigcup_i G i) (\bigcup_j H j).
Proof.
move=> hn.
have hAll:forall N,finite_open_box_smaller_pair_bounds R n N.
  move=> N; elim/ltn_ind:N=> N hInd.
  rewrite /finite_open_box_smaller_pair_bounds.
  move=> I J a b c d G H hSize hG hH hGNe hHNe.
  have hLess:finite_open_box_smaller_pair_bounds R n (#|I|+#|J|):=hInd _ hSize.
  case:(ltnP 1 #|I|)=>[hI|hI].
  - exact:(@finite_open_box_induction_step R n I J a b c d G H hn hLess hG hH hI hGNe hHNe).
  case:(ltnP 1 #|J|)=>[hJ|hJ].
  - have hLessSwap:finite_open_box_smaller_pair_bounds R n (#|J|+#|I|).
      by rewrite addnC.
    apply:(@euclidean_volume_root_sum_symmetric R n (\bigcup_i G i) (\bigcup_j H j)).2.
    exact:(@finite_open_box_induction_step R n J I c d a b H G hn hLessSwap hH hG hJ hHNe hGNe).
  - have [x [i0 _ hi0]]:=hGNe.
    have [y [j0 _ hj0]]:=hHNe.
    exact:(@finite_singleton_open_box_root_sum R n I J a b c d G H i0 j0 hn hI hJ hG hH).
move=> I J a b c d G H hG hH hGNe hHNe.
exact:(hAll (#|I|+#|J|).+1 I J a b c d G H (ltnSn _) hG hH hGNe hHNe).
Qed.
