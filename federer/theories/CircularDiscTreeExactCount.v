(** Federer (1969), 3.3.19, p. 302: actual
    geometric disjointness gives exactly n children per
    parent and exactly n!/6 distinct original level discs. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscRefinement CircularDiscTreeUP CircularDiscTreeTopology
  CircularDiscSiblingSeparation CircularDiscTreeSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Counts.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation N:=(@FactorialDiscScales.count R).
Local Notation hs:=(@FactorialDiscScales.laws R).

(** Source for [circular_disc_child_center_injective]:
    distinct original child indices give distinct actual
    centres, supporting exact counts in 3.3.19, p. 302. *)
Lemma circular_disc_child_center_injective (z:E) (r:R) n:
  0<r ->(4<=n)%N ->injective (@circular_disc_child_center R z r n).
Proof.
move=>hr hn k l hEqual;case:(eqVneq k l)=>[hEq|hne];first exact hEq.
have hnp:(0<n%:R:>R) by rewrite ltr0n;exact:leq_trans (erefl true : (1<=4)%N) hn.
have ht:(0<r/n%:R) by rewrite divr_gt0.
have hx:metric_closed_ball (circular_disc_child_center z r k) (r/n%:R)
    (circular_disc_child_center z r k).
  change (is_true (mdist (circular_disc_child_center z r k) (circular_disc_child_center z r k)<=r/n%:R));rewrite mdistxx;exact:ltW ht.
have hy:metric_closed_ball (circular_disc_child_center z r l) (r/n%:R)
    (circular_disc_child_center z r l).
  change (is_true (mdist (circular_disc_child_center z r l) (circular_disc_child_center z r l)<=r/n%:R));rewrite mdistxx;exact:ltW ht.
have hGap:=@circular_disc_sibling_separation R z r n k l
  (circular_disc_child_center z r k) (circular_disc_child_center z r l) hr hn hne hx hy.
rewrite hEqual mdistxx in hGap.
have hFalse:=lt_trans ht hGap;by rewrite ltxx in hFalse.
Qed.

(** Source for [circular_disc_child_count]: exactly n
    original closed child discs, 3.3.19, p. 302. Actual
    centre injectivity discharges the image-count premise. *)
Lemma circular_disc_child_count (z:E) (r:R) n:
  0<r ->(4<=n)%N ->
  #|` [fset circular_disc_child_center z r k | k:'I_n]|=n.
Proof.
move=>hr hn;rewrite card_imfset;last exact:(@circular_disc_child_center_injective z r n hr hn).
by rewrite /= -cardE card_ord.
Qed.

Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_distinct_parent_child_families]:
    actual child-centre families of distinct original parents
    are disjoint, supporting the exact level count in
    3.3.19, p. 302. A common centre would be an actual
    point in both separated original parent discs. *)
Lemma circular_disc_distinct_parent_child_families j a b:
  a \in H j ->b \in H j ->a!=b ->
  [disjoint [fset circular_disc_child_center a (rho j) k | k:'I_(j+4)] &
    [fset circular_disc_child_center b (rho j) k | k:'I_(j+4)]]%fset.
Proof.
move=>ha hb hab;apply/fdisjointP=>z /imfsetP[k _ hzA];apply/negP=>/imfsetP[l _ hzB].
have hCentre:metric_closed_ball z (rho j.+1) z.
  change (is_true (mdist z z<=rho j.+1));rewrite mdistxx;exact:ltW (factorial_disc_radius_positive hs j.+1).
have hx:metric_closed_ball a (rho j) z.
  apply:(@circular_disc_child_containment R j a k);by rewrite -hzA.
have hy:metric_closed_ball b (rho j) z.
  apply:(@circular_disc_child_containment R j b l);by rewrite -hzB.
have hGap:=@circular_disc_tree_separation R H hH j a b ha hb hab z z hx hy.
rewrite mdistxx in hGap.
have hFalse:=lt_trans (@factorial_disc_radius_positive R N rho hs j) hGap.
by rewrite ltxx in hFalse.
Qed.

(** Source for [circular_disc_tree_exact_count]: exact
    original count n!/3! in 3.3.19, p. 302, expressed
    through the independently specified factorial count. *)
Theorem circular_disc_tree_exact_count j:#|` H j|=N j.
Proof.
elim:j=>[|j ih];first by rewrite (circular_disc_tree_root hH) (factorial_disc_count_root hs) cardfs1.
have hDis a b:a \in H j ->b \in H j ->a!=b ->
  [disjoint [fset circular_disc_child_center a (rho j) k | k:'I_(j+4)] &
    [fset circular_disc_child_center b (rho j) k | k:'I_(j+4)]]%fset.
  exact:circular_disc_distinct_parent_child_families.
have hAssembly:#|` H j.+1|=\sum_(a<-H j) #|` [fset circular_disc_child_center a (rho j) k | k:'I_(j+4)]|.
  rewrite (circular_disc_tree_step hH) card_fset_sum1 /circular_disc_refinement
    partition_disjoint_bigfcup;last exact:hDis.
  apply:eq_big_seq=>a ha;by rewrite -card_fset_sum1.
have hChild a:#|` [fset circular_disc_child_center a (rho j) k | k:'I_(j+4)]|=(j+4)%N.
  exact:(@circular_disc_child_count a (rho j) (j+4)%N
    (@factorial_disc_radius_positive R N rho hs j) (leq_addl j 4)).
rewrite hAssembly (factorial_disc_count_step hs).
have hSum:(\sum_(a<-H j) #|` [fset circular_disc_child_center a (rho j) k | k:'I_(j+4)]|)=
    \sum_(a<-H j) (j+4)%N.
  apply:eq_big_seq=>a _;exact:hChild.
by rewrite hSum big_seq_fsetE sum_nat_const cardT -cardE -cardfE mulnC ih.
Qed.

(** Source for [circular_disc_tree_factorial_count]: literal
    factorial count with book level n=j+3, 3.3.19,
    p. 302. All original levels n>=4 are included. *)
Corollary circular_disc_tree_factorial_count j:(#|` H j|*6=(j+3)`!)%N.
Proof. rewrite (@circular_disc_tree_exact_count j);exact:(@factorial_disc_count_factorial R N rho hs j). Qed.
End Counts.
