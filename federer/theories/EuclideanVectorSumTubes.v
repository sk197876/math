(** Federer (1969), 3.2.41, printed p. 278, compact
    approximation: the sum of two small neighborhoods lies
    in the corresponding neighborhood of the original sum.
    The actual open-ball tubes retain empty-source conventions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric VectorSetSum MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_vector_sum_distance_bound]: supporting
    continuity and tube control in the compact approximation of
    Federer 3.2.41, p. 278. The actual metric triangle law and
    exact translations give the two-increment distance bound. *)
Lemma euclidean_vector_sum_distance_bound (R:realType) n
    (a b c d:inner_metric_space (@euclidean_inner_productP R n)):
  mdist (a+b) (c+d)<=mdist a c+mdist b d.
Proof.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
have hTranslation (w x y:E):mdist (w+x) (w+y)=mdist x y.
  by rewrite !inner_metric_distanceE opprD addrACA subrr add0r.
have hFirst:mdist (a+b) (c+b)=mdist a c.
  by rewrite [a+b]addrC [c+b]addrC hTranslation.
have hTriangle:=metric_triangle (a+b) (c+b) (c+d).
by rewrite hFirst (hTranslation c b d) in hTriangle.
Qed.

(** Source for [euclidean_vector_sum_open_tubes]: supporting actual
    neighborhood containment in Federer 3.2.41, p. 278.
    Every image point retains original centers in A and B;
    no chosen nearest point or nonempty-source hypothesis is used. *)
Lemma euclidean_vector_sum_open_tubes (R:realType) n
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))) (r s:R):
  vector_set_sum (metric_open_thickening A r) (metric_open_thickening B s) `<=`
    metric_open_thickening (vector_set_sum A B) (r+s).
Proof.
move=> z /vector_set_sum_membership [x [y [[a ha hax] [[b hb hby] ->]]]].
exists (a+b); first exact:vector_set_sum_contains ha hb.
change (is_true (mdist (a+b) (x+y)<r+s)).
exact:(le_lt_trans (euclidean_vector_sum_distance_bound a b x y) (ltrD hax hby)).
Qed.
