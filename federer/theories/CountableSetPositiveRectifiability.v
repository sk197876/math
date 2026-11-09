(** Federer (1969), 3.3.18, p. 301: actual countable
    carriers are countably rectifiable in every positive degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RectifiableSetUP
  EuclideanLipschitzRectifiableImage CountablyRectifiableUnions LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [countable_set_countably_positive_rectifiable]: the
    rectifiability of the countable carrier in the false-converse
    examples of Federer 3.3.18, p. 301. Each actual singleton
    is the image of a constant Lipschitz map from the original
    positive-dimensional Euclidean source. Actual countable union
    retains precisely the original countable set. *)
Lemma countable_set_countably_positive_rectifiable (R:realType) (X:metricType R) m (E:set X):
  countable E ->is_countably_m_rectifiable m.+1 E.
Proof.
move=>hE.
have hPoint (a:X):is_countably_m_rectifiable m.+1 [set a].
  pose P:=inner_metric_space (@euclidean_inner_productP R m.+1).
  have hLip:@is_metric_lipschitz R [the metricType R of P] X setT (fun _=>a).
    exists 1; split; first exact:ltr01.
    split; first exact:ler01.
    move=>x y _ _; rewrite mdistxx mul1r; exact:mdist_ge0.
  have hImage:(fun _:P=>a) @` setT=[set a].
    apply/seteqP; split=>x; first by move=>[y _ <-].
    move=>->; exists (0%R:P); first exact:Logic.I.
    by [].
  rewrite -hImage; exact:euclidean_lipschitz_image_countably_rectifiable hLip.
have hUnion:E=\bigcup_(a in E) [set a].
  apply/seteqP; split=>x.
  - move=>hx; by exists x.
  - by move=>[a ha ->].
rewrite hUnion; exact:countably_rectifiable_countable_union hE (fun a _=>hPoint a).
Qed.
