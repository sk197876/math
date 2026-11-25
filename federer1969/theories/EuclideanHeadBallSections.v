(** Federer 2.10.27, p. 191: supporting unit-ball geometry for
    the real coordinate integral. Reuse the existing Euclidean
    Pythagorean norm identity, retaining tangent scalar sections. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  InnerNormedTopology EuclideanCoordinateSplit EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

(** Source for [euclidean_head_unit_ball_section]: the exact
    scalar section used in the profile computation of Federer
    2.10.27, p. 191. At a boundary base point the interval
    reduces to the single scalar zero; no section is discarded. *)
Lemma euclidean_head_unit_ball_section (R:realType) m
    (y:inner_metric_space (@euclidean_inner_productP R m)) (t:R):
  inner_norm (@euclidean_inner_productP R m) y<= 1 ->
  (inner_norm (@euclidean_inner_productP R m.+1) (euclidean_join (y,t))<= 1 <->
    `|t|<=Num.sqrt (1-(inner_norm (@euclidean_inner_productP R m) y)^+2)).
Proof.
move=> hy.
pose N:=inner_norm (@euclidean_inner_productP R m).
pose J:=inner_norm (@euclidean_inner_productP R m.+1) (euclidean_join (y,t)).
have hSq:J^+2=(N y)^+2+t^+2.
  have h:=@euclidean_join_norm R m y t;by rewrite !inner_norm_topologyE in h.
have hd:0<= 1-(N y)^+2.
  rewrite subr_ge0 -(expr1n _ 2) (ler_sqr _ _) //;
    by rewrite nnegrE ?inner_norm_nonnegative.
have ht:`|t|^+2=t^+2 by rewrite -normrX ger0_norm ?sqr_ge0.
split=> h.
- have hJ:J^+2<= 1.
    rewrite -(expr1n _ 2) (ler_sqr _ _) //;
      by rewrite nnegrE ?inner_norm_nonnegative.
  rewrite -(ler_sqr _ _) ?nnegrE ?normr_ge0 ?sqrtr_ge0 // ht sqr_sqrtr //.
  rewrite hSq in hJ.
  rewrite lerBrDl;exact:hJ.
- have hT:t^+2<= 1-(N y)^+2.
    rewrite -ht -(sqr_sqrtr hd) (ler_sqr _ _) //;
      by rewrite nnegrE ?normr_ge0 ?sqrtr_ge0.
  rewrite -(ler_sqr _ _) ?nnegrE ?inner_norm_nonnegative // expr1n hSq;lra.
Qed.

(** Source for [euclidean_head_unit_ball_empty_section]: supporting
    empty-section case for the profile identity in Federer
    2.10.27, p. 191. A scalar coordinate cannot move an exterior
    base point into the unit ball. *)
Lemma euclidean_head_unit_ball_empty_section (R:realType) m
    (y:inner_metric_space (@euclidean_inner_productP R m)) (t:R):
  1<inner_norm (@euclidean_inner_productP R m) y ->
  1<inner_norm (@euclidean_inner_productP R m.+1) (euclidean_join (y,t)).
Proof.
move=> hy.
have hSq:=@euclidean_join_norm R m y t.
rewrite !inner_norm_topologyE in hSq.
rewrite -(ltr_sqr _ _) ?nnegrE ?inner_norm_nonnegative // expr1n hSq.
have hY:1<(inner_norm (@euclidean_inner_productP R m) y)^+2.
  rewrite -(expr1n _ 2) (ltr_sqr _ _) //;
    by rewrite nnegrE ?inner_norm_nonnegative.
have ht:=sqr_ge0 t;lra.
Qed.
