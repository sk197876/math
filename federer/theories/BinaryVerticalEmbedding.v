(** An actual isometric embedding into a maximum-metric product,
    supporting a project test of the spherical parenthesis in
    Federer 2.10.11, p. 176. Positive target balls have diameter
    twice their radius by the existing isometric-line theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import BinaryPrefixMetric MetricProductBackground RealMetricBackground
  EuclideanBallDiameter MetricClosedBalls MetricDiameter LipschitzUP
  NormMetricScaleContinuity BinaryPrefixCompact TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_vertical_embedding]: the project example
    sends x to (x,0) in the maximum-metric product with a line.
    This is not Federer's example; it tests the spherical variant
    printed in 2.10.11, p. 176. *)
Definition binary_vertical_embedding (R:realType) (x:binary_prefix_metric R):
  metric_product (binary_prefix_metric R) (real_line_metric R):=(x,0).

(** Source for [binary_vertical_embedding_isometry]: exact metric
    preservation by the project test map of Federer 2.10.11,
    p. 176, with no completion or ambient extension hypothesis. *)
Lemma binary_vertical_embedding_isometry (R:realType) (x y:binary_prefix_metric R):
  mdist (binary_vertical_embedding x) (binary_vertical_embedding y)=mdist x y.
Proof.
rewrite metric_product_distanceE /binary_vertical_embedding /=
  real_line_metric_distanceE subrr normr0.
by rewrite max_l //;exact:mdist_ge0.
Qed.

(** Source for [binary_vertical_embedding_injective]: univalent
    fibres of the project test map for Federer 2.10.11, p. 176. *)
Lemma binary_vertical_embedding_injective (R:realType):
  injective (@binary_vertical_embedding R).
Proof. move=> x y h;exact:(congr1 fst h). Qed.

(** Source for [binary_vertical_embedding_lipschitz]: the original
    Lipschitz hypothesis with finite bound one in the project
    test of Federer 2.10.11, p. 176. *)
Lemma binary_vertical_embedding_lipschitz (R:realType):
  is_metric_lipschitz_bound setT (@binary_vertical_embedding R) 1.
Proof.
split;first exact:ler01.
move=> x y _ _;by rewrite binary_vertical_embedding_isometry mul1r.
Qed.

(** Source for [binary_vertical_embedding_continuous]: continuity
    needed for the compact Borel image in the project test of
    Federer 2.10.11, p. 176, from its existing Lipschitz bound. *)
Lemma binary_vertical_embedding_continuous (R:realType):
  continuous (@binary_vertical_embedding R).
Proof.
apply:(@metric_fixed_lipschitz_continuous R _ _ _ 1 ler01)=>x y.
by rewrite binary_vertical_embedding_isometry mul1r.
Qed.

(** Source for [binary_vertical_image_compact]: the actual compact
    image in the project test of Federer 2.10.11, p. 176. *)
Lemma binary_vertical_image_compact (R:realType):
  compact ((@binary_vertical_embedding R) @` setT).
Proof.
exact:(continuous_compact (continuous_subspaceT
  (@binary_vertical_embedding_continuous R)) (@binary_prefix_metric_compact R)).
Qed.

(** Source for [binary_vertical_image_borel]: image measurability
    in the project test of Federer 2.10.11, p. 176, follows from
    actual compactness in the existing Hausdorff metric topology. *)
Lemma binary_vertical_image_borel (R:realType):
  borel_set ((@binary_vertical_embedding R) @` setT).
Proof.
apply:closed_borel_set;apply:compact_closed;last exact:binary_vertical_image_compact.
exact:metric_hausdorff.
Qed.

(** Source for [binary_vertical_ball_diameter]: positive target
    balls have actual diameter 2r in the project test of Federer
    2.10.11, p. 176. The proof reuses the general isometric-line
    result; no such identity is imposed on the source metric. *)
Lemma binary_vertical_ball_diameter (R:realType)
    (a:metric_product (binary_prefix_metric R) (real_line_metric R)) (r:R):
  0<=r -> extended_metric_diameter (metric_closed_ball a r)=(r+r)%:E.
Proof.
move=> hr.
pose f (t:R):metric_product (binary_prefix_metric R) (real_line_metric R):=(a.1,a.2+t).
have hf0:f 0=a by rewrite /f addr0;exact:esym (surjective_pairing a).
have hiso s t:mdist (f s) (f t)=`|s-t|.
  rewrite metric_product_distanceE /f /= mdistxx real_line_metric_distanceE.
  have he:a.2+s-(a.2+t)=s-t by ring.
  rewrite he;by rewrite max_r //;exact:normr_ge0.
exact:metric_closed_ball_diameter_from_line hr hf0 hiso.
Qed.
