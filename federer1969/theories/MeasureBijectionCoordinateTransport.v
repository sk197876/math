(** Supporting comparison of actual coordinate maps in Federer
    (1969), 2.6.5, pp. 119–120. These elementary
    image-measure identities let the canonical finite product
    association act on the existing Euclidean carrier. Source
    editions and the association correction: MeasureBijectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasurePushforward ProductMeasure ProductMeasureTranspose
  MeasureBijectionUP MeasureBijectionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measure_pushforward_composition]: supporting
    composition of the image measures in Federer 2.6.5,
    pp. 119–120; follows directly from inverse images. *)
Lemma measure_pushforward_composition (R : realType) (X Y Z : choiceType)
    (mu : set X -> \bar R) (f : X -> Y) (g : Y -> Z) :
  measure_pushforward g (measure_pushforward f mu) =
    measure_pushforward (fun x => g (f x)) mu.
Proof. by apply: funext=> A. Qed.

(** Source for [measure_bijection_swap]: the displayed flip
    map r and its image-measure identity in Federer 2.6.5,
    p. 119. No countability assumption is needed. *)
Lemma measure_bijection_swap (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :
  is_measure_bijection (product_measure ha hb) (product_measure hb ha)
    (fun p => (p.2,p.1)) (fun p => (p.2,p.1)).
Proof.
constructor; try by move=> [x y].
apply: funext=> A; exact: product_measure_transpose.
Qed.

(** Source for [measure_bijection_image_transport]: supporting
    passage from a coordinate-preserving finite association to
    the usual Euclidean map in Federer 2.6.5, p. 120.
    The commuting coordinate square determines the image measure. *)
Lemma measure_bijection_image_transport (R : realType) (X Y U V : choiceType)
    (mu : set X -> \bar R) (nu : set Y -> \bar R)
    (alpha : set U -> \bar R) (beta : set V -> \bar R)
    (e : X -> U) (ei : U -> X) (b : Y -> V) (bi : V -> Y)
    (f : X -> Y) (g : U -> V) :
  is_measure_bijection mu alpha e ei -> is_measure_bijection nu beta b bi ->
  measure_pushforward g alpha = beta ->
  (forall x, b (f x) = g (e x)) -> measure_pushforward f mu = nu.
Proof.
move=> he hb hg hc.
have hcomp : (fun x => bi (g (e x))) = f.
  apply: funext=> x; rewrite -hc; exact (measure_bijection_cancel hb (f x)).
have hi := measure_bijection_pushforward (measure_bijection_inverse hb).
rewrite -hg -(measure_bijection_pushforward he) !measure_pushforward_composition hcomp in hi.
exact hi.
Qed.
