(** Supporting composition of the canonical finite-product
    identifications in Federer (1969), 2.6.5, pp. 119–120.
    All proofs use the abstract inverse and image-measure
    laws. The product law uses the sealed binary product's
    extremal characterisation. Sources and editions:
    MeasureBijectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasurePushforward ProductMeasureUP ProductMeasure
  MeasureBijectionUP ProductMeasureBijections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measure_bijection_identity]: supporting
    unchanged factor in a finite association of Federer
    2.6.5, p. 119. *)
Lemma measure_bijection_identity (R : realType) (X : choiceType) (mu : set X -> \bar R) :
  is_measure_bijection mu mu (fun x => x) (fun x => x).
Proof. constructor=> //; by apply: funext=> A. Qed.

(** Source for [measure_bijection_inverse]: supporting
    reversal of a Cartesian identification in Federer
    2.6.5, pp. 119–120. *)
Lemma measure_bijection_inverse (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (nu : set Y -> \bar R) (f : X -> Y) (g : Y -> X) :
  is_measure_bijection mu nu f g -> is_measure_bijection nu mu g f.
Proof.
move=> [hf hg he]; constructor=> //.
rewrite -he; apply: funext=> A; rewrite /measure_pushforward.
congr (mu _); apply/seteqP; split=> x /=; by rewrite hf.
Qed.

(** Source for [measure_bijection_compose]: supporting
    composition of finite product associations in Federer
    2.6.5, p. 119. *)
Lemma measure_bijection_compose (R : realType) (X Y Z : choiceType)
    (mu : set X -> \bar R) (nu : set Y -> \bar R) (xi : set Z -> \bar R)
    (f : X -> Y) (g : Y -> X) (h : Y -> Z) (k : Z -> Y) :
  is_measure_bijection mu nu f g -> is_measure_bijection nu xi h k ->
  is_measure_bijection mu xi (fun x => h (f x)) (fun z => g (k z)).
Proof.
move=> [hf hg he] [hh hk hj]; constructor.
- by move=> x; rewrite hh hf.
- by move=> z; rewrite hg hk.
- rewrite -hj -he; by apply: funext=> A.
Qed.

(** Source for [measure_bijection_product]: supporting
    replacement of either grouped factor by its identified
    version in Federer 2.6.5, pp. 119–120. No
    countability is needed for this bijection invariance. *)
Lemma measure_bijection_product (R : realType) (X Y U V : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (alpha' : set U -> \bar R) (beta' : set V -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (ha' : is_measure alpha') (hb' : is_measure beta')
    (f : X -> U) (fi : U -> X) (g : Y -> V) (gi : V -> Y) :
  is_measure_bijection alpha alpha' f fi -> is_measure_bijection beta beta' g gi ->
  is_measure_bijection (product_measure ha hb) (product_measure ha' hb')
    (cartesian_map f g) (cartesian_map fi gi).
Proof.
move=> [hf hfi he] [hg hgi hj]; constructor.
- by move=> [x y]; rewrite /cartesian_map /= hf hg.
- by move=> [u v]; rewrite /cartesian_map /= hfi hgi.
- rewrite (@product_measure_bijection R X Y U V alpha beta ha hb f fi g gi hf hfi hg hgi).
  pose rho := product_measure (measure_pushforward_is_measure f ha) (measure_pushforward_is_measure g hb).
  have hp : is_product_measure (measure_pushforward f alpha) (measure_pushforward g beta) rho :=
    product_measure_specification (measure_pushforward_is_measure f ha) (measure_pushforward_is_measure g hb).
  rewrite he hj in hp.
  exact: product_measure_unique hp (product_measure_specification ha' hb').
Qed.
