(** Supporting coordinate identifications for Federer (1969), 2.6.5, pp.
    119–120: the canonical maps between Cartesian factors and the block map
    from R^(m+n) to R^m times R^n. We prove invariance under arbitrary
    bijections directly from the maximality law of 2.6.1, p. 115. No
    countable-measurability assumption is needed for a change of coordinates
    in two factors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasurePushforward PushforwardMeasurableSets
  PushforwardMeasurabilityTransfer ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [cartesian_map]: supporting componentwise map
    for Cartesian identifications in Federer 2.6.5, pp. 119–120. *)
Definition cartesian_map (X Y U V : Type) (f : X -> U) (g : Y -> V) (p : X * Y) :=
  (f p.1,g p.2).

(** Source for [product_measure_injective_image_bound]:
    supporting extremal comparison from Federer 2.6.1,
    p. 115, for coordinate invariance in 2.6.5,
    pp. 119–120. Injectivity transfers measurable target
    rectangles back to the factor measures. *)
Lemma product_measure_injective_image_bound (R : realType) (X Y U V : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (f : X -> U) (g : Y -> V) :
  injective f -> injective g -> forall S,
  measure_pushforward (cartesian_map f g) (product_measure ha hb) S <=
  product_measure (measure_pushforward_is_measure f ha) (measure_pushforward_is_measure g hb) S.
Proof.
move=> hf hg S.
apply: (product_measure_greatest (measure_pushforward_is_measure f ha) (measure_pushforward_is_measure g hb)).
- exact: measure_pushforward_is_measure (product_measure_is_measure ha hb).
- move=> A B hA hB.
  have hpa := @measure_pushforward_preimage_measurable R X U f alpha A hf hA.
  have hpb := @measure_pushforward_preimage_measurable R Y V g beta B hg hB.
  change (product_measure ha hb ((f @^-1` A) `*` (g @^-1` B)) <=
    alpha (f @^-1` A) * beta (g @^-1` B)).
  exact: product_measure_rectangle_bound hpa hpb.
Qed.

(** Source for [product_measure_bijection]: coordinate-change invariance
    supporting the canonical Cartesian identifications of Federer 2.6.5, pp.
    119–120. Both inverse identities are explicit, including empty factor
    spaces. *)
Theorem product_measure_bijection (R : realType) (X Y U V : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : X -> U) (fi : U -> X) (g : Y -> V) (gi : V -> Y) :
  cancel f fi -> cancel fi f -> cancel g gi -> cancel gi g ->
  measure_pushforward (cartesian_map f g) (product_measure ha hb) =
  product_measure (measure_pushforward_is_measure f ha) (measure_pushforward_is_measure g hb).
Proof.
move=> hf hfi hg hgi.
pose nu := product_measure (measure_pushforward_is_measure f ha) (measure_pushforward_is_measure g hb).
have hnu := product_measure_is_measure (measure_pushforward_is_measure f ha) (measure_pushforward_is_measure g hb).
have hpreF (A : set X) : f @^-1` (fi @^-1` A) = A.
  by apply/seteqP; split=> x /=; rewrite hf.
have hpreG (B : set Y) : g @^-1` (gi @^-1` B) = B.
  by apply/seteqP; split=> y /=; rewrite hg.
have hrect A B (hA : measure_measurable alpha A) (hB : measure_measurable beta B) :
    measure_pushforward (cartesian_map fi gi) nu (A `*` B) <= alpha A * beta B.
  have hfa : measure_measurable (measure_pushforward f alpha) (fi @^-1` A).
    apply: pushforward_measurable_from_preimage; by rewrite hpreF.
  have hgb : measure_measurable (measure_pushforward g beta) (gi @^-1` B).
    apply: pushforward_measurable_from_preimage; by rewrite hpreG.
  have h := @product_measure_rectangle_bound R U V
    (measure_pushforward f alpha) (measure_pushforward g beta)
    (measure_pushforward_is_measure f ha) (measure_pushforward_is_measure g hb)
    (fi @^-1` A) (gi @^-1` B) hfa hgb.
  rewrite /measure_pushforward hpreF hpreG in h.
  exact h.
have hback T := @product_measure_greatest R X Y alpha beta ha hb
  (measure_pushforward (cartesian_map fi gi) nu)
  (measure_pushforward_is_measure (cartesian_map fi gi) hnu) hrect T.
apply: funext=> S; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@product_measure_injective_image_bound R X Y U V alpha beta ha hb f g
    (can_inj hf) (can_inj hg) S).
- have h := hback ((cartesian_map f g) @^-1` S).
  have he : (cartesian_map fi gi) @^-1` ((cartesian_map f g) @^-1` S) = S.
    by apply/seteqP; split; move=> [u v] /=; rewrite /cartesian_map /= hfi hgi.
  by rewrite /measure_pushforward he in h.
Qed.
