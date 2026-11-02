(** Federer (1969), 1.7.6, p. 33: supporting functor and scalar laws for
    exterior powers, including the sign for skewsymmetric maps. The laws
    hold over any field. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear AlgebraUP ExteriorAlgebra ExteriorGrading
  ExteriorMaps GradedComponents GradedAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_power_map_ext]: Federer 1.7.6,
    p. 33, supporting replacement of a linear map by an equal
    map when passing to an exterior power. *)
Lemma exterior_power_map_ext (R : fieldType) (V U : lmodType R)
    (f g : {linear V -> U}) : f =1 g -> forall m,
  exterior_power_map f m =1 exterior_power_map g m.
Proof.
move=> h m x; apply: val_inj.
exact (@exterior_algebra_map_eq R V U f g h (component_val x)).
Qed.

(** Source for [exterior_power_map_identity]: Federer 1.7.6,
    p. 33, supporting identity law used in the orthogonality
    and projection criteria; the underlying functor law is 1.3.1. *)
Lemma exterior_power_map_identity (R : fieldType) (V : lmodType R) m x :
  exterior_power_map (linear_id V) m x = x.
Proof. apply: val_inj; exact (@exterior_algebra_map_id R V (component_val x)). Qed.

(** Source for [exterior_power_map_composition]: Federer 1.7.6,
    p. 33, supporting composition law for the induced maps. *)
Lemma exterior_power_map_composition (R : fieldType) (V U W : lmodType R)
    (f : {linear V -> U}) (g : {linear U -> W}) m x :
  exterior_power_map g m (exterior_power_map f m x) =
    exterior_power_map (linear_comp g f) m x.
Proof. apply: val_inj; exact (@exterior_algebra_map_comp R V U W f g (component_val x)). Qed.

(** Source for [exterior_word_constant_scale]: Federer 1.7.6,
    p. 33, supporting multilinearity: scaling every factor by c
    scales a word of length m by c to the power m. *)
Lemma exterior_word_constant_scale (R : fieldType) (V U : lmodType R)
    (f : V -> U) c s :
  exterior_word [seq c *: f v | v <- s] = c ^+ (size s) *: exterior_word [seq f v | v <- s].
Proof.
elim: s => [|v s ih] /=.
- by rewrite exterior_word_nil expr0 scale1r.
- by rewrite !exterior_word_cons linearZ (bilZl (wedge_bilinear U))
    ih (bilZr (wedge_bilinear U)) scalerA exprS.
Qed.

(** Source for [exterior_power_map_scale]: Federer 1.7.6,
    p. 33, the sign formula uses this general scaling identity:
    the m-th exterior map of c times f is c^m times the m-th
    exterior map of f. *)
Theorem exterior_power_map_scale (R : fieldType) (V U : lmodType R)
    (f g : {linear V -> U}) c :
  (forall v, g v = c *: f v) -> forall m (x : exterior_power V m),
  exterior_power_map g m x = c^+m *: exterior_power_map f m x.
Proof.
move=> h m x; apply: val_inj.
change (exterior_algebra_map g (component_val x) =
  component_val (c^+m *: exterior_power_map f m x)).
rewrite linearZ.
apply: (@exterior_component_induction R V m
  (fun z => exterior_algebra_map g z = c^+m *: exterior_algebra_map f z))
  (component_homogeneous x) => [|z t hz ht|a z hz|s hs].
- by rewrite !linear0 ?scaler0.
- by rewrite !linearD hz ht ?scalerDr.
- by rewrite !linearZ hz.
- rewrite !exterior_algebra_map_word.
  have he : [seq g v | v <- s] = [seq c *: f v | v <- s].
    apply: eq_map => v; exact: h.
  by rewrite he exterior_word_constant_scale hs.
Qed.
