(** Federer (1969), 1.6.5, pp. 25-26, supporting treatment of the
    nontransverse case. A normalised nonzero covector gives a
    projection onto its kernel; words in that kernel are fixed,
    while a volume containing the covector pulls back to zero.
    The projection is an existence construction for this argument,
    not a replacement definition of any exterior-algebra object. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors InteriorVanishing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Projection.
Variable K : fieldType.
Variable V : lmodType K.
Variable a : Hom V K^o.
Variable d : V.
Hypothesis hd : a d = 1.

(** Source for [covector_kernel_projection]: Federer 1.6.5,
    pp. 25-26, supporting nontransverse case. Existence construction:
    v maps to v-a(v)d, where a(d)=1. *)
Definition covector_kernel_projection (v : V) := v - (a v : K) *: d.

(** Source for [covector_kernel_projection_linear]: Federer 1.6.5,
    pp. 25-26, supporting projection construction. Verification
    that this map is linear. *)
Lemma covector_kernel_projection_linear : linear covector_kernel_projection.
Proof.
move=> c x y; rewrite /covector_kernel_projection (hom_linear a)
  scalerDl scalerBr scalerA opprD.
by rewrite addrACA.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K V V *:%R
  covector_kernel_projection covector_kernel_projection_linear.

(** Source for [covector_kernel_projection_map]: Federer 1.6.5,
    pp. 25-26, supporting projection construction. Packages the
    map with its proved linearity. *)
Definition covector_kernel_projection_map : {linear V -> V} :=
  GRing.Linear.clone _ _ _ _ covector_kernel_projection _.

(** Source for [covector_kernel_projection_zero]: Federer 1.6.5,
    pp. 25-26, supporting nontransverse case. The covector vanishes
    on the image of this projection. *)
Lemma covector_kernel_projection_zero v : a (covector_kernel_projection v) = 0.
Proof.
rewrite /covector_kernel_projection linearB linearZ.
change (a v - a v * a d = 0); by rewrite hd mulr1 subrr.
Qed.

(** Source for [covector_kernel_projection_fixed]: Federer 1.6.5,
    pp. 25-26, supporting nontransverse case. The projection fixes
    every vector in the covector's kernel. *)
Lemma covector_kernel_projection_fixed v : a v = 0 -> covector_kernel_projection v = v.
Proof. by move=> hv; rewrite /covector_kernel_projection hv scale0r subr0. Qed.

(** Source for [covector_kernel_projection_word]: Federer 1.6.5,
    pp. 25-26, supporting nontransverse case. The induced exterior
    map fixes any word all of whose factors lie in the kernel. *)
Lemma covector_kernel_projection_word s :
  (forall v, v \in s -> a v = 0) ->
  exterior_algebra_map covector_kernel_projection_map (exterior_word s) = exterior_word s.
Proof.
move=> hs; rewrite exterior_algebra_map_word.
congr (exterior_word _); apply: map_id_in => v hv; exact: covector_kernel_projection_fixed (hs v hv).
Qed.
End Projection.

Section Vanishing.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable alpha : 'I_n -> A_m V K^o 1.
Variable j : 'I_n.
Variable d : V.
Hypothesis hd : one_hom (alpha j) d = 1.
Local Notation a := (one_hom (alpha j)).
Local Notation F := (covector_kernel_projection_map a d).
Local Notation volume := (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) alpha).

(** Source for [kernel_volume_pullback_zero]: Federer 1.6.5,
    pp. 25-26, supporting nontransverse case. A volume product
    containing a vanishing covector restricts to zero on its kernel. *)
Lemma kernel_volume_pullback_zero : A_m_dual F volume = 0.
Proof.
apply: (@top_product_pullback_zero K h2 V V F n alpha j) => v.
exact: covector_kernel_projection_zero.
Qed.

(** Source for [word_contraction_missing_covector]: Federer 1.6.5,
    pp. 25-26, supporting nontransverse case. If a factor of the
    volume annihilates every factor of a word, its contraction is zero. *)
Theorem word_contraction_missing_covector s :
  (forall v, v \in s -> a v = 0) ->
  left_interior_hom h2 (exterior_word s) (form_homogeneous volume) = 0.
Proof.
move=> hs; rewrite -(@covector_kernel_projection_word K V a d s hs).
apply: left_interior_map_vanishes.
exact: form_pullback_hom_zero kernel_volume_pullback_zero.
Qed.

(** Source for [mixed_words_missing_covector]: Federer 1.6.5,
    pp. 25-26, supporting nontransverse case. If a volume factor
    annihilates both words, their mixed left/right contraction is zero. *)
Theorem mixed_words_missing_covector s t :
  (forall v, v \in s -> a v = 0) ->
  (forall v, v \in t -> a v = 0) ->
  left_interior_hom h2 (exterior_word s)
    (right_interior_hom (exterior_word t) (form_homogeneous volume)) = 0.
Proof.
move=> hs ht; rewrite -(@covector_kernel_projection_word K V a d s hs)
  -(@covector_kernel_projection_word K V a d t ht).
apply: mixed_interior_map_vanishes.
exact: form_pullback_hom_zero kernel_volume_pullback_zero.
Qed.
End Vanishing.
