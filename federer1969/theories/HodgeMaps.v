(** Federer (1969), 1.7.8, p. 34: the two Hodge maps are defined by left
    contraction with a unit top vector and the inner-product polarity.
    Definitions below apply to every top vector; unit norm is a hypothesis
    of subsequent laws. They follow the book's explicit formula using only
    the existing abstract interior and polarity maps. Erratum: p. 1, book p.
    34 lines 29-30, concerns later pairing laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior ExteriorGrading
  AlternatingCoordinates DualityMaps InteriorMultiplication LeftInterior
  TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Hodge.
Variable R : realFieldType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable E : exterior_power V n.

(** Source for [hodge_vector]: Federer 1.7.8, p. 34,
    first definition: star(xi) is E left-interior gamma_p(xi).
    Equivalently it is D^p composed with gamma_p. *)
Definition hodge_vector p (hp : (p <= n)%N) (x : exterior_power V p) :
    exterior_power V (n-p) := D_upper h2 E hp (inner_exterior_form h2 hB x).

(** Source for [hodge_vector_linear]: Federer 1.7.8, p. 34,
    the first displayed map is linear, by linearity of both factors. *)
Lemma hodge_vector_linear p hp : linear (@hodge_vector p hp).
Proof. by move=> a x y; rewrite /hodge_vector !linearP. Qed.
HB.instance Definition _ p hp := GRing.isLinear.Build R
  (exterior_power V p) (exterior_power V (n-p)) *:%R
  (@hodge_vector p hp) (@hodge_vector_linear p hp).

(** Source for [hodge_covector]: Federer 1.7.8, p. 34,
    second definition: star(phi) is gamma_(n-p)(E left-interior phi).
    Equivalently it is gamma_(n-p) composed with D^p. *)
Definition hodge_covector p (hp : (p <= n)%N) (phi : A_m V R^o p) :
    A_m V R^o (n-p) := inner_exterior_form h2 hB (D_upper h2 E hp phi).

(** Source for [hodge_covector_linear]: Federer 1.7.8, p. 34,
    the second displayed map is linear, by linearity of both factors. *)
Lemma hodge_covector_linear p hp : linear (@hodge_covector p hp).
Proof. by move=> a x y; rewrite /hodge_covector !linearP. Qed.
HB.instance Definition _ p hp := GRing.isLinear.Build R
  (A_m V R^o p) (A_m V R^o (n-p)) *:%R
  (@hodge_covector p hp) (@hodge_covector_linear p hp).

(** Source for [hodge_polarity_diagram]: Federer 1.7.8, p. 34,
    supporting compatibility: polarity intertwines the vector and
    covector Hodge maps, directly from the two defining composites. *)
Lemma hodge_polarity_diagram p hp (x : exterior_power V p) :
  hodge_covector hp (inner_exterior_form h2 hB x) =
    inner_exterior_form h2 hB (hodge_vector hp x).
Proof. by []. Qed.
End Hodge.

(** Source for [hodge_vector_volume_scale]: Federer 1.7.8,
    p. 34, supporting orientation dependence: scaling E scales
    its Hodge maps by the same scalar, by contraction bilinearity. *)
Lemma hodge_vector_volume_scale (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (E : exterior_power V n) c p hp (x : exterior_power V p) :
  hodge_vector h2 hB (c *: E) hp x = c *: hodge_vector h2 hB E hp x.
Proof. by rewrite /hodge_vector /D_upper (bilZl (@left_interior_bilinear R h2 V p n hp)). Qed.

(** Source for [hodge_covector_volume_scale]: Federer 1.7.8,
    p. 34, covector form of the preceding orientation scaling law. *)
Lemma hodge_covector_volume_scale (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (E : exterior_power V n) c p hp (phi : A_m V R^o p) :
  hodge_covector h2 hB (c *: E) hp phi = c *: hodge_covector h2 hB E hp phi.
Proof.
by rewrite /hodge_covector /D_upper (bilZl (@left_interior_bilinear R h2 V p n hp)) linearZ.
Qed.
