(** Federer (1969), 1.6.5, pp. 25-26. The two contractions as
    operations on the full exterior algebra. The second operation
    is the right member after the inverse-duality computation on
    p. 26. Bilinearity and linear dependence on the volume allow
    the basis computations to extend to all inputs. These
    definitions use only the existing public algebra interfaces. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors ProductSpaceMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Import FedererProduct.

Section Algebra.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Local Notation E := (exterior_space V).
Local Notation W := (GRing.Lmodule.clone K (V * V)%type _).

(** Source for [product_contraction_hom]: Federer 1.6.5, p. 25,
    left member of the main display. Definition on the full
    exterior algebra, with the volume written as its functional. *)
Definition product_contraction_hom (volume : Hom E K^o) (x y : E) :=
  left_interior_hom h2
    (wedge (exterior_algebra_map (P_map V) x) (exterior_algebra_map (Q_map V) y))
    (hom_comp volume (hom_of_linear (exterior_algebra_map (f_map V)))).

(** Source for [diagonal_contraction_hom]: Federer 1.6.5,
    pp. 25-26, right member after applying the inverse duality
    identity. Definition excluding the separately printed sign. *)
Definition diagonal_contraction_hom (volume : Hom E K^o) (x y : E) :=
  exterior_algebra_map (g_map V)
    (left_interior_hom h2 x (right_interior_hom y volume)).

(** Source for [product_contraction_hom_bilinear]: Federer 1.6.5,
    pp. 25-26, extension to arbitrary multivectors. Supporting
    bilinearity of the full-algebra left member. *)
Lemma product_contraction_hom_bilinear volume : bilinear (product_contraction_hom volume).
Proof.
split.
- move=> y c x z; rewrite /product_contraction_hom linearP
    (proj1 (wedge_bilinear W)) (proj1 (left_interior_hom_bilinear h2 W)); by [].
- move=> x c y z; rewrite /product_contraction_hom linearP
    (proj2 (wedge_bilinear W)) (proj1 (left_interior_hom_bilinear h2 W)); by [].
Qed.

(** Source for [diagonal_contraction_hom_bilinear]: Federer 1.6.5,
    pp. 25-26, extension to arbitrary multivectors. Supporting
    bilinearity of the full-algebra right member before its sign. *)
Lemma diagonal_contraction_hom_bilinear volume : bilinear (diagonal_contraction_hom volume).
Proof.
split.
- move=> y c x z; rewrite /diagonal_contraction_hom
    (proj1 (left_interior_hom_bilinear h2 V)) linearP; by [].
- move=> x c y z; rewrite /diagonal_contraction_hom
    (proj1 (right_interior_hom_bilinear V K^o))
    (proj2 (left_interior_hom_bilinear h2 V)) linearP; by [].
Qed.

(** Source for [product_contraction_volume_linear]: Federer 1.6.5,
    p. 25, change-of-basis observation after the main display.
    Supporting stronger fact: the left member is linear in the
    top-form functional. *)
Lemma product_contraction_volume_linear x y : linear (fun volume => product_contraction_hom volume x y).
Proof.
move=> c a b; rewrite /product_contraction_hom hom_precompose_linear
  (proj2 (left_interior_hom_bilinear h2 W)); by [].
Qed.

(** Source for [diagonal_contraction_volume_linear]: Federer 1.6.5,
    p. 25, change-of-basis observation, after the inverse-duality
    reduction on p. 26. Supporting linear dependence on the volume. *)
Lemma diagonal_contraction_volume_linear x y : linear (fun volume => diagonal_contraction_hom volume x y).
Proof.
move=> c a b; rewrite /diagonal_contraction_hom
  (proj2 (right_interior_hom_bilinear V K^o))
  (proj2 (left_interior_hom_bilinear h2 V)) linearP; by [].
Qed.
End Algebra.

(** Source for [form_pullback_hom]: Federer 1.6.5, pp. 25-26,
    the volume pulled back by f. Supporting identification of the
    degree-specific pullback and composition of its functional. *)
Lemma form_pullback_hom (K : fieldType) (V W : lmodType K)
  (f : {linear V -> W}) n (a : A_m W K^o n) :
  (form_homogeneous (A_m_dual f a) : Hom (exterior_space V) K^o) =
    hom_comp (form_homogeneous a) (hom_of_linear (exterior_algebra_map f)).
Proof.
apply: hom_ext => x.
by rewrite /A_m_dual homogeneous_formK homogeneous_precomposeE.
Qed.
