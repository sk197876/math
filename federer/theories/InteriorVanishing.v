(** Federer (1969), 1.6.5, pp. 25-26. Supporting zero cases needed
    to extend the displayed adapted-family computation to arbitrary
    multivectors. If the volume pulls back to zero on a common
    parametrising space, both the ordinary and mixed contractions
    considered here vanish. These are supporting arguments; Federer
    does not spell out the nontransverse case in the printed proof. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors InteriorNaturality CovectorProductNaturality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [right_interior_hom_natural]: Federer 1.6.5,
    pp. 25-26, use of induced maps with D_l. Supporting naturality
    of right contraction on the full exterior algebra. *)
Lemma right_interior_hom_natural (K : fieldType) (V W Z : lmodType K)
  (f : {linear V -> W}) y (a : Hom (exterior_space W) Z) :
  hom_comp (right_interior_hom (exterior_algebra_map f y) a)
    (hom_of_linear (exterior_algebra_map f)) =
  right_interior_hom y (hom_comp a (hom_of_linear (exterior_algebra_map f))).
Proof.
apply: hom_ext => x.
change (a (wedge (exterior_algebra_map f x) (exterior_algebra_map f y)) =
  a (exterior_algebra_map f (wedge x y))).
by rewrite (algebra_map_mul (exterior_algebra_map f)).
Qed.

(** Source for [mixed_interior_natural]: Federer 1.6.5,
    pp. 25-26, xi contracted by D_l eta. Supporting naturality
    when both multivectors are images of a common linear map. *)
Theorem mixed_interior_natural (K : fieldType) (h2 : (1+1 : K) != 0)
  (V W : lmodType K) (f : {linear V -> W}) x y (a : Hom (exterior_space W) K^o) :
  left_interior_hom h2 (exterior_algebra_map f x)
    (right_interior_hom (exterior_algebra_map f y) a) =
  exterior_algebra_map f
    (left_interior_hom h2 x
      (right_interior_hom y (hom_comp a (hom_of_linear (exterior_algebra_map f))))).
Proof.
by rewrite -left_interior_hom_natural right_interior_hom_natural.
Qed.

(** Source for [left_interior_map_vanishes]: Federer 1.6.5,
    pp. 25-26, supporting treatment of a nontransverse product.
    A contraction vanishes when its covector pulls back to zero
    on the space from which its multivector is mapped. *)
Lemma left_interior_map_vanishes (K : fieldType) (h2 : (1+1 : K) != 0)
  (V W : lmodType K) (f : {linear V -> W}) x (a : Hom (exterior_space W) K^o) :
  hom_comp a (hom_of_linear (exterior_algebra_map f)) = 0 ->
  left_interior_hom h2 (exterior_algebra_map f x) a = 0.
Proof.
move=> ha; rewrite -left_interior_hom_natural ha
  (bil0r (left_interior_hom_bilinear h2 V)).
exact: linear0.
Qed.

(** Source for [mixed_interior_map_vanishes]: Federer 1.6.5,
    pp. 25-26, supporting treatment of the nontransverse right
    member. If the volume restricts to zero on a common containing
    space, xi contracted by D_l eta is zero. *)
Lemma mixed_interior_map_vanishes (K : fieldType) (h2 : (1+1 : K) != 0)
  (V W : lmodType K) (f : {linear V -> W}) x y (a : Hom (exterior_space W) K^o) :
  hom_comp a (hom_of_linear (exterior_algebra_map f)) = 0 ->
  left_interior_hom h2 (exterior_algebra_map f x)
    (right_interior_hom (exterior_algebra_map f y) a) = 0.
Proof.
move=> ha; rewrite mixed_interior_natural ha
  (bil0r (right_interior_hom_bilinear V K^o))
  (bil0r (left_interior_hom_bilinear h2 V)).
exact: linear0.
Qed.

(** Source for [one_forms_wedge_zero_factor]: Federer 1.6.5,
    pp. 25-26, supporting zero-volume case. A product of one-forms
    with a zero factor is zero, independently of the position of
    that factor. *)
Lemma one_forms_wedge_zero_factor (K : fieldType) (h2 : (1+1 : K) != 0)
  (V : lmodType K) n (a : 'I_n -> A_m V K^o 1) j :
  a j = 0 -> one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) a = 0.
Proof.
move=> hj; apply: (can_inj (@form_includeK K V K^o n)).
rewrite (one_forms_wedge_include h2 (scalar_bilinear K) (@mulr1 K)) linear0 /one_forms_product.
have hz (s : seq 'I_n) : j \in s ->
  foldr (alternating_wedge h2 (scalar_bilinear K)) (coefficient_form V (1 : K^o))
    [seq form_include (a i) | i <- s] = 0.
  elim: s => [|i s ih] //=; rewrite inE => /orP [/eqP hji|hs].
  - rewrite -hji hj linear0; exact: (bil0l (alternating_wedge_bilinear h2 V (scalar_bilinear K))).
  - rewrite (ih hs); exact: (bil0r (alternating_wedge_bilinear h2 V (scalar_bilinear K))).
apply: hz; exact: mem_enum.
Qed.

(** Source for [one_form_pullback_zero]: Federer 1.6.5,
    pp. 25-26, supporting zero-volume case. A one-form pulls back
    to zero if it vanishes on the image of the map. *)
Lemma one_form_pullback_zero (K : fieldType) (V W : lmodType K)
  (f : {linear V -> W}) (a : A_m W K^o 1) :
  (forall v, one_hom a (f v) = 0) -> A_m_dual f a = 0.
Proof.
move=> ha; apply: one_hom_injective; apply: hom_ext => v.
rewrite one_homE A_m_dualE linear0 hom_zeroE.
have ht : map_tuple f [tuple v] = [tuple f v] by apply: val_inj.
by rewrite ht -one_homE ha.
Qed.

(** Source for [top_product_pullback_zero]: Federer 1.6.5,
    pp. 25-26, supporting zero-volume case. It suffices that one
    factor of the volume vanish on the parametrising space. *)
Lemma top_product_pullback_zero (K : fieldType) (h2 : (1+1 : K) != 0)
  (V W : lmodType K) (f : {linear V -> W}) n (a : 'I_n -> A_m W K^o 1) j :
  (forall v, one_hom (a j) (f v) = 0) ->
  A_m_dual f (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) a) = 0.
Proof.
move=> ha; rewrite one_forms_wedge_natural.
apply: (@one_forms_wedge_zero_factor K h2 V n _ j).
exact: one_form_pullback_zero.
Qed.

(** Source for [form_pullback_hom_zero]: Federer 1.6.5,
    pp. 25-26, supporting transfer from degree-specific forms to
    full-algebra contraction. A zero pullback gives the zero
    composed homogeneous functional. *)
Lemma form_pullback_hom_zero (K : fieldType) (V W : lmodType K)
  (f : {linear V -> W}) n (a : A_m W K^o n) :
  A_m_dual f a = 0 ->
  hom_comp (form_homogeneous a) (hom_of_linear (exterior_algebra_map f)) = 0.
Proof.
move=> ha; apply: hom_ext => x.
have hh := congr1 (fun b => form_homogeneous b x) ha.
rewrite /A_m_dual homogeneous_formK homogeneous_precomposeE linear0 hom_m_zeroE in hh.
exact: hh.
Qed.
