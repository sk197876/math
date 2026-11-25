(** Federer (1969), 1.7.9, p. 35: symmetry and positive definiteness follow
    from the characterising pure-tensor equation; tensor products of
    orthonormal families are orthonormal. All arguments below use an
    arbitrary bilinear form satisfying the equation; they do not inspect an
    existence construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws OrthonormalFamilies
  OrthonormalBilinearCoordinates TensorUP TensorProduct TensorSpan AlgebraTensor
  Bilinear TensorOrthonormalSpan.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [tensor_pure_orthonormal]: Federer 1.7.9,
    p. 35, products of two orthonormal families are orthonormal.
    The assertion follows from the pure-tensor equation alone. *)
Theorem tensor_pure_orthonormal (R : fieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (D : tensor_space V W -> tensor_space V W -> R)
    (hD : forall v w v' w', D (tensor_inj v w) (tensor_inj v' w') = B v v' * C w w')
    (I J : finType) (e : I -> V) (f : J -> W)
    (he : orthonormal_family B e) (hf : orthonormal_family C f) :
  orthonormal_family D (fun ij : (I * J)%type => tensor_inj (e ij.1) (f ij.2)).
Proof.
move=> [i j] [i' j']; rewrite hD he hf xpair_eqE.
by case: (i == i'); case: (j == j'); rewrite ?mulr1 ?mulr0 ?mul0r.
Qed.

(** Source for [tensor_form_symmetric]: Federer 1.7.9,
    p. 35, the unique bilinear tensor form is symmetric when
    both input inner products are symmetric. *)
Theorem tensor_form_symmetric (R : realFieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (D : tensor_space V W -> tensor_space V W -> R)
    (hD : @bilinear R _ _ R^o D)
    (hP : forall v w v' w', D (tensor_inj v w) (tensor_inj v' w') = B v v' * C w w') :
  forall x y, D x y = D y x.
Proof.
have ht : @bilinear R _ _ R^o (fun x y => D y x) by split; [exact hD.2 | exact hD.1].
apply: tensor_bilinear_ext hD ht _ => v w v' w'.
by rewrite !hP (inner_symmetric hB) (inner_symmetric hC).
Qed.

(** Source for [tensor_form_positive]: Federer 1.7.9,
    p. 35, positive definiteness of the characterised form.
    Finite orthonormal expansions reduce it to a sum of squares,
    with no finite-dimensional hypothesis on either factor. *)
Theorem tensor_form_positive (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (D : tensor_space V W -> tensor_space V W -> R)
    (hD : @bilinear R _ _ R^o D)
    (hP : forall v w v' w', D (tensor_inj v w) (tensor_inj v' w') = B v v' * C w w') x :
  (0 < D x x) = (x != 0).
Proof.
have [m [k [e [f [c [he [hf hx]]]]]]] := tensor_finite_orthonormal_expansion hB hC x.
have hO := tensor_pure_orthonormal hP he hf.
have hval : D x x = \sum_ij c ij * c ij.
  rewrite hx.
  exact (@orthonormal_bilinear_expansion R (tensor_space V W) D hD
    (Finite.clone ('I_m * 'I_k)%type _)
    (fun ij => tensor_inj (e ij.1) (f ij.2)) hO c c).
have hnon : 0 <= \sum_ij c ij * c ij.
  apply: sumr_ge0 => ij _; by rewrite -expr2 sqr_ge0.
have hzero : ((\sum_ij c ij * c ij) == 0) = (x == 0).
  apply/eqP/eqP.
  - move=> hz; rewrite hx; apply: big1 => ij _.
    have hp ab : 0 <= c ab * c ab by rewrite -expr2 sqr_ge0.
    have hh := psumr_eq0P (fun ab _ => hp ab) hz (i:=ij) isT.
    have hc : c ij = 0 by apply/eqP; rewrite -sqrf_eq0 expr2 hh eqxx.
    by rewrite hc scale0r.
  - move=> hx0; by rewrite -hval hx0 (bil0l hD).
by rewrite hval lt_def hnon andbT hzero.
Qed.
