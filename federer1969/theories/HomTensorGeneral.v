(** Federer 1.1.4, p. 11: the canonical transformation Phi from the
    tensor product of the algebraic dual of V with W to Hom(V,W) is
    injective in arbitrary dimensions and onto when either factor space
    has a finite basis. The existing finite-source inverse is retained. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP TensorProduct TensorMaps TensorSpan
  TensorEvaluation Hom HomTensor LinearBasis FiniteDualDimension
  FiniteBasisCriterion CoefficientCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section General.
Variable K : fieldType.
Variables V W : lmodType K.

(** Source for [tensor_Hom_evaluation]: Federer 1.1.4, p. 11, defining
    formula Phi(alpha tensor y)(x)=alpha(x)y. The tensor evaluation used
    in the injectivity proof agrees with precisely this original map. *)
Lemma tensor_Hom_evaluation (t : tensor_space (Hom V K^o) W) x :
  @tensor_evaluation K V W (Hom V K^o) (linear_id _) x
    (tensor_swap _ _ t) = @tensor_Hom K V W t x.
Proof.
elim/tensor_induction: t=> [|t u ht hu|a t ht|alpha w].
- by rewrite !linear0 hom_zeroE.
- by rewrite !linearD /= ?hom_addE ht hu.
- by rewrite !linearZ /= ?hom_scaleE ht.
- by rewrite tensor_swapE tensor_evaluationE tensor_HomE.
Qed.

(** Source for [tensor_Hom_zero_fibre]: Federer 1.1.4, p. 11,
    supporting kernel calculation for the printed monomorphism assertion.
    Finite support and finite evaluation separation are proved earlier;
    no finite-dimensional premise on V or W is introduced. *)
Lemma tensor_Hom_zero_fibre (t : tensor_space (Hom V K^o) W) :
  @tensor_Hom K V W t = 0 -> t = 0.
Proof.
move=> ht.
have hs : tensor_swap _ _ t = 0.
  apply: (@tensor_evaluation_separates K V W (Hom V K^o)
    (linear_id _) (fun x y h => h)).
  by move=> x; rewrite tensor_Hom_evaluation ht hom_zeroE.
have h := congr1 (tensor_swap W (Hom V K^o)) hs.
by rewrite tensor_swapK linear0 in h.
Qed.

(** Source for [tensor_Hom_injective]: Federer 1.1.4, p. 11,
    Phi is always a monomorphism. Arbitrary-dimensional original spaces
    and the actual canonical transformation are retained. *)
Theorem tensor_Hom_injective : injective (@tensor_Hom K V W).
Proof.
move=> t u h; apply/eqP; rewrite -subr_eq0; apply/eqP.
apply: tensor_Hom_zero_fibre.
by rewrite linearB /= h subrr.
Qed.

Variable I : finType.
Variable e : I -> W.
Hypothesis he : is_basis e.

(** Source for [Hom_tensor_finite_target]: Federer 1.1.4, p. 11,
    the basis-of-W argument: compose each dual coordinate with f and sum
    those covectors tensored with the target basis vectors. *)
Definition Hom_tensor_finite_target (f : Hom V W) :
    tensor_space (Hom V K^o) W :=
  \sum_i tensor_inj (hom_comp (dual_basis he i) f) (e i).

(** Source for [Hom_tensor_finite_targetK]: Federer 1.1.4, p. 11;
    this finite target-basis expansion is an actual preimage under Phi. *)
Lemma Hom_tensor_finite_targetK :
  cancel Hom_tensor_finite_target (@tensor_Hom K V W).
Proof.
move=> f; apply: hom_ext=> x.
rewrite /Hom_tensor_finite_target linear_sum hom_sum_coefficientsE.
under eq_bigr do rewrite tensor_HomE hom_compE.
have h := basis_coordinatesK he (f x).
rewrite basis_synthesis_finiteE in h.
exact: h.
Qed.

(** Source for [Hom_tensor_finite_target_linear]: Federer 1.1.4, p. 11;
    the finite-target inverse is linear by the original canonical map's
    unrestricted injectivity and the proved inverse law. *)
Lemma Hom_tensor_finite_target_linear : linear Hom_tensor_finite_target.
Proof.
move=> a f g; apply: tensor_Hom_injective.
by rewrite Hom_tensor_finite_targetK linearP !Hom_tensor_finite_targetK.
Qed.

(** Source for [tensor_Hom_finite_target_isomorphism]: Federer 1.1.4,
    p. 11; finite-dimensional W makes Phi an epimorphism and, by its
    unrestricted injectivity, an isomorphism, even for infinite V. *)
Theorem tensor_Hom_finite_target_isomorphism : bijective (@tensor_Hom K V W).
Proof.
exists Hom_tensor_finite_target; last exact: Hom_tensor_finite_targetK.
move=> t; apply: tensor_Hom_injective.
exact: Hom_tensor_finite_targetK.
Qed.
End General.

(** Source for [tensor_Hom_finite_factor_surjective]: Federer 1.1.4,
    p. 11, Phi is onto unless both dimensions are infinite. A finite basis
    of either original space suffices; this states exactly that alternative
    without assuming both spaces finite. *)
Theorem tensor_Hom_finite_factor_surjective (K : fieldType)
    (V W : lmodType K) :
  ((exists n (e : 'I_n -> V), is_basis e) \/
   (exists n (e : 'I_n -> W), is_basis e)) ->
  forall f : Hom V W, exists t, @tensor_Hom K V W t = f.
Proof.
move=> [[n [e he]]|[n [e he]]] f.
- by exists (Hom_tensor he f); exact: Hom_tensorK.
- by exists (Hom_tensor_finite_target he f); exact: Hom_tensor_finite_targetK.
Qed.

(** Source for [Hom_tensor_finite_target_basis_independent]: Federer
    1.1.4, p. 11, natural transformation and target-basis argument; the
    resulting inverse depends only on Phi, not the auxiliary finite basis. *)
Theorem Hom_tensor_finite_target_basis_independent (K : fieldType)
    (V W : lmodType K) (I J : finType) (e : I -> W) (d : J -> W)
    (he : is_basis e) (hd : is_basis d) (f : Hom V W) :
  Hom_tensor_finite_target he f = Hom_tensor_finite_target hd f.
Proof.
apply: tensor_Hom_injective.
by rewrite !Hom_tensor_finite_targetK.
Qed.
