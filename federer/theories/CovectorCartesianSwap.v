(** Federer (1969), 4.1.8, p. 361: pulling an
    original separated form through w(x,y)=(y,x)
    interchanges the factors with sign (-1)^(kl).
    Reuse the original contravariant composition,
    pullback product and graded commutation laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations
  EuclideanBlockLinearMaps EuclideanCartesianSwapLinear AlternatingForms AlternatingDual
  AlternatingProduct ScalarCoefficients ExteriorHomogeneousProducts ComassWedgeSymmetry
  FormPullbackProduct DifferentialFormPullbackLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CovectorCartesianSwap.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation W := (R_n R (n+m)).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Local Notation p' := (@euclidean_first_block_map R n m).
Local Notation q' := (@euclidean_last_block_map R n m).
Local Notation swap := (@euclidean_cartesian_swap_map R m n).

(** Source for [covector_cartesian_swap_first_composition]:
    the first target projection after w is the
    second source projection, supporting Federer 4.1.8,
    p. 361, as an equality of actual linear maps. *)
Lemma covector_cartesian_swap_first_composition:hom_comp p' swap=q.
Proof. apply:hom_ext=>x;exact:euclidean_cartesian_swap_first. Qed.

(** Source for [covector_cartesian_swap_second_composition]:
    the second target projection after w is the
    first source projection, supporting Federer 4.1.8,
    p. 361, as an equality of actual linear maps. *)
Lemma covector_cartesian_swap_second_composition:hom_comp q' swap=p.
Proof. apply:hom_ext=>x;exact:euclidean_cartesian_swap_last. Qed.

(** Source for [covector_cartesian_swap_product]: the original
    pulled-back separated covector has sign (-1)^(kl),
    supporting the signed interchange in Federer 4.1.8,
    p. 361, by the original graded commutation
    and contravariant composition laws. *)
Theorem covector_cartesian_swap_product k l (alpha:A_m Y R^o k) (beta:A_m X R^o l):
  A_m_dual (hom_as_linear swap)
    (form_wedge h2 (@scalar_bilinear R)
      (A_m_dual (hom_as_linear p') alpha) (A_m_dual (hom_as_linear q') beta))=
  (-1:R)^+(k * l)*:form_reindex (addnC l k)
    (form_wedge h2 (@scalar_bilinear R)
      (A_m_dual (hom_as_linear p) beta) (A_m_dual (hom_as_linear q) alpha)).
Proof.
rewrite form_pullback_product
  -(@original_linear_pullback_composition R Z W Y R^o swap p' k alpha)
  -(@original_linear_pullback_composition R Z W X R^o swap q' l beta)
  covector_cartesian_swap_first_composition covector_cartesian_swap_second_composition.
exact:form_wedge_reindex_swap.
Qed.
End CovectorCartesianSwap.
