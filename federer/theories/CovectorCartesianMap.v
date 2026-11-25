(** Federer (1969), 4.1.11, pp. 365–366: the original
    componentwise maps commute with separated covectors. Reuse
    the original block-map formula, contravariant composition and
    pullback product laws; no exterior construction is inspected. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations
  EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap EuclideanCartesianLinear AlternatingForms
  AlternatingDual AlternatingProduct ScalarCoefficients
  ExteriorHomogeneousProducts FormPullbackProduct DifferentialFormPullbackLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CovectorCartesianMap.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables m mu n v : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R mu).
Local Notation Z := (R_n R (m+mu)%N).
Local Notation N := (R_n R n).
Local Notation V := (R_n R v).
Local Notation W := (R_n R (n+v)%N).
Local Notation p := (@euclidean_first_block_map R m mu).
Local Notation q := (@euclidean_last_block_map R m mu).
Local Notation p' := (@euclidean_first_block_map R n v).
Local Notation q' := (@euclidean_last_block_map R n v).
Variables (A : Hom X N) (B : Hom Y V).
Local Notation L := (@euclidean_cartesian_linear R m mu n v A B).

(** Source for [covector_cartesian_map_first_composition]:
    the first target projection after D(f times g) is Df after
    the first source projection, supporting Federer 4.1.11,
    pp. 365–366, by the product differential in 3.2.23, p. 260. *)
Lemma covector_cartesian_map_first_composition :
  hom_comp p' L = hom_comp A p.
Proof.
apply: hom_ext => z.
rewrite !hom_compE euclidean_cartesian_linearE.
change ((@euclidean_block_split R n v
    (@euclidean_cartesian_map R m mu n v A B z)).1 =
  A (@euclidean_block_split R m mu z).1).
by rewrite euclidean_cartesian_map_coordinates.
Qed.

(** Source for [covector_cartesian_map_second_composition]:
    the second target projection after D(f times g) is Dg after
    the second source projection, supporting Federer 4.1.11,
    pp. 365–366, by 3.2.23, p. 260. *)
Lemma covector_cartesian_map_second_composition :
  hom_comp q' L = hom_comp B q.
Proof.
apply: hom_ext => z.
rewrite !hom_compE euclidean_cartesian_linearE.
change ((@euclidean_block_split R n v
    (@euclidean_cartesian_map R m mu n v A B z)).2 =
  B (@euclidean_block_split R m mu z).2).
by rewrite euclidean_cartesian_map_coordinates.
Qed.

(** Source for [covector_cartesian_map_product]: pulling a
    separated covector through the original componentwise map
    pulls back each factor, supporting affine naturality and
    associativity in Federer 4.1.11, pp. 365–366. Both degrees
    may be zero; the proof uses the preceding original laws. *)
Theorem covector_cartesian_map_product k l
    (alpha : A_m N R^o k) (beta : A_m V R^o l) :
  A_m_dual (hom_as_linear L)
    (form_wedge h2 (@scalar_bilinear R)
      (A_m_dual (hom_as_linear p') alpha)
      (A_m_dual (hom_as_linear q') beta)) =
  form_wedge h2 (@scalar_bilinear R)
    (A_m_dual (hom_as_linear p) (A_m_dual (hom_as_linear A) alpha))
    (A_m_dual (hom_as_linear q) (A_m_dual (hom_as_linear B) beta)).
Proof.
rewrite form_pullback_product
  -(@original_linear_pullback_composition R Z W N R^o L p' k alpha)
  -(@original_linear_pullback_composition R Z W V R^o L q' l beta)
  covector_cartesian_map_first_composition
  covector_cartesian_map_second_composition
  (@original_linear_pullback_composition R Z X N R^o p A k alpha)
  (@original_linear_pullback_composition R Z Y V R^o q B l beta).
by [].
Qed.
End CovectorCartesianMap.
