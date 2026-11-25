(** Federer (1969), 4.1.8, p. 361: pullback
    through the original three-factor association preserves
    the triple exterior product. Reuse the original
    contravariant composition and associative alternating
    product of 1.4.2, p. 18. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear GrassmannAbbreviations
  EuclideanBlockLinearMaps EuclideanDimensionCastLinear EuclideanCartesianReassociation
  AlternatingForms Alternating AlternatingDual AlternatingProduct ScalarCoefficients ExteriorHomogeneousProducts
  ComassWedgeSymmetry FormPullbackProduct DifferentialFormPullbackLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CovectorCartesianReassociation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n v:nat.
Local Notation X := (R_n R ((m+n)+v)).
Local Notation Y := (R_n R (m+(n+v))).
Local Notation M := (R_n R m).
Local Notation N := (R_n R n).
Local Notation V := (R_n R v).
Local Notation MN := (R_n R (m+n)).
Local Notation NV := (R_n R (n+v)).
Local Notation assoc := (@euclidean_dimension_cast_map R ((m+n)+v)%N (m+(n+v))%N
  (esym (addnA m n v))).
Local Notation pL := (@euclidean_first_block_map R (m+n) v).
Local Notation qL := (@euclidean_last_block_map R (m+n) v).
Local Notation pA := (@euclidean_first_block_map R m n).
Local Notation qB := (@euclidean_last_block_map R m n).
Local Notation pR := (@euclidean_first_block_map R m (n+v)).
Local Notation qR := (@euclidean_last_block_map R m (n+v)).
Local Notation pB := (@euclidean_first_block_map R n v).
Local Notation qC := (@euclidean_last_block_map R n v).

(** Source for [covector_reassociation_first_composition]: natural
    association retains the first original projection, supporting
    Federer 4.1.8, p. 361. *)
Lemma covector_reassociation_first_composition:hom_comp pR assoc=hom_comp pA pL.
Proof. apply:hom_ext=>x;exact:euclidean_cartesian_reassociate_first. Qed.

(** Source for [covector_reassociation_middle_composition]: natural
    association retains the second original projection, supporting
    Federer 4.1.8, p. 361. *)
Lemma covector_reassociation_middle_composition:
  hom_comp pB (hom_comp qR assoc)=hom_comp qB pL.
Proof. apply:hom_ext=>x;exact:euclidean_cartesian_reassociate_middle. Qed.

(** Source for [covector_reassociation_last_composition]: natural
    association retains the third original projection, supporting
    Federer 4.1.8, p. 361. *)
Lemma covector_reassociation_last_composition:hom_comp qC (hom_comp qR assoc)=qL.
Proof. apply:hom_ext=>x;exact:euclidean_cartesian_reassociate_last. Qed.

(** Source for [covector_cartesian_reassociation_product]: the
    original pulled-back triple separated covector is exactly
    its other association, supporting product associativity in
    Federer 4.1.8, p. 361, without a sign
    or any positive-degree assumption. *)
Theorem covector_cartesian_reassociation_product k l r
    (alpha:A_m M R^o k) (beta:A_m N R^o l) (gamma:A_m V R^o r):
  A_m_dual (hom_as_linear assoc)
    (form_wedge h2 (@scalar_bilinear R) (A_m_dual (hom_as_linear pR) alpha)
      (A_m_dual (hom_as_linear qR)
        (form_wedge h2 (@scalar_bilinear R) (A_m_dual (hom_as_linear pB) beta)
          (A_m_dual (hom_as_linear qC) gamma))))=
  form_reindex (esym (addnA k l r))
    (form_wedge h2 (@scalar_bilinear R)
      (A_m_dual (hom_as_linear pL)
        (form_wedge h2 (@scalar_bilinear R) (A_m_dual (hom_as_linear pA) alpha)
          (A_m_dual (hom_as_linear qB) beta)))
      (A_m_dual (hom_as_linear qL) gamma)).
Proof.
have hAlpha:A_m_dual (hom_as_linear assoc) (A_m_dual (hom_as_linear pR) alpha)=
    A_m_dual (hom_as_linear pL) (A_m_dual (hom_as_linear pA) alpha).
  by rewrite -(@original_linear_pullback_composition R X Y M R^o assoc pR k alpha)
    -(@original_linear_pullback_composition R X MN M R^o pL pA k alpha)
    covector_reassociation_first_composition.
have hBeta:A_m_dual (hom_as_linear assoc)
    (A_m_dual (hom_as_linear qR) (A_m_dual (hom_as_linear pB) beta))=
    A_m_dual (hom_as_linear pL) (A_m_dual (hom_as_linear qB) beta).
  by rewrite -(@original_linear_pullback_composition R X Y NV R^o assoc qR l
      (A_m_dual (hom_as_linear pB) beta))
    -(@original_linear_pullback_composition R X NV N R^o (hom_comp qR assoc) pB l beta)
    -(@original_linear_pullback_composition R X MN N R^o pL qB l beta)
    covector_reassociation_middle_composition.
have hGamma:A_m_dual (hom_as_linear assoc)
    (A_m_dual (hom_as_linear qR) (A_m_dual (hom_as_linear qC) gamma))=
    A_m_dual (hom_as_linear qL) gamma.
  by rewrite -(@original_linear_pullback_composition R X Y NV R^o assoc qR r
      (A_m_dual (hom_as_linear qC) gamma))
    -(@original_linear_pullback_composition R X NV V R^o (hom_comp qR assoc) qC r gamma)
    covector_reassociation_last_composition.
rewrite !form_pullback_product hAlpha hBeta hGamma.
apply:(can_inj (@form_includeK R X R^o (k+(l+r))%N)).
rewrite form_reindex_include !form_wedge_include.
exact:(@alternating_wedge_associative R h2 X R^o (fun a b:R^o=>a*b)
  (@scalar_bilinear R) (@mulrA R)
  (form_include (A_m_dual (hom_as_linear pL) (A_m_dual (hom_as_linear pA) alpha)))
  (form_include (A_m_dual (hom_as_linear pL) (A_m_dual (hom_as_linear qB) beta)))
  (form_include (A_m_dual (hom_as_linear qL) gamma))).
Qed.
End CovectorCartesianReassociation.
