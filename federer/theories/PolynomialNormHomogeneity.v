(** Federer (1969), 1.10.5, p. 48: supporting homogeneous evaluation
    estimate for polynomial norms. Source context: PolynomialNormUP.v. The
    homogeneous-polynomial representation and its scaling law were proved
    from 1.10.4, pp. 45-46. Arbitrary normed input and seminormed
    coefficient spaces are allowed. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import RealNormUP RealNormNormalization SymmetricForms
  HomogeneousPolynomialFunctions PolynomialNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [homogeneous_polynomial_normalized_norm]: Federer
    1.10.5, p. 48, supporting normalization by the input
    norm. Homogeneity extracts the m-th power of the input length.
    At zero this remains valid even for constant, degree-zero terms. *)
Lemma homogeneous_polynomial_normalized_norm (R : realType) (V W : lmodType R)
    (NV : V -> R) (NW : W -> R) (hV : is_real_norm NV) (hW : is_real_seminorm NW)
    m (P : V -> W) (hP : is_homogeneous_polynomial m P) x :
  NW (P x) = (NV x)^+m * NW (P (real_norm_normalize NV x)).
Proof.
have [f hf] := hP; rewrite !hf.
have hx := @real_norm_normalize_reconstruct R V NV (proj2 hV) x.
rewrite -{1}hx sform_polynomial_scale_argument (real_seminorm_scale hW)
  normrX (ger0_norm (real_seminorm_nonnegative (proj1 hV) x)).
by [].
Qed.

(** Source for [homogeneous_polynomial_norm_evaluation]: Federer
    1.10.5, p. 48, supporting bound |P(x)| <= |x|^m ||P||,
    including infinite supremum values and the degree-zero case. *)
Theorem homogeneous_polynomial_norm_evaluation (R : realType) (V W : lmodType R)
    (NV : V -> R) (NW : W -> R) (hV : is_real_norm NV) (hW : is_real_seminorm NW)
    m (P : V -> W) (hP : is_homogeneous_polynomial m P) x :
  ((NW (P x))%:E <= ((NV x)^+m)%:E * polynomial_norm (proj1 hV) NW P)%E.
Proof.
rewrite (@homogeneous_polynomial_normalized_norm R V W NV NW hV hW m P hP x) EFinM.
apply: lee_wpmul2l.
- rewrite lee_fin; exact: exprn_ge0 (real_seminorm_nonnegative (proj1 hV) x).
- apply: polynomial_norm_upper; exact (@real_norm_normalize_unit R V NV (proj1 hV) x).
Qed.
