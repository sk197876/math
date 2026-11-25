(** Federer (1969), 4.1.6, pp. 352–355:
    public bounded coefficient maps and naturality
    of the original exterior alternation. These
    adapters use only the independently specified
    original form norms and signed derivative law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  GrassmannAbbreviations Alternating FormCoefficients AlternatingFormNormUP
  ExteriorDifferentialUP ExteriorDifferentialSealed DifferentialFormCoefficientMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [bounded_form_coefficient_map]: a bounded
    original coefficient map induces a bounded map
    of the induced form spaces,
    supporting Federer 4.1.6, pp. 352–355. *)
Lemma bounded_form_coefficient_map (R:realType) (V W Z:lmodType R)
    (NV:V->R) (NW:W->R) (NZ:Z->R) (hNV:is_real_norm NV) (hNZ:is_real_norm NZ)
    m (P:A_m V W m->R) (Q:A_m V Z m->R)
    (hP:is_alternating_form_norm NV NW P) (hQ:is_alternating_form_norm NV NZ Q) (M:Hom W Z):
  norm_bounded_linear NW NZ M->
  norm_bounded_linear P Q (hom_of_linear (@form_coefficients R V W Z (hom_as_linear M) m)).
Proof.
move=>[C [hC hBound]]; exists C; split=>//.
exact:(form_coefficient_change_bound hNV hNZ hP hQ hC hBound).
Qed.

(** Source for [exterior_differential_change_coefficients]:
    the opaque original exterior alternation commutes
    with every linear coefficient map,
    supporting Federer 4.1.6, pp. 352–355. *)
Theorem exterior_differential_change_coefficients (R:realType) (h2:(1+1:R)!=0)
    n (W Z:lmodType R) (M:Hom W Z) m (L:Hom (R_n R n) (A_m (R_n R n) W m)):
  form_coefficients (hom_as_linear M) (@ExteriorDifferential.value R h2 n W m L)=
    @ExteriorDifferential.value R h2 n Z m
      (hom_comp (hom_of_linear (@form_coefficients R (R_n R n) W Z (hom_as_linear M) m)) L).
Proof.
apply:exterior_differential_value_unique.
- exact:(exterior_differential_coefficient_values M (@ExteriorDifferential.laws R h2 n W m L)).
- exact:ExteriorDifferential.laws.
Qed.
