(** Federer (1969), 1.8.2, p. 40: restriction to the associated
    subspace commutes with the exterior power of the imaginary two-form.
    This is the multiplicativity of pullback from 1.4.2, p. 18. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import BoundedHom HomogeneousHom AlgebraUP AlgebraPowers AlternatingForms
  AlternatingSum AlternatingDual AlternatingProduct AlternatingUnit
  ScalarCoefficients OmegaNaturality TwoFormPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [two_form_power_natural]: Federer 1.8.2,
    p. 40, the displayed pullback of A^m is the m-th power of the
    pulled-back two-form. This holds for every linear map and degree. *)
Theorem two_form_power_natural (K : fieldType) (h2 : (1+1 : K) != 0)
    (V W : lmodType K) (f : {linear V -> W}) (phi : A_m W K^o 2) m :
  A_m_dual f (two_form_power h2 phi m) =
    two_form_power h2 (A_m_dual f phi) m.
Proof.
apply: (can_inj (@form_includeK K V K^o (m+m))).
rewrite -A_star_dual_include !two_form_power_include.
elim: m => [|m ih].
- exact: (@A_star_dual_coefficient K V W (scalar_algebra K) f 1).
- change (A_star_dual f (alternating_wedge h2 (scalar_bilinear K)
    (form_include phi) (@algebra_power K
      (alternating_unital_algebra h2 W (scalar_algebra K)) (form_include phi) m)) =
    alternating_wedge h2 (scalar_bilinear K) (form_include (A_m_dual f phi))
      (@algebra_power K (alternating_unital_algebra h2 V (scalar_algebra K))
        (form_include (A_m_dual f phi)) m)).
  by rewrite A_star_dual_multiplicative A_star_dual_include ih.
Qed.
