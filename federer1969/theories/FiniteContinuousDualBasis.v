(** Federer (1969), 4.1.19, p. 377: the
    original finite coefficient dual has the
    dual basis of 1.4.3, p. 19.
    Existing finite linear bounds and the
    algebraic basis-transport theorem provide this
    supporting coordinate interface. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP LinearBasis FiniteDualDimension
  NormDifferentialUP NormFiniteLinearBound ContinuousRealFunctional
  ContinuousDualUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [finite_continuous_dual_basis_exists]:
    the basis of the actual continuous coefficient
    dual used in Federer 4.1.19, p. 377,
    is the original algebraic dual basis of
    1.4.3, p. 19. Finite-dimensional continuity
    adds no new restriction on the linear functionals. *)
Theorem finite_continuous_dual_basis_exists
    (R : realType) (V D : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hDual : is_continuous_dual hN ed DN)
    d (e : 'I_d -> V) (he : is_basis e) :
  exists b : 'I_d -> D, is_basis b /\
    forall i, ed (b i) = dual_basis he i.
Proof.
have hSurjective (a : Hom V R^o) : exists v : D, ed v = a.
  have [c [hC hBound]] := @norm_finite_linear_bounded R V R^o
    N (fun t : R => `|t|%R) hN (scalar_absolute_value_norm R) d e he a.
  have hContinuous := @bounded_real_functional_continuous R V N hN
    (hom_as_linear a) c hC hBound.
  exact: (continuous_dual_surjective hDual hContinuous).
pose hInjective := continuous_dual_injective hDual.
pose j := @linear_inverse R D (Hom V R^o) (hom_as_linear ed)
  hInjective hSurjective.
have hK : cancel j ed.
  exact: (@linear_inverseK R D (Hom V R^o) (hom_as_linear ed)
    hInjective hSurjective).
have hKV : cancel ed j.
  exact: (@linear_inverseKV R D (Hom V R^o) (hom_as_linear ed)
    hInjective hSurjective).
exists (fun i => j (dual_basis he i)); split.
- exact: (@basis_transport R [the choiceType of 'I_d] (Hom V R^o) D
    (dual_basis he) (GRing.Linear.clone _ _ _ _ j _) (hom_as_linear ed)
    hK hKV (dual_basisP he)).
- move=> i; exact: hK.
Qed.
