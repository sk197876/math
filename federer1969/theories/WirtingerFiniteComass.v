(** Federer (1969), 1.8.2, p. 40: the computed comass
    in the public sealed finite-dimensional interface. A complex
    basis of length n supplies the printed condition m <= n. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexOrderedBases
  HermitianUP HermitianRealImaginary HermitianRotation TwoFormPowers
  LinearBasis Comass ComassUP WirtingerComass ComplexFrameDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [wirtinger_finite_comass]: Federer 1.8.2,
    p. 40, ||A^m||=m! for 0<m<=dim_C V, using the sealed
    comass interface. Degree zero is covered separately by
    [two_form_zeroth_comass], with literal empty-product simplicity. *)
Theorem wirtinger_finite_comass (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType (ComplexScalars.C R))
    (H : V -> V -> ComplexScalars.C R) (hH : is_hermitian_product H)
    n (e : 'I_n -> V) (he : is_basis e) m
    (hm : (0 < m+m)%N) (hmn : (m <= n)%N) :
  comass h2 (hermitian_real_inner_product hH) (ordered_real_basisP he) hm
    (two_form_power h2 (hermitian_two_form hH) m) = m`!%:R.
Proof.
exact (@wirtinger_comass_value R h2 V H hH m
  (fun i : 'I_m => e (widen_ord hmn i)) (@basis_prefix_independent (ComplexScalars.C R) V n e he m hmn) _
  (@comassP R h2 (restricted_space (ComplexScalars.embed R) V)
    (hermitian_real_part H) (hermitian_real_inner_product hH)
    (n+n) (ordered_real_basis e) (ordered_real_basisP he) (m+m) hm _)).
Qed.
