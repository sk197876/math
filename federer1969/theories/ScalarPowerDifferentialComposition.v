(** Federer (1969), 3.4.8(10), p. 331:
    differentiate the original coordinate powers
    in the displayed defining equations. Apply
    the existing scalar power derivative and
    the chain rule of 3.1.1(2), p. 210. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialChain NormDifferentialLocal
  NormHigherCurveDerivativeUP ScalarCoefficientLinearAlgebra RealCurvePolynomialDerivatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_scalar_power_differential_composition]:
    the differential of a coordinate power
    on the original source, supporting
    3.4.8(10), p. 331. Compose the proved
    scalar power derivative with the original
    scalar differential; the empty power remains. *)
Theorem norm_scalar_power_differential_composition (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) (A:X->Prop) (f:X->R) a (L:Hom X R^o) n:
  has_norm_differential NX (fun t:R^o=>`|t|) A f a L ->
  has_norm_differential NX (fun t:R^o=>`|t|) A (fun x=>f x^+n) a
    ((n%:R*f a^+n.-1)*:L).
Proof.
move=>hF.
pose c:=n%:R*f a^+n.-1.
have hPower:=@real_curve_derivative_full_differential R (fun t:R=>t^+n) (f a) c
  (@real_curve_power_actual_derivative R (f a) n).
have hComposite:=@norm_differential_chain R X R^o R^o NX (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
  hNX (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R) A (fun _=>True) f
  (fun t=>t^+n) a L (@scalar_coefficient_linear_map R R^o c) hF hPower.
have hDifferential:=@norm_differential_restrict R X R^o NX (fun t:R^o=>`|t|)
  (fun x=>A x /\True) A (fun x=>f x^+n) a
  (hom_comp (@scalar_coefficient_linear_map R R^o c) L)
  (fun x hx=>conj hx Logic.I) (norm_differential_interior hF) hComposite.
have hMaps:hom_comp (@scalar_coefficient_linear_map R R^o c) L = c*:L.
  apply:hom_ext=>x;rewrite hom_compE.
  change (L x*c = c*L x);exact:mulrC.
by rewrite hMaps in hDifferential.
Qed.
