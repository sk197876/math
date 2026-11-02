(** Federer (1969), 3.1.24, p. 240: actual
    symmetric forms for the derivatives of the scalar forward
    majorant at zero, for use in the exact composition formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ContinuousMultilinearUP ContinuousMultilinearZero NormHigherDifferentialUP
  NormHigherSymmetricFormUP ScalarAnalyticFraction ScalarInverseMajorant ScalarInverseMajorantIdentity
  ScalarForwardMajorantDifferentials ScalarCoefficientForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_forward_majorant_form_actual]: the
    scalar outer derivative forms used to identify lambda_p
    in Federer 3.1.24, p. 240. Their coefficients are
    zero in order zero, beta*gamma in order one, and
    -gamma^m m! above order one. All forms represent actual
    recursive differentials at zero on the nonzero-denominator domain. *)
Theorem scalar_forward_majorant_form_actual (R:realType)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->R^o}->Hom (Z i) R^o)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) (@ev i) (@ZN i))
    (b g:R) m :
  is_norm_higher_differential_form (fun t:R^o=>`|t|) ev ZN
    (scalar_analytic_fraction_domain g) (scalar_forward_majorant b g) m 0
    (scalar_coefficient_form m (scalar_forward_majorant_coefficient b g m)).
Proof.
have [_ [D [hD hE]]]:=@scalar_forward_majorant_differentials R Z ev ZN hZ b g.
have h0:=scalar_analytic_fraction_zero_domain g.
have he i (u:{ffun 'I_i->R^o}):@ev i u (D i 0)=
    (\prod_(j<i) u j)*scalar_forward_majorant_coefficient b g i.
  case:i u=>[|i] u; last exact (hE i.+1 (leq0n i) u).
  rewrite big_ord0 mul1r /scalar_forward_majorant_coefficient.
  have hh: @ev 0%N [ffun i:'I_0=>(0:R^o)] (D 0%N 0)= scalar_forward_majorant b g 0.
    exact (hD 0%N 0 h0).2.
  rewrite (zero_arity_arguments_unique u [ffun i:'I_0=>(0:R^o)]) hh.
  exact: scalar_forward_majorant_zero.
exact (@scalar_coefficient_form_actual R Z ev ZN (scalar_analytic_fraction_domain g)
  (scalar_forward_majorant b g) m 0 (D m 0) (scalar_forward_majorant_coefficient b g m)
  (hD m 0 h0) (he m)).
Qed.
