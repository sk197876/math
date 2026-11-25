(** Federer (1969), 4.1.18, p. 375: positive
    compact test convergence gives signed compact test
    convergence in the original Daniell weak topology.
    The decomposition is the old function-lattice
    positive/negative decomposition.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws
  CompactSupportFunctionUP CompactSupportFunctionLattice RadonCompactScalarIntegral
  MeasureUP RadonMeasureUP MeasureIntegralUniqueness SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_function_positive_parts]: the
    two original compact positive parts are in
    K(X)+ and reconstruct f, from 2.5.1,
    p. 91, supporting the signed weak variation
    conclusion of 4.1.18, p. 375. *)
Theorem compact_function_positive_parts (R:realType) (X:topologicalType)
    (f:X->R):
  compactly_supported_continuous_functions f ->
  positive_function_lattice (@compactly_supported_continuous_functions R X)
    (fun x=>Order.max (f x) 0) /\
  positive_function_lattice (@compactly_supported_continuous_functions R X)
    (fun x=>Order.max (-f x) 0) /\
  f=(fun x=>Order.max (f x) 0-Order.max (-f x) 0).
Proof.
move=>hF.
have hL:=@compactly_supported_continuous_functions_lattice R X.
split.
- split;first exact:(@function_lattice_positive_part R X
    (@compactly_supported_continuous_functions R X) hL f hF).
  by move=>x;rewrite le_max lexx orbT.
- split.
  + split;first exact:(@function_lattice_negative_part R X
      (@compactly_supported_continuous_functions R X) hL f hF).
    by move=>x;rewrite le_max lexx orbT.
  + apply:funext=>x;case:(leP 0 (f x))=>hx.
    * have hNeg:-f x<=0 by rewrite oppr_le0.
      by rewrite (max_r hNeg) subr0.
    * have hNeg:0<=-f x by rewrite oppr_ge0;exact:ltW hx.
      by rewrite (max_l hNeg) sub0r opprK.
Qed.

(** Source for [radon_compact_integral_positive_parts]:
    the original signed compact integral is the
    difference of the two positive compact integrals,
    supporting Federer 4.1.18, p. 375. Values
    of the positive integral off its cone are
    never used. *)
Theorem radon_compact_integral_positive_parts (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu) (f:X->R):
  compactly_supported_continuous_functions f ->
  @radon_compact_integral R X mu hm hr f=
    @radon_positive_compact_integral R X mu hm hr (fun x=>Order.max (f x) 0)-
    @radon_positive_compact_integral R X mu hm hr (fun x=>Order.max (-f x) 0).
Proof.
move=>hF.
have [hPlus [hMinus hEqual]]:=compact_function_positive_parts hF.
have hP:=@radon_positive_compact_integral_laws R X mu hm hr
  (fun x=>Order.max (f x) 0) hPlus.
have hM:=@radon_positive_compact_integral_laws R X mu hm hr
  (fun x=>Order.max (-f x) 0) hMinus.
have hSub:=@real_total_integral_subtract R X mu hm
  (fun x=>Order.max (f x) 0) (fun x=>Order.max (-f x) 0)
  (@radon_positive_compact_integral R X mu hm hr (fun x=>Order.max (f x) 0))
  (@radon_positive_compact_integral R X mu hm hr (fun x=>Order.max (-f x) 0)) hP hM.
rewrite -hEqual in hSub.
exact:(EFin_inj (measure_integral_unique
  (@radon_compact_integral_laws R X mu hm hr f hF) hSub)).
Qed.
