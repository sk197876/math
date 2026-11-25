(** Federer (1969), 4.1.18, p. 375: uniform
    approximation on one compact support controls the
    positive compact Daniell integrals. The ambient
    measure may have infinite total mass.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology lra.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws
  CompactSupportFunctionUP CompactSupportFunctionLattice CompactCutoffUP
  MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_daniell_fixed_support_uniform_bound]:
    one original compact cutoff controls the uniform
    approximation error in Federer 4.1.18, p. 375,
    by the preceding positive lattice integral laws
    of 2.5.1–2.5.2, pp. 91–92. *)
Theorem compact_daniell_fixed_support_uniform_bound (R:realType)
    (X:topologicalType) (C:set X) (chi:X->R)
    (hChi:is_compact_cutoff C chi) (D:(X->R)->R)
    (hD:is_monotone_daniell_integral
      (positive_function_lattice (@compactly_supported_continuous_functions R X)) D)
    (f g:X->R) delta:
  positive_function_lattice (@compactly_supported_continuous_functions R X) f ->
  positive_function_lattice (@compactly_supported_continuous_functions R X) g ->
  0<=delta ->(forall x,`|f x-g x|<=delta) ->
  (forall x,~C x->f x=0) ->(forall x,~C x->g x=0) ->
    `|D f-D g|<=delta*D chi.
Proof.
move=>hF hG hDelta hError hFOff hGOff.
have hL:=@compactly_supported_continuous_functions_lattice R X.
have hLP:=positive_function_lattice_laws hL.
have hChiPositive:positive_function_lattice
    (@compactly_supported_continuous_functions R X) chi.
  split;first exact:compact_cutoff_function hChi.
  by move=>x;exact:(andP (compact_cutoff_range hChi x)).1.
have hScale:=function_lattice_scale hLP hDelta hChiPositive.
have hFG:forall x,f x<=g x+delta*chi x.
  move=>x;case:(pselect (C x))=>[hx|hx].
  - rewrite (compact_cutoff_on_set hChi hx) mulr1.
    have h:=le_trans (ler_norm (f x-g x)) (hError x);lra.
  - rewrite (hFOff x hx) (hGOff x hx) add0r.
    exact:mulr_ge0 hDelta (hChiPositive.2 x).
have hGF:forall x,g x<=f x+delta*chi x.
  move=>x;case:(pselect (C x))=>[hx|hx].
  - rewrite (compact_cutoff_on_set hChi hx) mulr1.
    have hNorm:`|g x-f x|<=delta by rewrite distrC;exact:hError x.
    have h:=le_trans (ler_norm (g x-f x)) hNorm;lra.
  - rewrite (hFOff x hx) (hGOff x hx) add0r.
    exact:mulr_ge0 hDelta (hChiPositive.2 x).
have hFirst:=monotone_daniell_integral_monotone hD hF
  (function_lattice_add hLP hG hScale) hFG.
have hSecond:=monotone_daniell_integral_monotone hD hG
  (function_lattice_add hLP hF hScale) hGF.
rewrite (monotone_daniell_integral_add hD hG hScale)
  (monotone_daniell_integral_scale hD hDelta hChiPositive) in hFirst.
rewrite (monotone_daniell_integral_add hD hF hScale)
  (monotone_daniell_integral_scale hD hDelta hChiPositive) in hSecond.
rewrite ler_norml;apply/andP;split;lra.
Qed.
