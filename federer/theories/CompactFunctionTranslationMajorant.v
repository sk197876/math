(** Federer (1969), 4.1.18, p. 375: a positive
    compact continuous function has a positive compact
    majorant of all sufficiently small translates, whose
    integral exceeds the original by less than any
    prescribed positive delta.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric LinearBasis
  NormClassZeroWhole NormCompactFunctionBound FiniteNormMetricCompactness
  FiniteNormEquivalence CompactSupportFunctionUP CompactSupportFunctionLattice
  CompactCutoffUP CompactCutoffSealed FunctionLatticeUP FunctionLatticeLaws
  MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws
  CompactFunctionUniformContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_function_translation_majorant]:
    the displayed choice of g after the averaged-variation
    bound in Federer 4.1.18, p. 375. Function order
    is the pointwise lattice order of 2.5.1; the
    majorant is also unequal to every nearby translate.
    The proof uses a small positive compact cutoff,
    not a constant function with noncompact support. *)
Theorem compact_function_translation_majorant (R:realType)
    (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    d (b:'I_d->X) (hb:is_basis b)
    (D:((real_norm_metric_space hNX)->R)->R):
  is_monotone_daniell_integral
    (positive_function_lattice
      (@compactly_supported_continuous_functions R
        (real_norm_metric_space hNX))) D ->
  forall f,compactly_supported_continuous_functions f ->
    (forall x,0<=f x) ->forall delta:R,0<delta ->
    exists g,compactly_supported_continuous_functions g /\
      (forall x,0<=g x) /\D g<D f+delta /\
      exists r:R,0<r /\forall z:X,NX z<r ->
        function_le (fun x:X=>f (x+z)) g /\
        (fun x:X=>f (x+z))<>g.
Proof.
move=>hD f hF hFpos delta hDelta.
pose XT:=real_norm_metric_space hNX.
have hIdentity:continuous (fun x:XT=>x) by move=>x; exact:cvg_id.
have hClass:=@norm_continuous_whole_class_zero R X X NX NX
  hNX hNX (fun x=>x) hIdentity.
have [M [hM hBound]]:=@norm_class_zero_compact_bounded R X X NX NX
  hNX hNX setT (real_function_support f) (fun x=>x) hF.2
  (fun _ _=>Logic.I) hClass.
pose C:set XT:=[set x|NX x<=M+1].
have hC:compact C:=@finite_norm_metric_ball_compact R X NX hNX d b hb (M+1).
pose chi:=@CompactCutoff.value R XT C (@metric_hausdorff R XT)
  (@finite_norm_locally_compact R X d b hb NX hNX) hC.
have hChi:is_compact_cutoff C chi:=@CompactCutoff.laws R XT C
  (@metric_hausdorff R XT) (@finite_norm_locally_compact R X d b hb NX hNX) hC.
have hChiPos:positive_function_lattice
    (@compactly_supported_continuous_functions R XT) chi.
  split;first exact:compact_cutoff_function hChi.
  by move=>x; exact:(andP (compact_cutoff_range hChi x)).1.
have hL:=@compactly_supported_continuous_functions_lattice R XT.
have hPositiveL:=positive_function_lattice_laws hL.
have hDChi:0<=D chi:=monotone_daniell_integral_nonnegative
  hPositiveL hD hChiPos hChiPos.2.
have hDen:0<1+D chi by lra.
pose a:=delta/(1+D chi).
have hA:0<a by rewrite /a divr_gt0.
have hCost:a*D chi<delta.
  have hNonzero:1+D chi!=0 by rewrite (gt_eqF hDen).
  have hEq:a*(1+D chi)=delta.
    by rewrite /a divfK //.
  rewrite mulrDr mulr1 in hEq; lra.
pose g (x:XT):=f x+a*chi x.
have hScale:compactly_supported_continuous_functions (fun x=>a*chi x):=
  function_lattice_scale hL (ltW hA) hChiPos.1.
have hG:compactly_supported_continuous_functions g:=
  function_lattice_add hL hF hScale.
have hGpos x:0<=g x.
  apply:addr_ge0;first exact:hFpos.
  exact:mulr_ge0 (ltW hA) (hChiPos.2 x).
have hIntegral:D g<D f+delta.
  rewrite /g (monotone_daniell_integral_add hD
    (conj hF hFpos) (conj hScale (fun x=>mulr_ge0 (ltW hA) (hChiPos.2 x))))
    (monotone_daniell_integral_scale hD (ltW hA) hChiPos).
  rewrite ltrD2l;exact:hCost.
have hHalf:0<a/2 by rewrite divr_gt0 // ltr0n.
have [r [hr hUniform]]:=@compact_function_uniform_translation R X NX hNX
  f hF (a/2) hHalf.
exists g; split=>//;split=>//;split=>//.
exists (Order.min r 1);split;first by rewrite lt_min hr ltr01.
move=>z hz.
have hRadiusR:Order.min r 1<=r by rewrite ge_min lexx.
have hRadiusOne:Order.min r 1<=1 by rewrite ge_min lexx orbT.
have hzR:NX z<r:=lt_le_trans hz hRadiusR.
have hzOne:NX z<1:=lt_le_trans hz hRadiusOne.
have hZeroC:C 0 by rewrite /C /= (real_seminorm_zero hNX.1); lra.
have hChiZero:chi 0= 1:=compact_cutoff_on_set hChi hZeroC.
split.
- move=>x.
  case:(pselect (C x))=>[hx|hx].
  + have hOne:chi x= 1:=compact_cutoff_on_set hChi hx.
    have hError:=hUniform z hzR x.
    have hUpper:f (x+z)-f x<a/2:=le_lt_trans (ler_norm _) hError.
    rewrite /g hOne mulr1; lra.
  + have hShift:f (x+z)=0.
      apply:(@real_function_zero_off_support R XT f (x+z))=>hSupport.
      apply:hx.
      have hTriangle:=real_seminorm_triangle hNX.1 (x+z) (-z).
      rewrite addrK (real_seminorm_negate hNX.1) in hTriangle.
      exact:le_trans hTriangle (lerD (hBound (x+z) hSupport) (ltW hzOne)).
    rewrite hShift;exact:hGpos.
- move=>hEqual.
  have hAtZero:=congr1 (fun h:XT->R=>h 0) hEqual.
  have hError:=hUniform z hzR 0.
  have hUpper:f (0+z)-f 0<a/2:=le_lt_trans (ler_norm _) hError.
  rewrite /g hChiZero mulr1 in hAtZero; lra.
Qed.
