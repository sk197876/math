(** Federer (1969), 3.4.10, p. 338:
    the positive and negative halves of an actual
    analytic line cannot be separated by a local
    analytic variety. Reuse finite defining equations, their
    original germ laws and the existing analytic identity theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormBoundedLinearTopology NormLinearDomainLaws NormConvexConnected NormAnalyticUP
  NormAnalyticLinear NormAnalyticOperations AnalyticIdentityOpenZero SetGermUP
  SetGermExistence FiniteAnalyticVarietyUP AnalyticVarietyGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_half_line_obstruction]: supporting
    the nonanalytic singular-part example cited in 3.4.10,
    p. 338. A bounded actual linear map
    meets the original set on its whole positive
    half-line and misses it on its negative half-line;
    finite analytic equations at zero would contradict identity. *)
Theorem analytic_half_line_obstruction (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (S:set X) (L:Hom R^o X):
  norm_bounded_linear (fun t:R^o=>`|t|) NX L ->
  (forall t,0<t ->S (L t)) ->(forall t,t<0 ->~S (L t)) ->
  ~@is_analytic_variety_germ R X NX hNX 0
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 S).
Proof.
move=>hBound hPositive hNegative [U [Z [haU [[hU [I [f [hF hEquation]]]] hGerm]]]].
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
have [V [hV [haV hEqual]]]:=(@set_germ_equality_original T 0 Z S).1 hGerm.
pose O:=U `&` V.
have hO:@open T O:=openI hU hV.
have haO:O 0 by split.
have hInterior:norm_domain_interior NX O (L 0).
  rewrite linear0.
  apply:(@norm_domain_interior_neighbourhood R X NX hNX O 0).2.
  have h:=hO;rewrite openE in h;exact:h 0 haO.
have [r [hr hPre]]:=@norm_bounded_linear_preimage_interior R R^o X N NX hN
  L O 0 hBound hInterior.
pose B:set R^o:=[set t|N (t-0)<r].
have hBInterior t (ht:B t):norm_domain_interior N B t.
  exact:(@norm_open_ball_domain_interior R R^o N hN 0 r t ht).
have hB:@open (real_norm_metric_space hN) B.
  rewrite openE=>t ht;exact:(@norm_domain_interior_neighbourhood R R^o N hN B t).1
    (hBInterior t ht).
have hBO t (ht:B t):O (L t).
  have ht0:N t<r.
    change (is_true (N (t-0)<r)) in ht;by rewrite subr0 in ht.
  have h:=hPre t ht0;by rewrite add0r in h.
have hAnalyticL:=@norm_bounded_linear_analytic R R^o X N NX hN hNX B hBInterior L hBound.
have hComposite i:=@norm_analytic_compose_on R R^o X R^o N NX N hN hNX hN
  B U L (f i) (fun t ht=>(hBO t ht).1) hAnalyticL (hF i).
pose W:set R^o:=[set t|N (t-r/2)<r/4].
have hWInterior t (ht:W t):norm_domain_interior N W t.
  exact:(@norm_open_ball_domain_interior R R^o N hN (r/2) (r/4) t ht).
have hW:@open (real_norm_metric_space hN) W.
  rewrite openE=>t ht;exact:(@norm_domain_interior_neighbourhood R R^o N hN W t).1
    (hWInterior t ht).
have hMid:W (r/2).
  change (is_true (`|r/2-r/2|<r/4)).
  rewrite subrr normr0;by rewrite divr_gt0 // ltr0n.
have hWSmall t (ht:W t):0<t /\B t.
  have hUpper:=ler_norm (t-r/2).
  have hLower:=ler_norm (-(t-r/2));rewrite normrN in hLower.
  change (is_true (`|t-r/2|<r/4)) in ht.
  have hT:0<t by lra.
  split;first exact:hT.
  change (is_true (`|t-0|<r));rewrite subr0 (ger0_norm (ltW hT));lra.
have hZero i t (ht:W t):f i (L t)=0.
  have [htPositive htB]:=hWSmall t ht.
  have htO:=hBO t htB.
  have hz:Z (L t).
    have h:(Z `&` V) (L t) by rewrite hEqual;split;[exact:hPositive t htPositive|exact:htO.2].
    exact:h.1.
  exact:((hEquation (L t)).1 hz).2 i.
have hConnected:=@norm_inner_convex_connected R R^o N hN B
  (@norm_open_ball_convex R R^o N hN 0 r).
have hAll i:=@analytic_identity_open_zero R R^o R^o N N hN hN B W
  (fun t=>f i (L t)) (r/2) hConnected (hComposite i) hW hMid
  (fun t ht=>(hWSmall t ht).2) (hZero i).
have hNegPoint:B (-r/2).
  change (is_true (`|(-r/2)-0|<r)).
  rewrite subr0 mulNr normrN (ger0_norm (ltW (divr_gt0 hr (ltr0n R 2))));lra.
have hZ:Z (L (-r/2)).
  apply:(hEquation _).2;split;first exact:(hBO _ hNegPoint).1.
  by move=>i;exact:hAll i _ hNegPoint.
have hS:S (L (-r/2)).
  have h:(S `&` V) (L (-r/2)) by rewrite -hEqual;split;[exact:hZ|exact:(hBO _ hNegPoint).2].
  exact:h.1.
apply:(hNegative (-r/2) _ hS).
by rewrite mulNr oppr_lt0 divr_gt0 // ltr0n.
Qed.
