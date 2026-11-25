(** Federer (1969), 4.1.8, p. 361: the original
    binomial density estimate implies the comparison of
    outer measures on every set. Use the earlier 2.4.10
    upper-integral laws; retain the almost-everywhere
    hypothesis and all infinite-mass cases. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureDensityUP MeasureDensityTransfer
  SummableRealFunctionUP RealFiniteDensityIntegral NonnegativeDensitySetLowerBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FinitePositiveDensityLower.
Variable R:realType.
Variable X:choiceType.
Variables (mu nu:set X->\bar R).
Hypothesis hm:is_measure mu.
Variable k:X->R.
Hypothesis hDensity:is_measure_density mu (real_total_integrand k) nu.
Hypothesis hNonnegative:forall x,0<=k x.
Variable C:R.
Hypothesis hC:0<C.
Hypothesis hLower:measure_almost_everywhere mu [set x|1<=C*k x].

(** Source for [finite_positive_density_lower]: the
    original finite positive coefficient times the density
    measure dominates the original measure when the density
    bound holds almost everywhere, supporting Federer 4.1.8,
    p. 361. Arbitrary target sets are retained. *)
Theorem finite_positive_density_lower A:(mu A<=C%:E*nu A)%E.
Proof.
pose g x:=if pselect (1<=C*k x) then k x else C^-1.
have hInv:0<C^-1 by rewrite invr_gt0.
have hModified:measure_almost_equal mu (real_total_integrand k) (real_total_integrand g).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hLower)=>x hx.
  exists (k x)%:E;split;first by rewrite real_total_integrand_graph.
  rewrite real_total_integrand_graph /g;case:pselect=>//hn;by exfalso;exact:hn hx.
have hDensityG:=real_finite_density_total_laws (measure_density_almost_equal hm hDensity hModified).
have hGPositive:forall x,(0<=(g x)%:E)%E.
  move=>x;rewrite lee_fin /g;case:pselect=>hCase;first exact:hNonnegative.
  exact:ltW hInv.
have hGUpper:forall x,A x->((C^-1)%:E<=(g x)%:E)%E.
  move=>x _;rewrite lee_fin /g;case:pselect=>hx;last exact:lexx.
  have h:=ler_wpM2l (ltW hInv) hx.
  by rewrite mulr1 mulrA mulVf ?gt_eqF // mul1r in h.
have hBound:=@nonnegative_density_set_lower_bound R X mu nu hm
  (fun x=>(g x)%:E) A C^-1 hDensityG hGPositive hInv hGUpper.
have hCE:(0<=C%:E)%E by rewrite lee_fin;exact:ltW hC.
have hScaled:=lee_wpmul2l hCE hBound.
by rewrite muleA -EFinM mulfV ?gt_eqF // mul1e in hScaled.
Qed.
End FinitePositiveDensityLower.
