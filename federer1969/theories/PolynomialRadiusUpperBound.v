(** Radius-zero extension supporting Federer (1969), 2.10.19(1)–(2), p. 181.
    This supporting scalar lemma uses elementary polynomial continuity to
    justify that step, including degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal
  topology normedtype realfun lra.
From Federer Require Import RealMetricBackground ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [polynomial_positive_radius_upper_at_zero]: supporting
    radius-zero passage in 2.10.19(1)–(2), p. 181 If a fixed extended value
    is below every sufficiently small positive-radius polynomial bound, it
    is below its value at zero. No finiteness of x is assumed. *)
Lemma polynomial_positive_radius_upper_at_zero (R : realType) (x : \bar R)
    (a e : R) (m : nat) :
  (0<e)%R -> (forall r : R, (0<r<e)%R -> x<=(a*r^+m)%:E) ->
  x<=(a*0^+m)%:E.
Proof.
move=> he hbound.
apply: (@extended_upper_bound_from_scaled_errors R x (a*0^+m)%R 1%R (@ler01 R))=> eps heps.
pose f (z : real_line_metric R) : real_line_metric R := (a*z^+m)%R.
have hf : continuous f.
  move=> z; apply: (@continuousM R R^o (fun _ : R => a) (fun y : R => (y^+m)%R) z).
  - exact: cst_continuous.
  - exact: exprn_continuous.
have hn : nbhs (f 0%R) [set z : real_line_metric R | (mdist (f 0%R) z<eps)%R].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (f 0%R) _)).
  exists eps; first exact: heps.
  by move=> z hz.
have [d hd hlocal] := proj1 (metricType_numDomainType.nbhs_mdistP (0%R : real_line_metric R) _)
  (hf 0%R _ hn).
pose r := (Num.min e d/2)%R.
have hmin : (0<Num.min e d)%R by rewrite lt_min he hd.
have hr : (0<r)%R by rewrite /r divr_gt0 //.
have hsmall : (r<Num.min e d)%R by rewrite /r; lra.
have hme : (Num.min e d<=e)%R by rewrite ge_min lexx.
have hmd : (Num.min e d<=d)%R by rewrite ge_min lexx orbT.
have hre : (r<e)%R := lt_le_trans hsmall hme.
have hrd : (r<d)%R := lt_le_trans hsmall hmd.
have hdist : (mdist (0%R : real_line_metric R) r<d)%R.
  by rewrite real_line_metric_distanceE sub0r normrN ger0_norm //; exact: ltW hr.
have hh := hlocal r hdist.
change (is_true (`|f 0%R-f r|<eps)%R) in hh.
have hnorm := ler_norm (f r-f 0%R)%R.
rewrite distrC in hnorm.
have hpoly : (f r<f 0%R+eps)%R by lra.
have hrr : (0<r<e)%R by apply/andP.
have hpolyE : (f r)%:E<(f 0%R+eps)%:E by rewrite lte_fin.
have h := le_lt_trans (hbound r hrr) hpolyE.
rewrite mul1r; exact: ltW h.
Qed.
