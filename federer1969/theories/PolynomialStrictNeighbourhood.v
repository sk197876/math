(** Scalar continuity supporting Federer (1969), 3.3.15,
    p. 299: strict normalized-ball bounds persist under radius enlargement. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  topology normedtype realfun lra.
(** The narrow lra import checks only finite real-field arithmetic;
    it provides no measure or geometric theorem. *)
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [polynomial_strict_upper_neighbourhood]: scalar
    background supporting the Borel upper-density level sets used in
    Federer 3.3.15, p. 299, for the normalization in 2.10.19, p. 181.
    Every strict upper bound on a fixed real polynomial monomial
    persists on an actual radius neighbourhood, including degree zero. *)
Lemma polynomial_strict_upper_neighbourhood (R:realType) (a r b:R) m:
  a*r^+m<b ->exists d:R,0<d /\forall t:R,
    mdist (r:real_line_metric R) t<d ->a*t^+m<b.
Proof.
move=>hLower.
pose f (z:real_line_metric R):real_line_metric R:=a*z^+m.
have hContinuous:continuous f.
  move=>z; apply:(@continuousM R R^o (fun _:R=>a) (fun t:R=>t^+m) z).
  - exact:cst_continuous.
  - exact:exprn_continuous.
pose gap:=b-f r.
have hGap:0<gap by rewrite /gap subr_gt0.
have hNb:nbhs (f r) [set z:real_line_metric R|mdist (f r) z<gap].
  apply:(metricType_numDomainType.nbhs_mdistP (f r) _).2.
  exists gap; first exact:hGap.
  by move=>z hz.
have [d hd hLocal]:=(metricType_numDomainType.nbhs_mdistP (r:real_line_metric R) _).1
  (hContinuous r _ hNb).
exists d; split; first exact:hd.
move=>t ht; have hNear:=hLocal t ht.
change (is_true (`|f r-f t|<gap)) in hNear.
have hNorm:=ler_norm (f t-f r); rewrite distrC in hNorm.
rewrite /gap in hNear.
have hResult:f t<b by lra.
exact:hResult.
Qed.
