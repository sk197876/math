(** Federer (1969), 3.4.9, p. 337:
    the original functional analytic stratum is the
    difference of two analytic subvarieties of its domain.
    Keep its original finite equations and inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness FunctionalAnalyticSubmanifoldUP FiniteAnalyticVarietyUP FiniteAnalyticVarietyLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_analytic_difference]: the difference
    representation used to apply the first assertion
    of 3.4.9, p. 337, to each original
    stratum and its analytic sphere cut. *)
Theorem functional_analytic_difference (R:realType) n m (U S:set (R_n R n)):
  @is_functional_analytic_submanifold R n m U S ->
  exists H N:set (R_n R n),
    @is_finite_analytic_variety R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U H /\
    @is_finite_analytic_variety R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U N /\S=H `\` N.
Proof.
move=>[hMN [hU [f [g [hF [hG [hEquation hDifferentials]]]]]]].
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose H:set X:=[set x|U x /\forall i,f i x=0].
pose Z:set X:=[set x|U x /\g x=0].
have hH:@is_finite_analytic_variety R X NX hNX U H.
  split;first exact:hU.
  exists (Finite.clone 'I_(n-m) _),f;by split.
have hZ:@is_finite_analytic_variety R X NX hNX U Z.
  split;first exact:hU.
  exists (Finite.clone 'I_1 _),(fun _=>g);split;first by move=>i;exact:hG.
  move=>x;split;first by move=>[hx hZero];split=>// i.
  by move=>[hx hZero];split;last exact:hZero ord0.
exists H,(H `&` Z);split;first exact:hH.
split;first exact:finite_analytic_variety_intersection hH hZ.
apply/seteqP;split.
- move=>x /hEquation [hx [hZero hNonzero]];split;first by split.
  by move=>[_ [_ hBad]];apply:hNonzero.
- move=>x [[hx hZero] hNot];apply/(hEquation x);split;first exact:hx.
  split;first exact:hZero.
  move=>hBad;apply:hNot;split;by split.
Qed.
