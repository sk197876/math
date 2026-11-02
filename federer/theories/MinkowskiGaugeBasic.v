(** Federer (1969), 3.2.35, p. 271:
    elementary consequences of the independent infimum
    laws, used before proving radial convex-boundary geometry. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import MinkowskiGaugeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [minkowski_gauge_unique]: uniqueness
    of the defining infimum of g in Federer
    3.2.35, p. 271. The proof uses
    only the independent lower-bound laws and does
    not expose the existence witness. *)
Lemma minkowski_gauge_unique (R:realType) (V:lmodType R) (S:set V) g h:
  is_minkowski_gauge S g ->is_minkowski_gauge S h ->forall x,g x=h x.
Proof.
move=>hG hH x; apply/eqP; rewrite eq_le; apply/andP; split.
- apply:(@minkowski_gauge_greatest R V S h hH x (g x)).
  move=>t ht hS; exact:(@minkowski_gauge_lower R V S g hG x t ht hS).
- apply:(@minkowski_gauge_greatest R V S g hG x (h x)).
  move=>t ht hS; exact:(@minkowski_gauge_lower R V S h hH x t ht hS).
Qed.

(** Source for [minkowski_gauge_nonnegative]: the
    nonnegative gauge used in the positive radial
    parametrization of Federer 3.2.35, p. 271.
    Zero is a lower bound for all positive
    rescaling parameters; boundedness is not needed. *)
Lemma minkowski_gauge_nonnegative (R:realType) (V:lmodType R) (S:set V) g:
  is_minkowski_gauge S g ->forall x,0<=g x.
Proof.
move=>hG x; apply:(@minkowski_gauge_greatest R V S g hG x 0).
by move=>t ht _; exact:ltW ht.
Qed.

(** Source for [minkowski_gauge_approximation]: approximation
    of the defining infimum in Federer 3.2.35,
    p. 271, used to prove its homogeneity
    and convexity. Positive errors give actual original
    rescaling witnesses; no minimum is assumed. *)
Lemma minkowski_gauge_approximation (R:realType) (V:lmodType R) (S:set V) g:
  is_minkowski_gauge S g ->forall (x:V) (e:R),0<e ->
    exists t:R,0<t /\S (t^-1*:x) /\t<g x+e.
Proof.
move=>hG x e he; apply:contrapT=>hn.
have hb:forall t:R,0<t ->S (t^-1*:x) ->g x+e<=t.
  move=>t ht hs; rewrite leNgt; apply/negP=>hBad; apply:hn.
  exists t; by split=>//; split.
have hBound:=@minkowski_gauge_greatest R V S g hG x (g x+e) hb.
have hStrict:g x<g x+e by rewrite ltrDl.
by have hh:=lt_le_trans hStrict hBound; rewrite ltxx in hh.
Qed.

(** Source for [minkowski_gauge_zero]: the value
    g(0)=0 in the positively homogeneous gauge
    of Federer 3.2.35, p. 271. Every
    positive rescaling of zero remains in the
    original set, so its infimum is zero. *)
Lemma minkowski_gauge_zero (R:realType) (V:lmodType R) (S:set V) g:
  is_minkowski_gauge S g ->S 0 ->g 0= 0.
Proof.
move=>hG hS; apply/eqP; rewrite eq_le (minkowski_gauge_nonnegative hG) andbT.
apply/ler_addgt0Pr=>e he; rewrite add0r.
apply:(@minkowski_gauge_lower R V S g hG 0 e he).
by rewrite scaler0.
Qed.
