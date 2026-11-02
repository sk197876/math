(** Federer (1969), 3.2.35, p. 271:
    positive homogeneity of the actual gauge follows
    directly from its independent rescaling infimum laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import MinkowskiGaugeUP MinkowskiGaugeBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [minkowski_gauge_positive_homogeneous]:
    the assertion that g is positively homogeneous
    in the proof of Federer 3.2.35, p. 271.
    Positive rescaling gives matching lower-bound laws
    in both directions. Convexity, boundedness and
    a selected gauge construction are unnecessary
    for this consequence of the infimum specification. *)
Lemma minkowski_gauge_positive_homogeneous (R:realType) (V:lmodType R)
    (S:set V) g:
  is_minkowski_gauge S g ->forall (c:R) (x:V),0<c ->g (c*:x)=c*g x.
Proof.
move=>hG c x hc.
have hc0:c!=0 by rewrite gt_eqF.
have hDivide:g (c*:x)/c<=g x.
  apply:(@minkowski_gauge_greatest R V S g hG x (g (c*:x)/c)).
  move=>t ht hS.
  have hS':S ((c*t)^-1*:(c*:x)).
    by rewrite scalerA invfM mulrAC (mulVf hc0) mul1r.
  have hBound:=@minkowski_gauge_lower R V S g hG (c*:x) (c*t)
    (mulr_gt0 hc ht) hS'.
  by rewrite ler_pdivrMr // mulrC.
have hUpper:g (c*:x)<=c*g x.
  by move:hDivide; rewrite ler_pdivrMr // mulrC.
have hLower:c*g x<=g (c*:x).
  apply:(@minkowski_gauge_greatest R V S g hG (c*:x) (c*g x)).
  move=>t ht hS.
  have hS':S ((t/c)^-1*:x).
    by rewrite invfM invrK -scalerA.
  have hBound:=@minkowski_gauge_lower R V S g hG x (t/c)
    (divr_gt0 ht hc) hS'.
  by move:hBound; rewrite ler_pdivlMr // mulrC.
by apply/eqP; rewrite eq_le hUpper hLower.
Qed.

(** Source for [minkowski_gauge_nonnegative_homogeneous]:
    the zero-scalar extension of the positive homogeneity
    in Federer 3.2.35, p. 271. Original
    zero membership proves g(0)=0; no arbitrary
    completion of the gauge is introduced. *)
Lemma minkowski_gauge_nonnegative_homogeneous (R:realType) (V:lmodType R)
    (S:set V) g:
  is_minkowski_gauge S g ->S 0 ->forall (c:R) (x:V),0<=c ->g (c*:x)=c*g x.
Proof.
move=>hG hS c x hc.
case:(eqVneq c 0)=>[->|hc0].
- by rewrite scale0r (minkowski_gauge_zero hG hS) mul0r.
- apply:(minkowski_gauge_positive_homogeneous hG).
  rewrite lt_neqAle; apply/andP; split; last exact hc.
  by rewrite eq_sym.
Qed.
