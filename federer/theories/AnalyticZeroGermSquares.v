(** Federer (1969), 3.4.5, p. 320: the
    common zero germ of two real analytic equations is
    the zero germ of their sum of squares. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRepresentatives AnalyticGermUP AnalyticGermSealed
  AnalyticGermRingLaws SetGermUP SetGermSealed AnalyticZeroGermUP AnalyticZeroGermSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_zero_germ_square_sum]: the
    two-equation instance of the original sum-of-squares
    identity, 3.4.5, p. 320, with the
    original germs and induced operations. *)
Theorem analytic_zero_germ_square_sum (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) (alpha beta:analytic_germ_space hNX a):
  @AnalyticZeroGerm.value R X NX hNX a
    (@AnalyticGerms.add R X NX hNX a
      (@AnalyticGerms.mul R X NX hNX a alpha alpha)
      (@AnalyticGerms.mul R X NX hNX a beta beta))=
  @SetGerms.meet (Topological.clone (real_norm_metric_space hNX) _) a
    (@AnalyticZeroGerm.value R X NX hNX a alpha) (@AnalyticZeroGerm.value R X NX hNX a beta).
Proof.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
have [g hg]:=@analytic_germ_has_representative R X NX hNX a beta.
pose p:=@analytic_add_representatives R X NX hNX a
  (@analytic_multiply_representatives R X NX hNX a f f)
  (@analytic_multiply_representatives R X NX hNX a g g).
have hRep:analytic_germ p=@AnalyticGerms.add R X NX hNX a
    (@AnalyticGerms.mul R X NX hNX a alpha alpha) (@AnalyticGerms.mul R X NX hNX a beta beta).
  by rewrite -hf -hg
    !(@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a))
    (@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
rewrite -(@AnalyticZeroGerm.laws R X NX hNX a _ p hRep)
  -(@AnalyticZeroGerm.laws R X NX hNX a alpha f hf)
  -(@AnalyticZeroGerm.laws R X NX hNX a beta g hg)
  (@set_germ_intersection_equation T a _ _ _ (@SetGerms.laws T a)).
congr (@set_germ T a _);apply/seteqP;split.
- move=>x hZero.
  change (analytic_representative_value f x*analytic_representative_value f x+
    analytic_representative_value g x*analytic_representative_value g x=0) in hZero.
  move:hZero=>/eqP;rewrite -!expr2 paddr_eq0 ?sqr_ge0 // !sqrf_eq0.
  by move/andP=>[/eqP hF /eqP hG];split.
- move=>x [hF hG].
  change (analytic_representative_value f x*analytic_representative_value f x+
    analytic_representative_value g x*analytic_representative_value g x=0).
  by rewrite hF hG !mul0r add0r.
Qed.
