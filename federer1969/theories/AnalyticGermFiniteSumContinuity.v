(** Federer (1969), 3.4.8(5), p. 328:
    the original finite coefficient map into the germ
    ring is continuous. Finite addition uses the actual
    ring operations and the exact derivative-series topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP AnalyticGermUP AnalyticGermRing AnalyticGermMetric
  AnalyticGermAddContinuity AnalyticGermMultiplyContinuity ContinuousCommonPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section FiniteSums.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation M:=(@analytic_germ_metric R X NX hNX a).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Variable T:topologicalType.

(** Source for [analytic_germ_list_sum_continuous]: a finite
    list of continuous germ-valued functions has a
    continuous sum, supporting 3.4.8(5), p. 328. *)
Lemma analytic_germ_list_sum_continuous (F:seq (T->G)):
  (forall f,f\in F ->continuous (fun x=>f x:M)) ->
  continuous (fun x=>(\sum_(f<-F) f x:M)).
Proof.
elim:F=>[|f F ih] hEach.
- have hEqual:(fun x:T=>(\sum_(f<-[::]) f x:G))=(fun _=>0).
    by apply:funext=>x;rewrite big_nil.
  rewrite hEqual;exact:cst_continuous.
- have hf:continuous (fun x=>f x:M):=hEach f (mem_head f F).
  have hTail:continuous (fun x=>(\sum_(g<-F) g x:M)).
    apply:ih=>g hg;apply:hEach;by rewrite in_cons hg orbT.
  have hPair:=continuous_common_domain_pair hf hTail.
  have hAdd:=@analytic_germ_add_continuous R X NX hNX a.
  have hEqual:(fun x:T=>(\sum_(g<-f::F) g x:G))=
      (fun x=>f x+\sum_(g<-F) g x).
    by apply:funext=>x;rewrite big_cons.
  rewrite hEqual;move=>x U hU.
  exact:(hPair x _ (hAdd (f x,\sum_(g<-F) g x) U hU)).
Qed.

(** Source for [analytic_germ_finite_sum_continuous]: the
    finite coefficient sum is continuous for the actual
    germ metric, supporting the ideal image in
    3.4.8(5), p. 328. Empty index sets remain. *)
Theorem analytic_germ_finite_sum_continuous (I:finType) (F:I->T->G):
  (forall i,continuous (fun x=>F i x:M)) ->
  continuous (fun x=>(\sum_i F i x:M)).
Proof.
move=>hF.
pose L:=map F (enum I).
have hEach f:f\in L ->continuous (fun x=>f x:M).
  move=>/mapP[i _ ->];exact:hF.
have hList:=analytic_germ_list_sum_continuous hEach.
have hEqual:(fun x:T=>(\sum_(f<-L) f x:G))=(fun x=>\sum_i F i x).
  apply:funext=>x;by rewrite /L big_map /= -big_enum.
by rewrite -hEqual.
Qed.
End FiniteSums.
