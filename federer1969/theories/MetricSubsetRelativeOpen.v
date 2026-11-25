(** General topology supporting Federer (1969), 3.2.28(2),(4),
    pp. 264,267: openness between the actual relative spaces
    gives the ambient relatively open image pieces required
    by 3.1.19(3), p. 231. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import MetricSubsetBackground HomeomorphismUP EuclideanSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [metric_subset_relative_open_iff]: the relative
    openness used in Federer 3.2.28(2),(4), pp. 264,267.
    Supporting general topology: a subset of A is relatively
    open exactly when its inverse image in the actual subset
    type is open. *)
Lemma metric_subset_relative_open_iff (R:realType) (X:metricType R)
    (A W:set X):W `<=` A ->
  (open [set x:metric_subset A|W (val x)] <->relatively_open_set A W).
Proof.
move=>hWA; split.
- move=>[O hO hEq]; exists O; split; first exact hO.
  apply/seteqP; split=>x.
  + move=>hx; split; first exact:hWA x hx.
    pose z:metric_subset A:=exist _ x (mem_set (hWA x hx)).
    have hz:([set z:metric_subset A|W (val z)]) z by exact hx.
    by rewrite -hEq in hz.
  + move=>[hAx hOx].
    pose z:metric_subset A:=exist _ x (mem_set hAx).
    have hz:((fun z:metric_subset A=>(val z:X)) @^-1` O) z by exact hOx.
    by rewrite hEq in hz.
- move=>[O [hO hEq]].
  exists O; first exact hO.
  apply/seteqP; split=>x hx.
  + rewrite hEq; split; first exact:set_valP x.
    exact hx.
  + rewrite hEq in hx; exact:hx.2.
Qed.

(** Source for [metric_subset_open_relative_images]: the
    actual open-map arguments in Federer 3.2.28(2),(4),
    pp. 264,267, expressed in the ambient relative
    openness form of 3.1.19(3), p. 231. The
    restricted map is required to have the actual value f(x). *)
Theorem metric_subset_open_relative_images (R:realType) (X Y:metricType R)
    (A:set X) (C:set Y) (f:X->Y)
    (F:metric_subset A->metric_subset C):
  (forall x,(val (F x):Y)=f (val x)) ->is_open_map F ->
  forall W,relatively_open_set A W ->relatively_open_set C (f @` W).
Proof.
move=>hVal hOpen W hRel.
have hWA:W `<=` A by have [O [_ ->]]:=hRel; move=>x hx; exact:hx.1.
pose U:set (metric_subset A):=[set x|W (val x)].
have hU:open U:=(metric_subset_relative_open_iff hWA).2 hRel.
have hImage:F @` U=[set y:metric_subset C|(f @` W) (val y)].
  apply/seteqP; split=>y.
  - move=>[x hx <-]; exists (val x); first exact hx.
    exact:esym (hVal x).
  - move=>[x hx hxy].
    pose z:metric_subset A:=exist _ x (mem_set (hWA x hx)).
    exists z; first exact hx.
    apply:val_inj; rewrite hVal; exact hxy.
have hCW:(f @` W) `<=` C.
  move=>y [x hx <-].
  pose z:metric_subset A:=exist _ x (mem_set (hWA x hx)).
  have hz:=set_valP (F z); rewrite hVal in hz; exact hz.
apply:(metric_subset_relative_open_iff hCW).1.
rewrite -hImage; exact:hOpen U hU.
Qed.
