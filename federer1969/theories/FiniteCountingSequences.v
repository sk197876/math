(** Federer (1969), 3.2.6, p. 246: finite
    regular fibres are enumerated in increasing source
    order. These supporting counting identities use the
    existing sealed counting measure and finite lists. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets cardinality constructive_ereal lra.
From Federer Require Import CountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [counting_measure_finite_sequence]: supporting
    finite count in the proof of Federer 3.2.6, p. 246.
    A duplicate-free list enumerates exactly its many points;
    the empty list has count zero. *)
Lemma counting_measure_finite_sequence (R:realType) (X:choiceType) (s:seq X):
  uniq s -> @counting_measure R X [set x|x \in s]=((size s)%:R:R)%:E.
Proof.
move=>hs.
have he:[set x|x \in s]=[set` [fset x in s]].
  apply/seteqP; split=>x hx.
  - change (x \in [fset x in s]); by rewrite inE.
  - have hh:x \in [fset x in s]:=hx; by rewrite inE in hh.
by rewrite he counting_measure_finite card_fseq (undup_id hs).
Qed.

(** Source for [finite_counting_measure_set_finite]: supporting
    finite-fibre consequence of the almost-everywhere bound
    in Federer 3.2.6, p. 246. It is derived from
    the proved infinite-counting law of 2.1.2, p. 54. *)
Lemma finite_counting_measure_set_finite (R:realType) (X:choiceType) (A:set X):
  @counting_measure R X A< +oo -> finite_set A.
Proof.
move=>hFin; apply:contrapT=>hInf.
have hh:=@counting_measure_infinite R X A hInf.
by rewrite hh ltxx in hFin.
Qed.

Local Open Scope ring_scope.

(** Source for [real_sign_sum_counts]: supporting difference
    of positive and negative crossing counts in Federer
    3.2.6, p. 246. Each actual nonzero derivative
    contributes exactly one of the two signs. *)
Lemma real_sign_sum_counts (R:realType) (X:eqType) (s:seq X) (D:X->R):
  (forall x,x \in s -> D x!=0%R) ->
  \sum_(x<-s) Num.sg (D x)=
    ((count (fun x=>(0<D x)%R) s)%:R-(count (fun x=>(D x<0)%R) s)%:R)%R.
Proof.
elim:s=>[|x s ih] hD; first by rewrite big_nil /= subrr.
have hx:D x!=0%R:=hD x (mem_head x s).
have hTail t:t \in s -> D t!=0%R.
  move=>ht; apply:hD; by rewrite in_cons ht orbT.
have hSign:Num.sg (D x)=(((0<D x)%R)%:R-((D x<0)%R)%:R:R)%R.
  case:(ltP 0 (D x))=>hPos.
  - have hNeg:(D x<0)%R=false by rewrite ltNge (ltW hPos).
    by rewrite hNeg (gtr0_sg hPos) /= subr0.
  - have hNeg:(D x<0)%R by rewrite lt_neqAle hx hPos.
    by rewrite hNeg (ltr0_sg hNeg) /= sub0r.
rewrite big_cons hSign (ih hTail) /= !natrD.
lra.
Qed.
