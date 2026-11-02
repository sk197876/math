(** Federer (1969), 3.2.7, p. 246:
    every attained level of the sine on the whole
    real line has infinite multiplicity. This supporting
    lemma isolates the positive-period counting argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal ring.
From Federer Require Import RealMetricBackground MappingMultiplicity CountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [periodic_mapping_multiplicity_infinite]: supporting
    infinite count in the first example of Federer
    3.2.7, p. 246. Positive-period translates of
    one preimage form an injective infinite family in
    the actual fibre; no count is postulated. *)
Theorem periodic_mapping_multiplicity_infinite (R:realType) (Y:Type) (f:R->Y) (T:R):
  0<T -> (forall x,f (x+T)=f x) -> forall x:R,
  @mapping_multiplicity R [the choiceType of real_line_metric R] Y f setT (f x)= (+oo : \bar R)%E.
Proof.
move=>hT hPer x; pose u n:=x+n%:R*T.
have hVal n:f (u n)=f x.
  elim:n=>[|n ih]; first by rewrite /u mul0r addr0.
  have he:u n.+1=u n+T by rewrite /u -addn1 natrD natr1; ring.
  by rewrite he hPer ih.
have hInj:injective u.
  move=>n m he.
  have he':n%:R*T=m%:R*T by move:he; rewrite /u =>/addrI.
  have hT0:T!= 0 by rewrite gt_eqF.
  have heN:n%:R=m%:R:=mulIf hT0 he'.
  by move/eqP:heN; rewrite eqr_nat=>/eqP.
apply:counting_measure_infinite=>hFinite; apply:infinite_nat.
have hPre:=finite_preimage (fun n m _ _=>hInj n m) hFinite.
have he:u @^-1` mapping_fibre f setT (f x)=[set:nat].
  apply/seteqP; split=>n _; first exact I.
  split; first exact I; exact:hVal.
by rewrite he in hPre.
Qed.
