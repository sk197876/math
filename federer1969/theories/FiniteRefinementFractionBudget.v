(** Federer (1969), 3.3.19, p. 305: sum the actual
    selected-child fractions over a finite original parent
    family. Duplicate image labels can only reduce the budget. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets.
From Federer Require Import FiniteFsetUnionCardBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.

(** Source for [finite_refinement_fraction_budget]: if each
    original parent's selected child fraction is at most c,
    the union of its selected child images has normalized
    count at most c times the original parent count. This
    supplies the finite addition in 3.3.19, p. 305;
    actual geometric disjointness is unnecessary for this bound. *)
Theorem finite_refinement_fraction_budget (R:realType) (I X:choiceType) n
    (F:{fset I}) (B:I->{fset 'I_n}) (g:I->'I_n->X) (c:R):
  (0<n)%N ->(forall z,z \in F ->#|` B z|%:R/n%:R<=c) ->
  #|` (\bigcup_(z<-F) [fset g z k | k in B z])%fset|%:R/n%:R<=#|` F|%:R* c.
Proof.
move=>hn hBudget.
pose U:=(\bigcup_(z<-F) [fset g z k | k in B z])%fset.
have hUnion:= @finite_fset_union_card_upper I X F (fun z=>[fset g z k | k in B z]).
have hSum:(\sum_(z<-F) #|` [fset g z k | k in B z]|<=\sum_(z<-F) #|` B z|)%N.
  apply:leq_sum=>z _;exact:leq_imfset_card.
have hNat:(#|` U|<=\sum_(z<-F) #|` B z|)%N:= leq_trans hUnion hSum.
have hReal:(#|` U|%:R<=\sum_(z<-F) #|` B z|%:R:>R).
  by rewrite -natr_sum ler_nat.
have hPositive:(0<n%:R:>R) by rewrite ltr0n.
have hInverse:(0<(n%:R:R)^-1) by rewrite invr_gt0.
have hScaled:= ler_wpM2r (ltW hInverse) hReal.
rewrite big_distrl in hScaled.
have hUpper:(\sum_(z<-F) #|` B z|%:R/n%:R)<=\sum_(z<-F) c.
  rewrite !big_seq;apply:ler_sum=>z hz;exact:hBudget z hz.
have hConstant:(\sum_(z<-F) c)=#|` F|%:R*c.
  by rewrite big_seq_fsetE sumr_const cardT -cardE -cardfE mulr_natl.
rewrite hConstant in hUpper.
exact:(le_trans hScaled hUpper).
Qed.
