(** Federer (1969), 4.1.1, p. 345: any exhausting
    increasing sequence of finite partition indices eventually
    contains all terms active on a given compact support.
    This supporting finite-set fact reuses 2.4.8, p. 84. *)
From mathcomp Require Import all_boot finmap boolp classical_sets.
From Federer Require Import CountableFiniteExhaustionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.

(** Source for [finite_exhaustion_captures_finite]: a finite
    subset is contained in all sufficiently late partial
    sets of an increasing exhaustion, supporting the
    distribution partition sum in Federer 4.1.1, p. 345. *)
Theorem finite_exhaustion_captures_finite (J:choiceType) (I:J->Prop)
    (C:nat->{fset J}) (hC:is_countable_finite_exhaustion I C)
    (F:{fset J}):
  (forall s,s \in F ->I s) ->exists N,forall m,(N<=m)%N ->(F `<=` C m)%fset.
Proof.
move=>hFI.
have hChoice (s:F):exists n,val s \in C n.
  exact:(@finite_exhaustion_cover J I C hC (val s) (@hFI (val s) (valP s))).
have [q hq]:=choice hChoice.
pose N:=\max_(s:F) q s.
exists N=>m hm; apply/fsubsetP=>s hs.
pose a:F:=[` hs]%fset.
have hnm:(q a<=m)%N:=leq_trans (leq_bigmax a) hm.
exact:((fsubsetP (@finite_exhaustion_increasing J I C hC (q a) m hnm)) (val a) (hq a)).
Qed.
