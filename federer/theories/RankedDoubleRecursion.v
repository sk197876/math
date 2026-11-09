(** Federer (1969), 3.4.6, p. 324: the coefficient
    equations determine Q_(i,j) by induction on i+(k+1)j.
    This supporting recursion theorem uses finite stages and
    induction on natural numbers, without a recursion axiom. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Recursion.
Variable V:nat->zmodType.
Variable rank:nat->nat->nat.
Variable step:forall i j:nat,(forall p q:nat,V q)->V j.
Hypothesis hLocal:forall i j (f g:forall p q:nat,V q),
  (forall p q:nat,(rank p q<rank i j)%N ->f p q=g p q) ->step i j f=step i j g.

(** Source for [ranked_double_recursion_exists]: the original
    recursion's strictly smaller natural weights give a
    solution for every coefficient, supporting 3.4.6, p. 324.
    Finite stages are only local existence witnesses. *)
Theorem ranked_double_recursion_exists:
  exists f:(forall i j:nat,V j),forall i j:nat,f i j=step i j f.
Proof.
pose stage:=fix stage (n:nat):forall i j:nat,V j:=
  match n with 0%N=>fun i j=>0 |n.+1=>fun i j=>step i j (stage n) end.
have hStable:forall r i j n m,rank i j=r ->(r<n)%N ->(r<m)%N ->stage n i j=stage m i j.
  move=>r;elim/ltn_ind:r=>r ih i j n m hRank.
  case:n=>[|n];first by rewrite ltn0.
  case:m=>[|m];first by move=>_;rewrite ltn0.
  move=>hn hm;rewrite ltnS in hn hm.
  change (step i j (stage n)=step i j (stage m)).
  apply:hLocal=>p q hBefore.
  have hRankBefore:(rank p q<r)%N by rewrite -hRank.
  exact:(ih (rank p q) hRankBefore p q n m (erefl _)
    (leq_trans hRankBefore hn) (leq_trans hRankBefore hm)).
exists (fun i j=>stage (rank i j).+1 i j)=>i j.
change (step i j (stage (rank i j))=step i j (fun p q=>stage (rank p q).+1 p q)).
apply:hLocal=>p q hBefore.
exact:(hStable (rank p q) p q (rank i j) (rank p q).+1 (erefl _) hBefore (ltnSn _)).
Qed.

(** Source for [ranked_double_recursion_unique]: every
    actual solution of the original smaller-weight equations
    has the same coefficients, supporting the quotient
    uniqueness argument of 3.4.6, p. 324. *)
Theorem ranked_double_recursion_unique (f g:forall i j:nat,V j):
  (forall i j:nat,f i j=step i j f) ->(forall i j:nat,g i j=step i j g) ->
  forall i j:nat,f i j=g i j.
Proof.
move=>hf hg.
have hAll:forall r i j,rank i j=r ->f i j=g i j.
  move=>r;elim/ltn_ind:r=>r ih i j hRank.
  rewrite hf hg;apply:hLocal=>p q hBefore.
  have hRankBefore:(rank p q<r)%N by rewrite -hRank.
  exact:(ih (rank p q) hRankBefore p q (erefl _)).
move=>i j;exact:(hAll (rank i j) i j (erefl _)).
Qed.
End Recursion.
