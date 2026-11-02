(** Federer (1969), 3.2.28(1), printed p. 263: the
    number m(m+1)/2 of independent symmetric entries.
    Count the two triangular halves of the full array;
    their intersection is exactly the diagonal. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import EuclideanSymmetricUpperCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [euclidean_symmetric_index_cardinality]:
    dim Y_m=m(m+1)/2, Federer 3.2.28(1), p. 263:
    the combinatorial count of pairs i<=j, including m=0. *)
Theorem euclidean_symmetric_index_cardinality m:
  #|{:euclidean_symmetric_indices m}|=m*(m+1)%/2.
Proof.
pose P:=('I_m*'I_m)%type.
pose U:pred P:=fun p=>(p.1<=p.2)%N.
pose L:pred P:=fun p=>(p.2<=p.1)%N.
pose D:pred P:=fun p=>p.1==p.2.
pose swap (p:P):P:=(p.2,p.1).
have hSwap:injective swap.
  have hCan:cancel swap swap by move=>[i j].
  exact:can_inj hCan.
have hImage:image swap U =i L.
  move=>[i j]; apply/imageP/idP.
  - move=>[[r s] hrs he]; case:he=>-> ->; exact:hrs.
  - move=>hij; exists (j,i)=>//.
have hSame:#|L|=#|U|.
  rewrite -(card_image hSwap U); apply:eq_card=>p; symmetry; exact:hImage.
have hUnion:#|[predU U & L]|=m * m.
  rewrite (eq_card_prod (A:=[predU U & L])) ?card_ord //.
  move=>[i j]; change (is_true ((i<=j)||(j<=i))).
  exact:leq_total.
have hIntersection:#|[predI U & L]|=#|D|.
  apply:eq_card.
  move=>[i j].
  change (((i<=j)&&(j<=i))=(i==j)).
  apply/idP/idP.
  - move/andP=>[hij hji]; apply/eqP; apply:val_inj; apply/eqP.
    by rewrite eqn_leq hij hji.
  - move/eqP=>->; by rewrite leqnn.
pose diag (i:'I_m):P:=(i,i).
have hDiag:injective diag by move=>i j h; exact:(congr1 fst h).
have hDiagImage:codom diag =i D.
  move=>[i j]; apply/imageP/idP.
  - move=>[r _ he]; case:he=>-> ->; exact:eqxx.
  - move/eqP=>he; change (i=j) in he; exists i; first exact:isT.
    by rewrite /diag he.
have hD:#|D|=m.
  have hEqual:#|D|=#|codom diag|.
    apply:eq_card=>p; symmetry; exact:hDiagImage.
  have hImageCard:#|codom diag|=m by rewrite (card_codom hDiag) card_ord.
  exact:(eq_trans hEqual hImageCard).
have hCount:=cardUI U L.
rewrite hUnion hIntersection hD hSame in hCount.
have hCard:#|{:euclidean_symmetric_indices m}|=#|U|.
  by rewrite /euclidean_symmetric_indices card_sig.
have hTwice:#|U|*2=m*(m+1).
  by rewrite muln2 -addnn mulnDr muln1 -hCount.
by rewrite hCard -hTwice mulnK.
Qed.
