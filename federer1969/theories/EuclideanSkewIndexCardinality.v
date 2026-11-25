(** Federer (1969), 3.2.28(3), printed p. 265:
    the skew tangent directions have one index i<j
    for each unordered pair of source coordinates.
    Count them independently of any chosen tangent basis. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import EuclideanSymmetricUpperCoordinates EuclideanSymmetricIndexCardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [euclidean_skew_indices]: the pair indices
    1<=i<j<=m for the a_ij directions in Federer
    3.2.28(3), p. 265; the ordinal convention
    uses zero-based indices for precisely the same pairs. *)
Definition euclidean_skew_indices m:finType:=
  Finite.clone {p:('I_m*'I_m)%type |(p.1<p.2)%N} _.

(** Source for [euclidean_skew_index_cardinality]: the
    m(m-1)/2 skew directions in the tangent-basis
    calculation of Federer 3.2.28(3), p. 265.
    The empty and one-dimensional boundaries are included. *)
Theorem euclidean_skew_index_cardinality m:
  #|{:euclidean_skew_indices m}|=m*(m-1)%/2.
Proof.
pose P:=('I_m*'I_m)%type.
pose U:pred P:=fun p=>(p.1<=p.2)%N.
pose L:pred P:=fun p=>(p.2<=p.1)%N.
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
have hSym:#|U|=m*(m+1)%/2.
  rewrite -euclidean_symmetric_index_cardinality.
  by rewrite /euclidean_symmetric_indices card_sig.
have hCard:#|{:euclidean_skew_indices m}|=m * m-#|L|.
  rewrite /euclidean_skew_indices card_sig.
  have hEq:[pred p:P|(p.1<p.2)%N]=i [predC L].
    move=>[i j]; change ((i<j)%N= ~~(j<=i)%N).
    exact:ltnNge.
  rewrite (eq_card hEq).
  have hTotal:=cardC L.
  rewrite card_prod !card_ord in hTotal.
  by rewrite -hTotal addKn.
have hEven:2%|m*(m+1) by rewrite dvdn2 oddM addn1 oddS andbN.
have hPoly:(m * m)*2-m*(m+1)=m*(m-1).
  by rewrite -mulnA -mulnBr muln2 -addnn subnDA addnK.
have hDiv:((m * m)*2)%/2=m * m by rewrite mulnK.
rewrite hCard hSame hSym -{1}hDiv
  -(@divnBr ((m * m)*2) (m*(m+1)) 2 hEven) hPoly.
reflexivity.
Qed.
