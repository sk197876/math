(** Federer (1969), 3.4.6, pp. 323–324: the
    original coefficient recurrence cancels exactly the high
    distinguished-degree coefficients of the division remainder. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import WeierstrassCoefficientRecursion FiniteRectangularDeltaSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_recursion_convolution]: the
    original lower zero coefficients and leading coefficient
    one make the printed recurrence equivalent to the
    high-degree product coefficient equation, 3.4.6,
    pp. 323–324. Both finite bounds are retained,
    including transverse degree zero. *)
Theorem weierstrass_recursion_convolution (R:realType) (K:Type)
    (phi psi q:nat->nat->K->R) k:
  (forall r,(r<k)%N ->forall z,phi r 0%N z=0) ->
  (forall z,phi k 0%N z= 1) ->
  (forall i j,q i j=weierstrass_coefficient_step k phi psi i j q) ->
  forall i j z,psi (i+k)%N j z=
    \sum_(mu<(i+k).+1) \sum_(nu<j.+1) q mu nu z*phi (i+k-mu)%N (j-nu)%N z.
Proof.
move=>hLow hLeading hQ i j z.
have hi:(i<(i+k).+1)%N by rewrite ltnS leq_addr.
have hILower:(i<=(i+k).+1)%N:=ltnW hi.
have hTerm (mu:'I_(i+k).+1):q mu j z*phi (i+k-mu)%N 0%N z=
    (if (mu<i)%N then q mu j z*phi (i+k-mu)%N 0%N z else 0)+
    (if ((mu:nat)==i)%N then q i j z else 0).
  case hLess:(mu<i)%N.
  - have hNot:((mu:nat)!=i)%N by apply/eqP=>h;by rewrite h ltnn in hLess.
    by rewrite (negbTE hNot) addr0.
  - case hEqual:((mu:nat)==i)%N.
    + move/eqP:hEqual=>hEqual;rewrite hEqual.
      have hIndex:(i+k-i)%N=k by rewrite addnC addnK.
      by rewrite hIndex hLeading mulr1 add0r.
    + have hGreater:(i<mu)%N by rewrite ltn_neqAle eq_sym hEqual /= leqNgt hLess.
      have hMu:(mu<=i+k)%N by have:=ltn_ord mu;rewrite ltnS.
      have hIndex:(i+k-mu<k)%N by rewrite (@ltn_subLR (i+k)%N mu k hMu) ltn_add2r.
      by rewrite (hLow _ hIndex z) mulr0 add0r.
have hPadded:(\sum_(mu<i) q mu j z*phi (i+k-mu)%N 0%N z)=
    \sum_(mu<(i+k).+1) if (mu<i)%N then q mu j z*phi (i+k-mu)%N 0%N z else 0.
  by rewrite (big_ord_widen (i+k).+1 (fun mu=>q mu j z*phi (i+k-mu)%N 0%N z) hILower) big_mkcond.
have hSelected:(\sum_(mu<(i+k).+1) if ((mu:nat)==i)%N then q i j z else 0)=q i j z.
  by rewrite (@finite_ordinal_delta_sum R^o (i+k).+1 i (fun _=>q i j z)) hi.
have hEdge:(\sum_(mu<(i+k).+1) q mu j z*phi (i+k-mu)%N 0%N z)=
    (\sum_(mu<i) q mu j z*phi (i+k-mu)%N 0%N z)+q i j z.
  under eq_bigr do rewrite hTerm.
  by rewrite big_split -hPadded hSelected.
have hInner (mu:'I_(i+k).+1):
    (\sum_(nu<j.+1) q mu nu z*phi (i+k-mu)%N (j-nu)%N z)=
    (\sum_(nu<j) q mu nu z*phi (i+k-mu)%N (j-nu)%N z)+q mu j z*phi (i+k-mu)%N 0%N z.
  by rewrite big_ord_recr /= subnn.
under [RHS]eq_bigr do rewrite hInner.
rewrite big_split hEdge.
pose S:=\sum_(mu<i) q mu j z*phi (i+k-mu)%N 0%N z.
pose T:=\sum_(mu<(i+k).+1) \sum_(nu<j) q mu nu z*phi (i+k-mu)%N (j-nu)%N z.
change (psi (i+k)%N j z=T+(S+q i j z)).
have hRec:=congr1 (fun f:K->R=>f z) (hQ i j).
change (q i j z=psi (i+k)%N j z-S-T) in hRec.
rewrite hRec;ring.
Qed.
