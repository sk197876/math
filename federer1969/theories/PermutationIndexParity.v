(** Federer (1969), 1.3.3–4, pp. 15–16, and
    4.1.11, p. 366: the original inversion index agrees
    with the sign obtained from vertex transpositions.
    Reuse its proved multiplicativity, with no replacement
    definition of Federer's index. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import InversionCount PermutationDeterminant PermutationIndexFirstSwap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section PermutationIndexParity.
Variable K:fieldType.
Hypothesis h2:(1+1:K)!=0.

(** Source for [permutation_index_conjugation]:
    relabelling a permutation preserves its original index,
    by 1.3.4, p. 16; this supports the vertex signs
    in Federer 4.1.11, p. 366. *)
Lemma permutation_index_conjugation n (s t:'S_n):
  FedererPermutation.index K (s ^ t)%g=FedererPermutation.index K s.
Proof.
rewrite /conjg !(@index_multiplicative K h2).
have hInverse:FedererPermutation.index K (t ^-1)%g*FedererPermutation.index K t = 1.
  by rewrite -(@index_multiplicative K h2) mulVg (@index_one K h2).
by rewrite mulrA mulrAC hInverse mul1r.
Qed.

(** Source for [permutation_index_first_star]:
    exchanging the first vertex with any different vertex
    has index minus one, supporting Federer 4.1.11,
    p. 366, by the original multiplicative index. *)
Lemma permutation_index_first_star m (j:'I_(m.+2)):
  j!=ord0->FedererPermutation.index K (tperm ord0 j)= -1.
Proof.
move=>hj.
case:(eqVneq j (lift ord0 ord0))=>[->|hjb].
- exact:(@permutation_index_first_swap K m).
- have hb0:(lift (ord0:'I_(m.+2)) ord0)!=ord0 by rewrite eq_sym neq_lift.
  have hConj:=permutation_index_conjugation
    (tperm (ord0:'I_(m.+2)) (lift ord0 ord0)) (tperm (lift ord0 ord0) j).
  rewrite tpermJ (tpermD hb0 hj) tpermL in hConj.
  exact:(eq_trans hConj (@permutation_index_first_swap K m)).
Qed.

(** Source for [permutation_index_transposition]:
    every genuine vertex exchange has the original index
    minus one, supporting Federer 4.1.11, p. 366.
    Empty and singleton families are retained. *)
Theorem permutation_index_transposition n (i j:'I_n):
  i!=j->FedererPermutation.index K (tperm i j)= -1.
Proof.
case:n i j=>[|[|m]] i j hij.
- by have:=ltn_ord i;rewrite ltn0.
- have hi:i=ord0:=ord1 i.
  have hj:j=ord0:=ord1 j.
  by rewrite hi hj eqxx in hij.
- case:(eqVneq i ord0)=>[hEqual|hi].
  + subst i;apply:permutation_index_first_star;by rewrite eq_sym.
  + case:(eqVneq j ord0)=>[hEqual|hj].
    * subst j;rewrite tpermC;exact:(permutation_index_first_star hi).
    * have h0j:(ord0:'I_(m.+2))!=j by rewrite eq_sym.
      have hConj:=permutation_index_conjugation (tperm (ord0:'I_(m.+2)) j) (tperm ord0 i).
      rewrite tpermJ tpermL (tpermD h0j hij) in hConj.
      exact:(eq_trans hConj (permutation_index_first_star hj)).
Qed.

(** Source for [permutation_index_parity]:
    the original index is minus one raised to permutation
    parity, by 1.3.3–4, pp. 15–16; this identifies
    exactly the coefficient printed in 4.1.11, p. 366. *)
Theorem permutation_index_parity n (s:'S_n):
  FedererPermutation.index K s=(-1:K)^+(odd_perm s).
Proof.
have[ts -> hDistinct]:=prod_tpermP s.
elim:ts hDistinct=>[|[i j] ts ih] /= hDistinct.
- by rewrite big_nil (@index_one K h2) odd_perm1 expr0.
- move/andP:hDistinct=>[hij hRest].
  rewrite big_cons (@index_multiplicative K h2)
    (permutation_index_transposition hij) (ih hRest) odd_mul_tperm hij /=.
  by case:(odd_perm _)=>/=;rewrite ?expr0 ?expr1 ?mulr1 ?mulN1r ?opprK.
Qed.
End PermutationIndexParity.
