(** Federer (1969), 1.3.3, p. 15, and 4.1.11,
    p. 366: identify the original inversion index of
    the first vertex exchange. The inversion set is the
    singleton pair of those consecutive positions. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import InversionCount CurrentSimplexFirstSwap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [permutation_first_swap_inversions]:
    the first-pair exchange has exactly one inversion,
    by the original index definition of 1.3.3, p. 15;
    this supports the sign formula in 4.1.11, p. 366. *)
Lemma permutation_first_swap_inversions m:
  [set ij:('I_(m.+2)*'I_(m.+2))%type |
    (ij.1<ij.2)%N &&
    (tperm ord0 (lift ord0 ord0) ij.2<tperm ord0 (lift ord0 ord0) ij.1)%N]=
  [set ((ord0:'I_(m.+2)),lift ord0 ord0)].
Proof.
apply/setP=>[[i j]];rewrite !inE /=.
case:(unliftP ord0 i)=>[p ->|->];case:(unliftP ord0 j)=>[q ->|->].
- case:(unliftP ord0 p)=>[r ->|->];case:(unliftP ord0 q)=>[s ->|->].
  + have hR:=@current_simplex_first_swap_rest 'I_(m.+2) m (fun k=>k) r.
    have hS:=@current_simplex_first_swap_rest 'I_(m.+2) m (fun k=>k) s.
    rewrite /current_simplex_first_swap in hR hS.
    rewrite hR hS !lift0 /=.
    by case:ltngtP=>[h|h|h];rewrite ?ltnNge ?leq_eqVlt ?h //.
  + have hR:=@current_simplex_first_swap_rest 'I_(m.+2) m (fun k=>k) r.
    rewrite /current_simplex_first_swap in hR.
    by rewrite hR tpermR !lift0 /=.
  + have hS:=@current_simplex_first_swap_rest 'I_(m.+2) m (fun k=>k) s.
    rewrite /current_simplex_first_swap in hS.
    by rewrite hS tpermR !lift0 /=.
  + by rewrite tpermR !lift0 /=.
- by rewrite tpermL !lift0 /=.
- case:(unliftP ord0 q)=>[s ->|->].
  + have hS:=@current_simplex_first_swap_rest 'I_(m.+2) m (fun k=>k) s.
    rewrite /current_simplex_first_swap in hS.
    by rewrite hS tpermL !lift0 /=.
  + by rewrite tpermL tpermR !lift0 /=.
- by rewrite tpermL /=.
Qed.

(** Source for [permutation_index_first_swap]:
    the original inversion index of the first exchange
    is minus one, supporting Federer 4.1.11, p. 366. *)
Theorem permutation_index_first_swap (K:fieldType) m:
  FedererPermutation.index K (tperm (ord0:'I_(m.+2)) (lift ord0 ord0))= -1.
Proof.
by rewrite FedererPermutation.index_inversions permutation_first_swap_inversions cards1 expr1.
Qed.
