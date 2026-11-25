(** Federer (1969), 3.4.2(8), p. 315: split the fixed
    subspace by the projection kernel before choosing adapted cubes. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier GrassmannSubspaces
  InnerProductUP OrthogonalComplement OrthogonalSubspaceSplit AnnihilatorIntersection
  LinearBasis FiniteSubspaceBasisExistence SubspaceSumDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [critical_orthogonal_remainder_exists]: supporting
    the dimension calculation for p(Z) in 3.4.2(8), p. 315.
    A contained finite-dimensional K splits Z as K plus its
    relative orthogonal complement. Actual bases give dimension
    dim(Z)-dim(K); no rank or dimension formula is assumed. *)
Theorem critical_orthogonal_remainder_exists (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n (b:'I_n->V) (hb:is_basis b)
    d k (Z:G V d) (K:G V k):
  (forall x,grassmann_val K x ->grassmann_val Z x) ->
  exists W:G V (d-k),
    (forall x,grassmann_val W x <->grassmann_val Z x /\
      orthogonal_complement hB (grassmann_val K) x) /\
    forall x,grassmann_val Z x <->exists u w,
      grassmann_val K u /\grassmann_val W w /\x=u+w.
Proof.
move=>hKZ.
pose Q:=subspace_intersection (grassmann_val Z) (orthogonal_complement hB (grassmann_val K)).
have [a ha]:=grassmann_proof K.
have [z hz]:=grassmann_proof Z.
have [r [e [he hBound]]]:=@finite_subspace_basis_exists R V n b hb Q.
have hSplit x:grassmann_val Z x <->exists u w,grassmann_val K u /\Q w /\x=u+w.
  split.
  - move=>hx.
    have [u [w [hu [hw hEq]]]]:=@finite_subspace_orthogonal_split R V B hB
      (grassmann_val K) k a ha x.
    exists u,w;split;first exact:hu.
    split;last exact:hEq.
    split;last exact:hw.
    have hW:w=x-u by rewrite hEq addrAC subrr add0r.
    rewrite hW;exact:(subspace_sub hx (hKZ u hu)).
  - move=>[u [w [hu [hw ->]]]];exact:(subspace_add (hKZ u hu) hw.1).
have hDisjoint x (hx:grassmann_val K x) (hq:Q x):x=0.
  exact:(@orthogonal_complement_intersection_zero R V B hB (grassmann_val K) x hx hq.2).
have hDimension:(k+r=d)%N:=(@sum_dimension_iff_disjoint R V (grassmann_val K) Q
  (grassmann_val Z) hSplit k r d a e z ha he hz).2 hDisjoint.
have hR:r=(d-k)%N by rewrite -hDimension addKn.
rewrite -hR;exists (@GrassmannSubspace R V r Q (ex_intro _ e he)).
split;first by move=>x.
exact:hSplit.
Qed.
