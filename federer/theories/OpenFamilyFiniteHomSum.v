(** Federer (1969), 4.1.7, pp. 355–356:
    finite coefficient expansions give continuous smooth
    operators. The target is the original smooth
    topological vector space, not the final test space. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom OpenFamilyTopologyUP OpenVectorTopologyUP OpenFamilyContinuousOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [open_family_finite_hom_sum_continuous]:
    finite sums of the original continuous coefficient
    maps are continuous, supporting the operations in
    Federer 4.1.7, pp. 355–356. Only the target's
    vector topology is used. *)
Theorem open_family_finite_hom_sum_continuous (R:realType) (E F:lmodType R)
    (O:set (set E)) (P:set (set F))
    (hO:is_open_family_topology O) (hP:is_open_vector_topology P)
    (I:finType) (L:I->Hom E F):
  (forall i,open_family_continuous O P (L i))->
  open_family_continuous O P (\sum_i L i).
Proof.
move=>hL; apply:(big_ind (fun A:Hom E F=>open_family_continuous O P A)).
- change (open_family_continuous O P (fun _ : E=>(0:F))).
  exact:open_family_constant_continuous hO.
- move=>A B hA hB.
  change (open_family_continuous O P (fun x=>A x+B x)).
  exact:(open_family_continuous_add hO hP hA hB).
- move=>i _; exact:hL.
Qed.
