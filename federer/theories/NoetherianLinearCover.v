(** Federer (1969), 3.4.7, p. 325: finite
    generation transfers from a finite free cover to the
    submodule of polynomial remainders. This supporting image
    argument uses only actual linear maps and submodule laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingSubmoduleUP RingSubmoduleLinear NoetherianModuleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [noetherian_module_linear_cover]: a
    submodule covered by a Noetherian module has finite
    generators, supporting M intersect I in 3.4.7,
    p. 325. The map need not be injective or
    onto the whole ambient target. *)
Theorem noetherian_module_linear_cover (A:nzRingType) (U V:lmodType A)
    (f:{linear U->V}) (N:set V):
  is_noetherian_ring_module U ->is_ring_submodule N ->
  (forall x,N x ->exists u,f u = x) ->is_finitely_generated_ring_submodule N.
Proof.
move=>hU hN hCover.
have [F hF]:=hU (f @^-1` N) (ring_submodule_linear_preimage f hN).
exists (map f F);constructor;first exact:hN.
- move=>x /mapP [u hu ->];exact:(@generated_ring_submodule_contains A U _ _ hF u hu).
- move=>S hS hFS x hx.
  have hPre:=ring_submodule_linear_preimage f hS.
  have hContain:f @^-1` N `<=` f @^-1` S.
    apply:(generated_ring_submodule_minimal hF hPre)=>u hu.
    apply:hFS;apply/mapP;by exists u.
  have [u hu]:=hCover x hx.
  have huN:(f @^-1` N) u by change (N (f u));rewrite hu.
  have hh:=hContain u huN;change (S (f u)) in hh;by rewrite hu in hh.
Qed.
