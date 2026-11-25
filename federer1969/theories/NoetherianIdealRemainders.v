(** Federer (1969), 3.4.7, p. 325: the
    equation I = O Phi + (M intersect I)
    makes the ideal finitely generated. This supporting
    algebraic proof takes division remainders as its premise;
    the actual analytic division theorem supplies them later. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP RingSubmoduleUP RingScalarRestriction
  RingIdealModules NoetherianFiniteModule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [noetherian_ideal_from_remainders]: the
    finite-generation step after division in 3.4.7,
    p. 325. A single original divisor and
    the finite transverse remainder module supply finite
    generators of the original ideal. No generators or
    finiteness conclusion for that ideal are assumed. *)
Theorem noetherian_ideal_from_remainders (A B:comNzRingType)
    (embed:{rmorphism A->B}) (Phi:B)
    (M:set (ring_restricted_space embed B^o)) (I:set B):
  is_noetherian_commutative_ring A ->
  @is_finitely_generated_ring_submodule A
    [the lmodType A of (ring_restricted_space embed B^o)] M ->
  is_commutative_ideal I ->I Phi ->
  (forall x,I x ->exists q r:B,M r /\x = q*Phi+r) ->
  is_finitely_generated_commutative_ideal I.
Proof.
move=>hA hFiniteM hI hPhi hDivision.
pose V:=[the lmodType A of (ring_restricted_space embed B^o)].
pose N:set V:=M `&` I.
have hM:is_ring_submodule M.
  have [F hF]:=hFiniteM;exact:generated_ring_submodule_laws hF.
have hIAsModule:=ideal_restricted_ring_submodule embed hI.
have hN:=ring_submodule_intersection hM hIAsModule.
have hNM:N `<=` M by move=>x hx;exact:hx.1.
have [F hF]:=noetherian_submodule_of_finite_module hA hFiniteM hN hNM.
exists (Phi::F);constructor;first exact:hI.
- move=>x;change (x \in Phi::F ->I x).
  rewrite in_cons;move/orP=>[/eqP ->|hx];first exact:hPhi.
  exact:(@generated_ring_submodule_contains A V _ _ hF x hx).2.
- move=>J hJ hGenerators x hx.
  have hJAsModule:=ideal_restricted_ring_submodule embed hJ.
  have hNJ:N `<=` J.
    apply:(generated_ring_submodule_minimal hF hJAsModule)=>r hr.
    apply:hGenerators;change (r \in Phi::F);by rewrite in_cons hr orbT.
  have [q [r [hMr hEquation]]]:=hDivision x hx.
  have hProduct:I (q*Phi):=(@commutative_ideal_mul B I hI q Phi hPhi).
  have hRemainder:r = x-q*Phi by rewrite hEquation addrAC subrr add0r.
  have hIr:I r by rewrite hRemainder;exact:(@commutative_ideal_difference B I hI x (q*Phi) hx hProduct).
  have hJr:J r:=hNJ r (conj hMr hIr).
  have hJPhi:J Phi:=hGenerators Phi (mem_head Phi F).
  rewrite hEquation;exact:(@commutative_ideal_add B J hJ (q*Phi) r
    (@commutative_ideal_mul B J hJ q Phi hJPhi) hJr).
Qed.
