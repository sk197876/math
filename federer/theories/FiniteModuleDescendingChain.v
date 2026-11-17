(** Supporting algebra for Federer (1969), 3.4.8(5), p. 328.
    Descending submodules of a finite field module stabilize.
    Reuse finite dual bases, the existing Noetherian ascending-chain
    theorem and the original double-annihilator separation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import Hom ModuleQuotient LinearBasis Annihilator AnnihilatorIntersection
  FiniteDualDimension RingSubmoduleUP NoetherianModuleUP NoetherianFiniteModule
  NoetherianModuleChain CommutativeIdealUP CommutativeFactorizationUP
  CommutativeDivisionRingNoetherian FiniteFieldModuleBasis FiniteBasisRingModule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_field_module_descending_stabilizes]: supporting
    finite residue-fibre argument for the auxiliary sentence in Federer
    3.4.8(5), p. 328. The module retains its actual submodules and
    original scalar field; no chain limit or stabilization is assumed. *)
Theorem finite_field_module_descending_stabilizes (K:fieldType) (V:lmodType K)
    (M:nat->set V):
  is_finitely_generated_ring_submodule (setT:set V) ->
  (forall j,is_ring_submodule (M j)) ->
  (forall i j,(i<=j)%N ->M j `<=` M i) ->
  exists N,forall j,(N<=j)%N ->M j = M N.
Proof.
move=>hFinite hM hMono.
have [n [e hE]]:=finitely_generated_field_module_basis hFinite.
have hDualFinite:=@finite_basis_ring_module K (Hom V K^o) n
  (dual_basis hE) (dual_basisP hE).
have hK:is_noetherian_commutative_ring K.
  apply:commutative_division_ring_noetherian=>a hA.
  have hNonzero:a!=0 by apply/eqP;exact:hA.
  exists a^-1;exact:mulVf hNonzero.
have hDualNoetherian:is_noetherian_ring_module (Hom V K^o).
  move=>N hN;apply:(@noetherian_submodule_of_finite_module K (Hom V K^o)
    setT N hK hDualFinite hN)=>a _;exact:I.
pose S j:subspace V:=@Subspace K V (M j) (ring_submodule_zero (hM j))
  (@ring_submodule_add K V (M j) (hM j)) (@ring_submodule_scale K V (M j) (hM j)).
pose D j:set (Hom V K^o):=annihilator (S j).
have hD j:is_ring_submodule (D j).
  constructor.
  - exact:subspace_zero.
  - exact:subspace_add.
  - exact:subspace_opp.
  - exact:subspace_scale.
have hIncreasing i j (hIJ:(i<=j)%N):D i `<=` D j.
  move=>a ha v hv;exact:ha v (hMono i j hIJ v hv).
have [N hStable]:=@noetherian_module_ascending_stabilizes K (Hom V K^o)
  D hDualNoetherian hD hIncreasing.
exists N=>j hNJ;apply/seteqP;split;first exact:hMono N j hNJ.
move=>v hV;apply:(annihilator_separates (S j) v).2=>a hA.
have hIn:D N a by rewrite -(hStable j hNJ).
exact:hIn v hV.
Qed.
