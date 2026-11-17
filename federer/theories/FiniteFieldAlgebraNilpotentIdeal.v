(** Supporting algebra for Federer (1969), 3.4.8(5), p. 328.
    A finite-dimensional algebra's ideal of one-minus units is
    nilpotent. Use the existing finite-module theorem, descending-chain
    connection and finite-ideal Nakayama argument. This is the residue
    fibre step, not a hypothesis about the original reduction sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingScalarRestriction RingSubmoduleUP CommutativeIdealUP
  CommutativeFactorizationUP CommutativeDivisionRingNoetherian NoetherianFiniteModule
  CommutativeIdealPowersSealed CommutativeIdealPowersLaws CommutativeIdealProductSealed
  FiniteIdealNakayama FiniteModuleDescendingChain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_field_algebra_nilpotent_ideal]: supporting
    finite residue-fibre connection for the auxiliary sentence in
    Federer 3.4.8(5), p. 328. In a finite algebra over the original
    field, an ideal whose one-minus elements are units has a zero
    power. Nilpotence and stabilization are proved, not assumed. *)
Theorem finite_field_algebra_nilpotent_ideal (K:fieldType) (C:comNzRingType)
    (scalar:{rmorphism K->C}) (I:set C):
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType K of ring_restricted_space scalar C^o]) ->
  is_commutative_ideal I ->
  (forall a:C,I a ->is_commutative_unit (1-a)) ->
  exists k,forall x:C,@CommutativeIdealPowers.value C I k x ->x = 0.
Proof.
move=>hFinite hI hUnit.
pose V:=[the lmodType K of ring_restricted_space scalar C^o].
pose P:=@CommutativeIdealPowers.value C I.
have hP j:is_commutative_ideal (P j):=commutative_ideal_power_is_ideal I j.
have hSubmodule (J:set C):is_commutative_ideal J ->@is_ring_submodule K V J.
  move=>hJ;constructor.
  - exact:commutative_ideal_zero hJ.
  - exact:commutative_ideal_add hJ.
  - exact:commutative_ideal_opp hJ.
  - move=>c x hx;change (J (scalar c*x));exact:(@commutative_ideal_mul C J hJ (scalar c) x hx).
have [N hStable]:=@finite_field_module_descending_stabilizes K V P hFinite
  (fun j=>hSubmodule (P j) (hP j)) (@commutative_ideal_power_antitone C I).
have hK:is_noetherian_commutative_ring K.
  apply:commutative_division_ring_noetherian=>a hA.
  have hNonzero:a!=0 by apply/eqP;exact:hA.
  exists a^-1;exact:mulVf hNonzero.
have hFinitePower:is_finitely_generated_ring_submodule (P N:set V).
  apply:(@noetherian_submodule_of_finite_module K V setT (P N) hK hFinite
    (hSubmodule (P N) (hP N)))=>x _;exact:Logic.I.
have [F hF]:=hFinitePower.
pose J:set C:=[set z|z = 0].
have hJ:is_commutative_ideal J.
  constructor.
  - reflexivity.
  - by move=>a b -> ->;rewrite add0r.
  - by move=>a ->;rewrite oppr0.
  - by move=>a b ->;rewrite mulr0.
have hGenerators:is_generated_commutative_ideal (J `|` [set z:C|z\in F]) (P N).
  constructor;first exact:hP N.
  - move=>z [->|hZ];first exact:commutative_ideal_zero (hP N).
    exact:(@generated_ring_submodule_contains K V [set z:V|z\in F] (P N) hF z hZ).
  - move=>L hL hContains.
    apply:(generated_ring_submodule_minimal hF (hSubmodule L hL))=>z hZ.
    apply:hContains;by right.
have hDecompose z:P N z ->exists j w,J j /\
    @CommutativeIdealProduct.value C I (P N) w /\z = j+w.
  move=>hZ;exists 0,z;split;first reflexivity.
  split;last by rewrite add0r.
  have hNext:P N.+1 z by rewrite (hStable N.+1 (leqnSn N)).
  move:hNext;by rewrite /P commutative_ideal_power_successorE.
exists N=>z hZ.
exact:(@finite_ideal_nakayama_modulo C I J (P N) hI hJ hUnit hDecompose F hGenerators z hZ).
Qed.
