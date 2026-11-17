(** Supporting linear algebra for Federer (1969),
    3.4.8(8), pp. 329–330: a finitely
    generated module over the original coefficient
    field has a finite basis. Apply the
    existing independent-span and basis theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingSubmoduleUP LinearBasis FiniteIndependence FiniteSpans FiniteBasisCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finitely_generated_field_module_basis]:
    finite-dimensional reduction of the coefficient
    module in 3.4.8(8), pp. 329–330,
    by the already proved finite-span argument
    of 1.6.1, p. 23. The basis
    remains a local existence witness. *)
Theorem finitely_generated_field_module_basis (K:fieldType) (V:lmodType K):
  is_finitely_generated_ring_submodule (setT:set V) ->
  exists n,exists basis:'I_n->V,is_basis basis.
Proof.
move=>[F hF].
have [n [basis [hIndependent hSpan]]]:=@finite_independent_span K V F.
have hModule:is_ring_submodule (in_finite_span basis).
  constructor.
  - exact:in_finite_span_zero.
  - exact:(@in_finite_span_add K V n basis).
  - move=>v hV;rewrite -scaleN1r;exact:(@in_finite_span_scale K V n basis (-1) v hV).
  - exact:(@in_finite_span_scale K V n basis).
have hAll:=generated_ring_submodule_minimal hF hModule hSpan.
exists n,basis;apply:(@finite_basis_criterion K [the finType of 'I_n] V basis hIndependent)=>v.
exact:hAll v I.
Qed.
