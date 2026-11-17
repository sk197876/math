(** Federer (1969), 3.4.11, p. 338:
    choose finitely many original homogeneous polynomial
    generators, rather than arbitrary analytic linear combinations.
    Reuse the existing maximal-ideal-family theorem and
    the opaque generated ideal's least-ideal laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeIdealSealed NoetherianIdealMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [noetherian_finite_original_generators]: the
    finite original polynomial family in 3.4.11,
    p. 338. In a Noetherian ring,
    an arbitrary original generating family contains a
    finite subfamily generating its whole ideal. The
    original family may be empty. *)
Theorem noetherian_finite_original_generators (A:comNzRingType) (F:set A):
  is_noetherian_commutative_ring A ->exists L:seq A,
    (forall x,x \in L ->F x) /\
    @GeneratedCommutativeIdeal.value A F=
      @GeneratedCommutativeIdeal.value A [set x|x \in L].
Proof.
move=>hNoetherian.
pose J (L:seq A):set A:=@GeneratedCommutativeIdeal.value A [set x|x \in L].
pose D:set (set A):=[set M|exists L:seq A,(forall x,x \in L ->F x) /\M=J L].
have hNonempty:exists M,D M.
  exists (J [::]);exists [::];split;last reflexivity.
  by move=>x;rewrite in_nil.
have hIdeals M:D M ->is_commutative_ideal M.
  move=>[L [hLF ->]];exact:generated_commutative_ideal_laws (@GeneratedCommutativeIdeal.laws A _).
have [M [[L [hLF hM]] hMax]]:=@noetherian_ideal_family_maximum A D
  hNoetherian hNonempty hIdeals.
rewrite hM in hMax.
have hContains:F `<=` J L.
  move=>x hx.
  pose T:=J (L++[::x]).
  have hT:D T.
    exists (L++[::x]);split;last reflexivity.
    move=>y;rewrite mem_cat in_cons in_nil orbF=>/orP [hy|/eqP ->].
    - exact:hLF y hy.
    - exact:hx.
  have hLT:J L `<=` T.
    apply:(@generated_commutative_ideal_minimal A [set y|y \in L] (J L)
      (@GeneratedCommutativeIdeal.laws A _) T (hIdeals T hT)).
    move=>y hy;apply:(generated_commutative_ideal_contains (@GeneratedCommutativeIdeal.laws A _)).
    change (is_true (y \in L++[::x])).
    by rewrite mem_cat hy.
  apply:(hMax T hT hLT x).
  apply:(generated_commutative_ideal_contains (@GeneratedCommutativeIdeal.laws A _)).
  change (is_true (x \in L++[::x])).
  by rewrite mem_cat in_cons in_nil eqxx orbT.
exists L;split;first exact:hLF.
apply:funext=>x;apply:propext;split.
- exact:(@generated_commutative_ideal_minimal A F (@GeneratedCommutativeIdeal.value A F)
    (@GeneratedCommutativeIdeal.laws A F) (J L)
    (generated_commutative_ideal_laws (@GeneratedCommutativeIdeal.laws A [set y|y \in L]))
    hContains x).
- apply:(@generated_commutative_ideal_minimal A [set y|y \in L] (J L)
    (@GeneratedCommutativeIdeal.laws A _) (@GeneratedCommutativeIdeal.value A F)
    (generated_commutative_ideal_laws (@GeneratedCommutativeIdeal.laws A F)) _ x).
  move=>y hy;apply:(generated_commutative_ideal_contains (@GeneratedCommutativeIdeal.laws A F)).
  exact:hLF y hy.
Qed.
