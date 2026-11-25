(** Federer (1969), 4.1.7, p. 358: existence
    of the original global comass. Apply the
    extended-real supremum theorem of 2.1.1,
    p. 51, including the empty value set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP GrassmannAbbreviations AlternatingForms CurrentCoefficientNorms
  ExtendedSupremumUP ExtendedRealBoundsUP ExtendedRealBoundsSealed CurrentGlobalComassUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_global_comass_exists]: the
    original pointwise supremum exists as an
    extended real, supporting Federer 4.1.7,
    p. 358. No finite bound or
    nonempty-domain premise is imposed. *)
Theorem current_global_comass_exists (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n)) (phi:R_n R n->A_m (R_n R n) R^o m):
  exists c: \bar R,@is_current_global_comass R h2 n m U phi c.
Proof.
pose S:=@current_global_comass_values R h2 n m U phi.
pose ES:set (\bar R):=[set z|exists a:R,S a /\a%:E=z].
exists (@ExtendedRealBounds.value R ES).
have hSup:=@ExtendedRealBounds.laws R ES.
constructor.
- move=>a ha;apply:(extended_real_supremum_upper hSup);by exists a.
- move=>d hUpper;apply:(extended_real_supremum_least hSup)=>z [a [ha <-]].
  exact:hUpper a ha.
Qed.
