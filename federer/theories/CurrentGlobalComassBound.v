(** Federer (1969), 4.1.7, p. 358: the
    original global comass constraint is equivalent
    to the pointwise constraint in the mass
    supremum. Only the public supremum laws
    are used, including on an empty domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP GrassmannAbbreviations AlternatingForms CurrentCoefficientNorms
  ExtendedSupremumUP CurrentGlobalComassUP CurrentGlobalComassSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_global_comass_bound]: the
    original M(phi)<=b exactly means the
    pointwise comass is at most b on U,
    supporting Federer 4.1.7, p. 358. *)
Theorem current_global_comass_bound (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n)) (phi:R_n R n->A_m (R_n R n) R^o m) (b:R):
  (@CurrentGlobalComass.value R h2 n m U phi<=b%:E)%E<->
    forall x,U x->@current_form_comass R h2 n m (phi x)<=b.
Proof.
have hSup:=@CurrentGlobalComass.laws R h2 n m U phi.
split.
- move=>hBound x hx.
  have hValue:((@current_form_comass R h2 n m (phi x))%:E<=
      @CurrentGlobalComass.value R h2 n m U phi)%E.
    apply:(extended_supremum_upper hSup);by exists x.
  have h:=le_trans hValue hBound;by move:h;rewrite lee_fin.
- move=>hPoint;apply:(extended_supremum_least hSup)=>a [x [hx <-]].
  by rewrite lee_fin;apply:hPoint.
Qed.
