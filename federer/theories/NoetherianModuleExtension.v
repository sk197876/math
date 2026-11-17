(** Federer (1969), 3.4.7, p. 325: the
    finite-module assertion follows by induction on the number
    of generators. This supporting exact-sequence step proves
    finite generation from the two smaller module properties. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingSubmoduleUP RingSubmoduleSealed RingSubmoduleLinear NoetherianModuleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [noetherian_module_extension]: supporting
    finite-module induction for 3.4.7, p. 325.
    If the kernel of a linear map is the image of
    a Noetherian module and its target is Noetherian,
    its source is Noetherian. No splitting, basis or
    choice of ideal generators is assumed. *)
Theorem noetherian_module_extension (A:nzRingType) (U V W:lmodType A)
    (i:{linear U->V}) (p:{linear V->W}):
  (forall x:V,p x = 0 ->exists u:U,i u = x) ->
  is_noetherian_ring_module U ->is_noetherian_ring_module W ->
  is_noetherian_ring_module V.
Proof.
move=>hExact hU hW N hN.
pose NU:set U:=i @^-1` N.
pose NW:set W:=p @` N.
have hNU:=ring_submodule_linear_preimage i hN.
have hNW:=ring_submodule_linear_image p hN.
have [F hF]:=hW NW hNW.
have hLift w:w \in F ->exists x:V,N x /\p x = w.
  move=>hw;have [x hx hp]:=(@generated_ring_submodule_contains A W _ _ hF w hw).
  by exists x.
pose lift w:=if pselect (w \in F) is left h then
    projT1 (cid (hLift w h)) else (0:V).
have hLiftLaw w (hw:w \in F):N (lift w) /\p (lift w) = w.
  rewrite /lift;case:pselect=>[h|h];last by exfalso;exact:h hw.
  exact:(projT2 (cid (hLift w h))).
pose H:=@GeneratedRingSubmodule.value A V [set x|x \in map lift F].
have hH:=@GeneratedRingSubmodule.laws A V [set x|x \in map lift F].
have hHN:H `<=` N.
  apply:(generated_ring_submodule_minimal hH hN).
  move=>x /mapP [w hw ->];exact:(hLiftLaw w hw).1.
have hImageH:=ring_submodule_linear_image p (generated_ring_submodule_laws hH).
have hNWImage:NW `<=` p @` H.
  apply:(generated_ring_submodule_minimal hF hImageH)=>w hw.
  exists (lift w).
  + apply:(generated_ring_submodule_contains hH);apply/mapP;by exists w.
  + exact:(hLiftLaw w hw).2.
have [G hG]:=hU NU hNU.
exists (map lift F++map i G);constructor;first exact:hN.
- move=>x;change (x \in map lift F++map i G ->N x);rewrite mem_cat;move/orP=>[/mapP [w hw ->]|/mapP [u hu ->]].
  + exact:(hLiftLaw w hw).1.
  + exact:(@generated_ring_submodule_contains A U _ _ hG u hu).
- move=>S hS hGenerators x hx.
  have hHS:H `<=` S.
    apply:(generated_ring_submodule_minimal hH hS)=>y hy.
    apply:hGenerators;change (y \in map lift F++map i G);by rewrite mem_cat hy.
  have hpX:NW (p x) by exists x.
  have [t ht hpt]:=hNWImage (p x) hpX.
  have hDifference:p (x-t) = 0 by rewrite linearB hpt subrr.
  have [u hu]:=hExact (x-t) hDifference.
  have huNU:NU u.
    change (N (i u));rewrite hu;exact:(@ring_submodule_difference A V N hN x t hx (hHN t ht)).
  have hPreS:=ring_submodule_linear_preimage i hS.
  have hNUPreS:NU `<=` i @^-1` S.
    apply:(generated_ring_submodule_minimal hG hPreS)=>z hz.
    apply:hGenerators;change (i z \in map lift F++map i G);rewrite mem_cat;apply/orP;right;apply/mapP;by exists z.
  have hSU:S (i u):=hNUPreS u huNU.
  have hSum:=@ring_submodule_add A V S hS (i u) t hSU (hHS t ht).
  by rewrite hu subrK in hSum.
Qed.
