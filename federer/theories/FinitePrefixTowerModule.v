(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 329: finite adjacent prefix extensions give a finite
    whole quotient. This field-independent assembly reuses the
    existing finite ring-image step and surjective module theorem. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeSubringUP CommutativeSubringRealisationUP CommutativeSubringRealisationSealed
  CommutativeQuotientUP CommutativeRingImageQuotient RingScalarRestriction RingSubmoduleUP
  FiniteRingImageStep FiniteModuleSurjectiveImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_prefix_tower_module]: the finite module
    induction on the original Q_j images, supporting both the real
    and complex versions of 3.4.8(8), p. 329. Every adjacent
    scalar triangle and the actual full-prefix surjection remain. *)
Theorem finite_prefix_tower_module n m (hMN:(m<=n)%N) (A:nat->comNzRingType) (C:comNzRingType)
    (F:forall p,(p<=n)%N ->{rmorphism A p->C}):
  (forall j:'I_n,(m<=j)%N ->forall (D:comNzRingType) (inclusion:{rmorphism D->C}),
    is_commutative_subring_realisation (fun y:C=>exists a:A (j:nat).+1,y=F (j:nat).+1 (ltn_ord j) a) inclusion ->
    exists scalar:{rmorphism A (j:nat)->D},
      (forall a:A (j:nat),inclusion (scalar a)=F (j:nat) (leq_trans (leqnSn (j:nat)) (ltn_ord j)) a) /\
      is_finitely_generated_ring_submodule (setT:set [the lmodType (A (j:nat)) of ring_restricted_space scalar D^o])) ->
  (forall c:C,exists a:A n,F n (leqnn n) a=c) ->
  is_finitely_generated_ring_submodule (setT:set [the lmodType (A m) of ring_restricted_space (F m hMN) C^o]).
Proof.
move=>hStep0 hFull.
pose Property:=fun p=>forall (hPN:(p<=n)%N) (D:comNzRingType) (inclusion:{rmorphism D->C}),
    is_commutative_subring_realisation (fun y:C=>exists a:A p,y = F p hPN a) inclusion ->
    exists scalar:{rmorphism A m->D},
      (forall a:A m,inclusion (scalar a) = F m hMN a) /\
      is_finitely_generated_ring_submodule
        (setT:set [the lmodType (A m) of ring_restricted_space scalar D^o]).
have hTower r:Property (m+r)%N.
  elim:r=>[|r IH].
  - rewrite addn0 /Property=>hPN D inclusion hImage.
    have [rho [hTriangle hRho]]:=@commutative_ring_image_quotient (A m) C D (F m hPN) inclusion hImage.
    exists rho;split.
    + move=>a;rewrite hTriangle;by rewrite (bool_irrelevance hPN hMN).
    + exists [::1];constructor.
      * by constructor.
      * by move=>x _.
      * move=>N hN hGenerators d _.
        have hOne:N 1.
          apply:hGenerators;change (1 \in [::(1:D)]);by rewrite inE.
        have [a hA]:=commutative_quotient_surjective hRho d.
        have hScaled:=@ring_submodule_scale (A m) _ N hN a 1 hOne.
        change (N (rho a*1)) in hScaled;by rewrite mulr1 hA in hScaled.
  - rewrite addnS /Property=>hPN D inclusion hImage.
    pose j:'I_n:=Ordinal hPN.
    pose hPrev:=leq_trans (leqnSn (m+r)) hPN.
    pose S0:set C:=fun y=>exists a:A (m+r),y = F (m+r) hPrev a.
    have hS0:is_commutative_subring S0:=commutative_ring_image_subring (F (m+r) hPrev).
    pose D0:=@CommutativeSubringRealisation.space C S0 hS0.
    pose include0:=@CommutativeSubringRealisation.inclusion C S0 hS0.
    have hImage0:=@CommutativeSubringRealisation.laws C S0 hS0.
    have [base [hBase hFinite0]]:=IH hPrev D0 include0 hImage0.
    have hImageStep:is_commutative_subring_realisation
      (fun y:C=>exists a:A (j:nat).+1,y = F (j:nat).+1 (ltn_ord j) a) inclusion.
      move:hImage;rewrite (bool_irrelevance hPN (ltn_ord j));by [].
    have [scalar [hScalar hFinite1]]:=hStep0 j (leq_addr r m) D inclusion hImageStep.
    have hScalar0 a:inclusion (scalar a) = F (m+r) hPrev a.
      rewrite (bool_irrelevance hPrev (leq_trans (leqnSn (j:nat)) (ltn_ord j))).
      exact:hScalar.
    have [next [hNext hFinite]]:=@finite_ring_image_step (A m) (A (m+r)) C D0 D
      (F (m+r) hPrev) include0 inclusion _ scalar base hImage0 hImage hScalar0 hFinite0 hFinite1.
    exists next;split;last exact:hFinite.
    move=>a;by rewrite hNext hBase.
have hEnd:(m+(n-m)=n)%N:=subnKC hMN.
have hAtEnd:=hTower (n-m)%N.
rewrite hEnd in hAtEnd.
pose S:set C:=fun y=>exists a:A n,y = F n (leqnn n) a.
have hS:is_commutative_subring S:=commutative_ring_image_subring (F n (leqnn n)).
pose D:=@CommutativeSubringRealisation.space C S hS.
pose inclusion:=@CommutativeSubringRealisation.inclusion C S hS.
have hImage:=@CommutativeSubringRealisation.laws C S hS.
have [scalar [hScalar hFinite]]:=hAtEnd (leqnn n) D inclusion hImage.
pose V:=[the lmodType (A m) of ring_restricted_space scalar D^o].
pose W:=[the lmodType (A m) of ring_restricted_space (F m hMN) C^o].
have hLinear:linear (inclusion:V->W).
  move=>a x y;change (inclusion (scalar a*x+y) = F m hMN a*inclusion x+inclusion y).
  by rewrite rmorphD rmorphM hScalar.
pose f:{linear V->W}:=HB.pack (inclusion:V->W) (GRing.isLinear.Build _ _ _ _ _ hLinear).
have hOnto:forall c:W,exists d:V,f d=c.
  move=>c;have [a ha]:=hFull c.
  have hMember:S c by exists a;exact:esym ha.
  exact:(commutative_subring_inclusion_image hImage c).1 hMember.
exact:(@finite_module_surjective_linear_image (A m) V W f hOnto hFinite).
Qed.
