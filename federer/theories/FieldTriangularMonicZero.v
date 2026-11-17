(** Federer (1969), 3.4.12, p. 339, extending the
    zero-dimensional case of 3.4.8(11), p. 333:
    triangular distinguished monic equations isolate the origin.
    Reuse the original prefix equations and dual-basis expansion;
    the finite coordinate induction works over every field. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom LinearBasis FiniteCoordinates FieldPrefixCoordinatesUP FieldPrefixSuffixSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [field_triangular_monic_zero]: the simultaneous
    original B_j preparations force every coordinate of a common
    zero to vanish, 3.4.8(11), p. 333, as extended by
    3.4.12, p. 339. Include the empty ambient space. *)
Theorem field_triangular_monic_zero (K:fieldType) (X:lmodType K) n
    (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X K^o)
    (hDual:forall i j,omega i (e j) = if i==j then 1 else 0)
    (hJN:forall j:'I_n,(j<=n)%N)
    (P:forall j:'I_n,Hom X (coordinate_space K j))
    (k:'I_n->nat) (b:forall j:'I_n,'I_(k j)->coordinate_space K j->K):
  (forall j,is_field_prefix_projection omega (hJN j) (P j)) ->
  (forall j,(0<k j)%N) ->(forall j i,b j i 0 = 0) ->
  forall x,(forall j,(omega j x)^+(k j)+
    \sum_(i<k j) b j i (P j x)*(omega j x)^+(i:nat) = 0) ->x = 0.
Proof.
move=>hP hPositive hCentre x hEquation.
have hZero r:(r<=n)%N ->forall i:'I_n,(i<r)%N ->omega i x = 0.
  elim:r=>[|r IH] hRN i hi;first by move:hi;rewrite ltn0.
  have hPrevious:forall j:'I_n,(j<r)%N ->omega j x = 0.
    exact:IH (leq_trans (leqnSn r) hRN).
  pose j:'I_n:=Ordinal hRN.
  have hPrefix:P j x = 0.
    apply/ffunP=>q;rewrite (hP j) ffunE.
    exact:hPrevious (widen_ord (hJN j) q) (ltn_ord q).
  have hPower:(omega j x)^+(k j) = 0.
    have h:=hEquation j;rewrite hPrefix in h.
    have hSum : \sum_(q<k j) b j q 0*(omega j x)^+(q:nat) = 0.
      apply:big1=>q _;by rewrite hCentre mul0r.
    by rewrite hSum addr0 in h.
  have hLast:omega j x = 0.
    have hBoolean:(omega j x)^+(k j)==0 by apply/eqP;exact:hPower.
    move:hBoolean;rewrite expf_eq0 hPositive /=;by move/eqP.
  case:(ltnP i r)=>hIR;first exact:hPrevious i hIR.
  have hEqual:i = j.
    apply:val_inj;apply/eqP;rewrite eqn_leq hIR andbT;exact:hi.
  by rewrite hEqual.
have hAll:forall i:'I_n,omega i x = 0 by move=>i;exact:hZero n (leqnn n) i (ltn_ord i).
rewrite {1}(@field_original_given_basis_expansion K X n e he omega hDual x).
apply:big1=>i _;by rewrite hAll scale0r.
Qed.
