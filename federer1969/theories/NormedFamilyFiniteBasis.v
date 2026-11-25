(** Supporting Federer (1969), 3.4.8(5), p. 328:
    finite families of finite-dimensional derivative spaces
    are finite dimensional. The proof uses only the
    abstract finite-product coordinates of 3.1.1(4),
    p. 210, and the basis-size argument of 1.6.1,
    p. 23. Every basis remains an existence witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom LinearBasis FiniteDualDimension FiniteCoordinates Annihilator
  FiniteIndependence FiniteBasisComparison FiniteDimension IndependentMap
  BoundedIndependentBasis NormedFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [normed_family_finite_basis_exists]: the
    finite-dimensional product assertion supporting finite
    derivative coordinates in 3.4.8(5), p. 328.
    Factor dimensions may differ or vanish; an empty
    family remains allowed. No product basis is assumed. *)
Theorem normed_family_finite_basis_exists (R:realType) m
  (V:'I_m->lmodType R) (N:forall i,V i->R) (P:lmodType R)
  (coordinate:forall i,Hom P (V i)) (PN:P->R)
  (hP:is_normed_family N coordinate PN):
  (forall i,exists q (e:'I_q->V i),is_basis e) ->
  exists q (e:'I_q->P),is_basis e.
Proof.
move=>hFinite.
pose q i:=projT1 (cid (hFinite i)).
pose b i:=projT1 (cid (projT2 (cid (hFinite i)))).
have hb i:is_basis (b i):=projT2 (cid (projT2 (cid (hFinite i)))).
pose B:finType := Finite.clone {i:'I_m & 'I_(q i)} _.
pose f (x:P):coordinate_space R #|B| :=
  [ffun j:'I_#|B|=>dual_basis (hb (tag (enum_val j))) (tagged (enum_val j))
    (coordinate (tag (enum_val j)) x)].
have hLinear:linear f.
  move=>c x y;apply/ffunP=>j.
  by rewrite /f !ffunE linearP linearP.
pose L:=@HomMap R P (coordinate_space R #|B|) f (introT (asboolP _) hLinear).
have hInjective:injective L.
  move=>x y hEqual;apply:(normed_family_extensional hP)=>i.
  rewrite (basis_vector_expansion (hb i) (coordinate i x))
    (basis_vector_expansion (hb i) (coordinate i y)).
  apply:eq_bigr=>j _;congr (_*:_).
  pose t:B:=@Tagged 'I_m i (fun i=>'I_(q i)) j.
  have hValue:=congr1 (fun z:coordinate_space R #|B|=>z (enum_rank t)) hEqual.
  by move:hValue;rewrite /L /= /f !ffunE enum_rankK /t /=.
have hBound k (e:'I_k->P) (hIndependent:finite_independent e):(k<=#|B|)%N.
  have hDimension:=@finite_independent_dimension R (finite_basis_vect (@coordinate_basisP R #|B|))
    k (fun i=>L (e i))
    (@finite_independent_map R (Finite.clone 'I_k _) P (coordinate_space R #|B|)
      (hom_as_linear L) e hInjective hIndependent).
  by rewrite finite_basis_dimension card_ord in hDimension.
have [s [e [he _]]]:=@bounded_independent_basis R P #|B| hBound.
exists s,e;exact:he.
Qed.
